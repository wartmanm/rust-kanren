#[macro_use]
///! Contains `ToVar` definitions for many of Rust's built-in types.
pub mod vars;
///! Contains the implementation of the `Disequal` constraint.
pub mod disequal;
///! Contains `Reifier`, which reifies variables, providing a consistent, unique identifier for unset
///! variables.
pub mod reify;
mod get_values;

pub use core::get_values::{assign_values, assign_all_values};

use std::rc::Rc;
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::any::*;
use std::raw::TraitObject;
use std::collections::HashSet;

use core::ExactVal::*;
use core::VarRef::*;


///! Wrapper for a usize, used as a unique variable identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UntypedVar(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypedVar(UntypedVar, TypeId);

impl TypedVar {
    #[inline(always)] pub fn type_id(&self) -> TypeId { self.1 }
    #[inline(always)] pub fn untyped(&self) -> UntypedVar { self.0 }
}

///! Typed wrapper for a usize, used as a unique variable identifier.  Currently they aren't tied
///! to a particular state, so the typing, while helpful, isn't sufficient to guarantee safety
///! without additional runtime checks.
pub struct Var<A: VarWrapper> { var: UntypedVar, var_type: PhantomData<A> }
impl<A> Clone for Var<A> where A: VarWrapper { fn clone(&self) -> Var<A> { *self } }
impl<A> Copy for Var<A> where A: VarWrapper { }

///! State is the heart of rust_kanren.  It tracks all variable substitutions added by calling
///! `unify()`, hands out Vars through `make_var()` and `make_var_of()`, and tracks whether any
///! unifications have failed.
pub struct State {
    eqs: VarMap,
    // TODO: use a reference instead
    parent: Option<Rc<State>>,
    constraints: ConstraintStore,
    proxy_eqs: VarMap,
}

///! StateProxy is used to identify and include or roll back the substitutions added during
///! unification, which is necessary for constraints.
#[derive(Debug)]
pub struct StateProxy<'a> {
    parent: &'a mut State,
}

///! Enum representing the possible outcomes of `Constraint::update()`.
#[derive(Debug)]
pub enum ConstraintResult<A> {
    Failed,
    Irrelevant,
    Unchanged,
    Updated(A),
}

///! Trait for anything that can be used as a variable or turned into one.
pub trait ToVar : Debug + Any {
    type VarType : VarWrapper;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<Self::VarType>;
}

///! Constraints placed on one or more variables can alter whether a unification succeeds or
///  fails, or make other changes, if those variables are affected.
pub trait Constraint: Debug + Sized {
    ///! Apply the constraint and return a ContraintResult.
    fn update(&self, _: &mut StateProxy) -> ConstraintResult<Self> { ConstraintResult::Unchanged }
    ///! Called to see if a constraint is affected by a newly performed unification.  This should
    ///! call varmap.contains_key() for each variable in the constraint.
    fn relevant(&self, _: &VarMap) -> bool;
    ///! Called to update a constraint's variables when unification has assigned them to be equal
    ///! to other variables.  Should call `state.update_var()` for each variable in the constraint.
    fn update_vars(&mut self, _: &State);
    ///! (Optional) Called to determine whether `update_vars()` needs to be called.  Should call
    ///! `varmap.need_update()` for each variable in the constraint.
    fn need_update(&self, vars: &VarMap) -> bool { self.relevant(vars) }
}

///! Trait for creating a `Constraint`, given a `State`.
pub trait ToConstraint {
    type ConstraintType: Constraint + 'static + Clone;
    fn into_constraint(self, state: &mut State) -> Self::ConstraintType;
}

trait BoxedConstraint: Debug {
    fn update(&self, _: &mut StateProxy) -> ConstraintResult<Box<BoxedConstraint>>;
    fn relevant(&self, _: &VarMap) -> bool;
    fn update_vars(&mut self, _: &State);
    fn need_update(&self, vars: &VarMap) -> bool;
    fn clone_boxed(&self) -> Box<BoxedConstraint>;
}

struct ConstraintWrapper<A: Constraint + Clone>(A);

type RcConstraint = Rc<Box<BoxedConstraint>>;

impl<A> BoxedConstraint for ConstraintWrapper<A> where A : Constraint + Clone + 'static {
    fn update(&self, proxy: &mut StateProxy) -> ConstraintResult<Box<BoxedConstraint>> {
        use ::core::ConstraintResult::*;
        match self.0.update(proxy) {
            Updated(x) => Updated(Box::new(ConstraintWrapper(x))),
            Failed => Failed,
            Irrelevant => Irrelevant,
            Unchanged => Unchanged,
        }
    }
    fn relevant(&self, vars: &VarMap) -> bool { self.0.relevant(vars) }
    fn update_vars(&mut self, vars: &State) { self.0.update_vars(vars) }
    fn need_update(&self, vars: &VarMap) -> bool { self.0.need_update(vars) }
    fn clone_boxed(&self) -> Box<BoxedConstraint> {
        Box::new(ConstraintWrapper(self.0.clone()))
    }
}

impl<A> Debug for ConstraintWrapper<A> where A : Constraint + Clone + 'static {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        self.0.fmt(fmt)
    }
}

///! Store a value in a state.
pub trait VarStore {
    ///! Add a variable with a new value to the map.  Called by `make_var_of()`.
    fn store_value<A>(&mut self, value: A) -> Var<A> where A : VarWrapper + 'static;
    ///! Create a new variable with no value.
    fn make_var<A>(&mut self) -> Var<A> where A : VarWrapper;
    ///! Create a new variable with the provided value.
    fn make_var_of<A>(&mut self, value: A) -> Var<<A as ToVar>::VarType>
    where A : ToVar, Self: Sized + Unifier {
        value.into_var(self)
    }
}

///! Retrieve a value from a state.
pub trait VarRetrieve {
    ///! Retrive a reference to the stored value of a variable, if any.
    fn get_value<A>(&self, a: Var<A>) -> Option<&A> where A : VarWrapper;
    fn get_untyped(&self, var: UntypedVar) -> Option<&VarWrapper>;
}

///! Unify variables together, and get or change the current success state.
pub trait Unifier {
    fn unify_vars<A>(&mut self, a: Var<A>, b: Var<A>) -> &mut Self where A : VarWrapper;
    ///! Mark the state as invalid.
    fn fail(&mut self) -> &mut Self;
    ///! Retrive whether the state is valid.
    fn ok(&self) -> bool;
    ///! Helper method to call fail() if a statement evaluates to false.
    fn assert(&mut self, ok: bool) -> &mut Self {
        if !ok {
            self.fail();
        }
        self
    }
    ///! Helper method for unification.  Converts values to variables and calls unify_vars().
    fn unify<A, B, C>(&mut self, a: B, b: C) -> &mut Self
    where A : VarWrapper, B : ToVar<VarType=A>, C : ToVar<VarType=A>, Self: VarStore + Sized {
        let avar: Var<A> = self.make_var_of(a);
        let bvar: Var<A> = self.make_var_of(b);
        self.unify_vars(avar, bvar);
        self
    }
}

///! Represents possible results of `VarWrapper::unify_with()`.
pub struct UnifyResult(UnifyResultInner);

enum UnifyResultInner {
    Success,
    Failure,
    Overwrite(Box<VarWrapper>),
}

impl From<bool> for UnifyResult {
    fn from(val: bool) -> UnifyResult {
        UnifyResult(if val { UnifyResultInner::Success } else { UnifyResultInner::Failure })
    }
}

impl UnifyResult {
    pub unsafe fn overwrite<A>(a: A) -> UnifyResult where A: VarWrapper {
        UnifyResult(UnifyResultInner::Overwrite(Box::new(a)))
    }
}

///! Trait implemented by all variable types.
pub trait VarWrapper : Debug + 'static + Any {
    ///! Compare two variables for equality.  For containers this entails unifying the contained
    ///! variables; for everything else it's no different from PartialEq.
    fn unify_with(&self, other: &VarWrapper, state: &mut StateProxy) -> UnifyResult;
    ///! (Optional) Return the number of possible values returned by `value_iter`.  This is used by
    ///! `assign_all_values` to determine the variables needing assignment.
    fn value_count(&self) -> usize { 1 }
    ///! (Optional) Return an iterator over the values this variable can take.  This shouldn't be called if
    ///! `value_count()` returns 1.
    fn value_iter(&self) -> Box<Iterator<Item=Box<VarWrapper>>> { panic!() }
    ///! (Optional) Must be overridden to return `true` if `unify_with()` ever returns `Overwrite` -- this
    ///! disables an optimization that's incorrect in such a case.
    fn uses_overwrite(&self) -> bool { false }
    fn var_iter<'a>(&'a self) -> Option<Box<Iterator<Item=UntypedVar> + 'a>> { None }
    fn occurs_check(&self, _: &StateProxy, _: TypedVar) -> bool { false }
    fn can_contain_type(_: &TypeList, _: TypeId) -> bool where Self: Sized { false }
}

// needed for VarWrapper::can_contain_type(), to prevent infinite loops
pub enum TypeList<'a> {
    Nil,
    Pair(TypeId, &'a TypeList<'a>),
}

impl<'a> TypeList<'a> {
    pub fn contains_type(&self, t: TypeId) -> bool {
        let mut me = self;
        while let TypeList::Pair(my_t, ref tail) = *me {
            if my_t == t { return true; }
            me = tail;
        }
        false
    }
}

// TODO this can be determined at compile time, can it be made easier for llvm to discover that?
fn needs_occurs_check<T>() -> bool where T : VarWrapper {
    T::can_contain_type(&TypeList::Nil, TypeId::of::<T>())
}

trait FollowRef {
    ///! Follow a single level of indirection to look up the value of a variable.  This returns the
    ///! first result found, in the current or any parent state, but doesn't follow EqualTos.
    fn get_ref(&self, id: UntypedVar) -> &VarRef;

    ///! Follow unlimited levels of indirection to find the value of a variable, the UntypedVar
    ///! that directly refers to it, and its type.
    fn follow_ref(&self, mut id: UntypedVar) -> (UntypedVar, Option<&VarWrapper>, TypeId) {
        loop {
            match self.get_ref(id) {
                &EqualTo(x) => { id = x; },
                &Exactly(ref x, ty) => {
                    return (id, unsafe { self.var_opt(x) }, ty);
                },
            }
        }
    }

    ///! Follow unlimited levels of indirection to find the UntypedVar which a variable is equal to
    ///! and which directly holds a value.
    fn follow_id(&self, id: UntypedVar) -> UntypedVar {
        self.follow_ref(id).0
    }

    fn follow_typed(&self, id: UntypedVar) -> TypedVar {
        let (id, _, t) = self.follow_ref(id);
        TypedVar(id, t)
    }

    ///! Follow unlimited levels of indirection to find the value which a variable is equal to.
    fn get_exact_val(&self, id: UntypedVar) -> Option<&VarWrapper> {
        self.follow_ref(id).1
    }

    fn get_exact_val_opt<A>(&self, id: UntypedVar) -> Option<&A> where A: VarWrapper {
        self.get_exact_val(id).map(|x| x.get_wrapped_value())
    }

    #[inline(always)]
    unsafe fn var_opt<'var>(&'var self, var: &'var ExactVal) -> Option<&'var VarWrapper> {
        var.opt_ptr().map(|x| &*x)
    }
}

///! Holds the final value of a walked variable.  Fresh is used for unset variables; it doesn't have
///! to exist, but makes it easier to identify type errors.
enum ExactVal {
    Value(Box<VarWrapper>), 
    ValuePtr(*const VarWrapper),
    Fresh,
}

///! A variable can either be set to a specific value (which can be no value) or equal to another
///! variable.
enum VarRef {
    Exactly(ExactVal, TypeId),
    EqualTo(UntypedVar),
}


///! Stores Var -> value mappings.  An implementation detail required by
///  `Constraint::relevant`.
pub struct VarMap {
    id: UntypedVar,
    eqs: Vec<(UntypedVar, VarRef)>,
    ok: bool,
}

impl Clone for VarMap {
    fn clone(&self) -> VarMap {
        let new_eqs = self.iter().map(|&(k, ref v)| {
            let v = match *v {
                EqualTo(x) => EqualTo(x),
                Exactly(Fresh, t) => Exactly(Fresh, t),
                Exactly(Value(ref other), t) => {
                    Exactly(ValuePtr(&**other as *const VarWrapper), t)
                },
                Exactly(ValuePtr(other), t) => Exactly(ValuePtr(other), t),
            };
            (k, v)
        }).collect();
        VarMap { id: self.id, eqs: new_eqs, ok: self.ok }
    }
}

#[derive(Clone)]
struct ConstraintStore {
    constraints: Vec<RcConstraint>,
}

impl VarWrapper {
    //! Reimplementation of Any::downcast_ref(), because the original doesn't seem to be
    //! available.  I'm not entirely sure why.
    pub fn get_wrapped_value<T>(&self) -> &T
    where T : VarWrapper {
        assert!(TypeId::of::<T>() == self.get_type_id());
        let x: TraitObject = unsafe { ::std::mem::transmute(self) };
        unsafe { ::std::mem::transmute(x.data) }
    }
}

impl<A> Var<A>
where A : VarWrapper {
    fn new(var: UntypedVar) -> Var<A> {
        Var { var: var, var_type: PhantomData }
    }
    pub fn untyped(&self) -> UntypedVar {
        self.var
    }
    pub fn untyped_ref(&self) -> &UntypedVar {
        &self.var
    }
    pub fn untyped_mut(&mut self) -> &mut UntypedVar {
        &mut self.var
    }
    pub fn typed(&self) -> TypedVar {
        TypedVar(self.var, TypeId::of::<A>())
    }
}

impl<A> ToVar for Var<A> where A : VarWrapper {
    type VarType = A;
    fn into_var<U: VarStore>(self, _: &mut U) -> Var<A> {
        self
    }
}

impl ExactVal {
    fn new<A: VarWrapper + 'static>(value: A) -> ExactVal {
        Value(Box::new(value))
    }
    fn opt_ptr(&self) -> Option<*const VarWrapper> {
        match self {
            &Fresh => None,
            &Value(ref x) => Some(&**x as *const VarWrapper),
            &ValuePtr(x) => Some(x),
        }
    }
}

impl VarRetrieve for State {
    fn get_value<A: VarWrapper>(&self, var: Var<A>) -> Option<&A> {
        self.get_exact_val_opt(var.var)
    }
    fn get_untyped(&self, var: UntypedVar) -> Option<&VarWrapper> {
        self.get_exact_val(var)
    }
}

impl VarStore for State {
    fn store_value<A>(&mut self, value: A) -> Var<A>
    where A : VarWrapper + 'static { self.eqs.store_value(value) }
    fn make_var<A>(&mut self) -> Var<A> where A : VarWrapper { self.eqs.make_var() }
}

impl FollowRef for State {
    fn get_ref(&self, id: UntypedVar) -> &VarRef {
        let mut state = self;
        loop {
            match state.eqs.get(&id) {
                Some(x) => { return x; }
                None => {
                    state = match state.parent {
                        Some(ref x) => &*x,
                        None => { panic!("could not find reference for {:?} in {:?}", id, self); }
                    };
                }
            }
        }
    }
}

impl Unifier for State {
    fn unify_vars<A>(&mut self, a: Var<A>, b: Var<A>) -> &mut State
    where A : VarWrapper {
        self.untyped_unify(a.var, b.var, TypeId::of::<A>(), needs_occurs_check::<A>());
        self
    }

    fn fail(&mut self) -> &mut State {
        self.eqs.ok = false;
        self
    }

    fn ok(&self) -> bool {
        self.eqs.ok
    }
}

impl State {

    ///! Create a State with no substitutions and no parent.
    pub fn new() -> State {
        State {
            eqs: VarMap::new(),
            parent: None,
            constraints: ConstraintStore::new(),
            proxy_eqs: VarMap::new(),
        }
    }

    ///! Create a State which builds on a parent State.  This is essential for backtracking: no
    ///! steps are needed to return to an earlier point beyond dropping the child State.
    pub fn with_parent(parent: Rc<State>) -> State {
        let constraints = parent.constraints.clone();
        State {
            eqs: VarMap::with_parent(&parent.eqs),
            parent: Some(parent.clone()),
            constraints: constraints,
            proxy_eqs: VarMap::new(),
        }
    }

    ///! Find how many parents a state has, just in case that's useful to you for some reason.
    #[allow(dead_code)]
    pub fn depth(&self) -> usize {
        let mut state = self;
        let mut depth = 0;
        loop {
            state = match state.parent {
                Some(ref x) => {
                    depth += 1;
                    &**x
                },
                None => { return depth; }
            }
        }
    }

    ///! Unify two variables.  Inserts an EqualTo if one or both are unset, or calls _equals_ if
    ///! both are set.  If the value is a container, this will recurse and call unify() on the
    ///! contained types; otherwise it simply compares them.
    fn untyped_unify(&mut self, a: UntypedVar, b: UntypedVar, typeid: TypeId, use_occurs_check: bool) -> bool {
        {
            let mut proxy = StateProxy::new(self);
            proxy.untyped_unify(a, b, typeid, use_occurs_check);
        }
        let relevant = self.constraints.get_relevant_constraints(&self.proxy_eqs, Vec::new());
        self.merge_proxy();
        if !self.ok() {
            return false;
        }
        if !relevant.is_empty() {
            //println!("testing constraints...");
            self.test_constraints(relevant)
        //println!("testing constraints {:?} w/ {:?}", relevant, self);
        } else {
            true
        }
    }

    fn update_constraint(&self, constraint: RcConstraint) -> RcConstraint {
        if !constraint.need_update(&self.eqs) {
            constraint
        } else {
            let mut newconstraint = constraint.clone_boxed();
            newconstraint.update_vars(self);
            Rc::new(newconstraint)
        }
    }

    fn test_constraints(&mut self, mut relevant: Vec<RcConstraint>) -> bool {
        use core::ConstraintResult::*;
        while let Some(constraint) = relevant.pop() {
            let constraint = self.update_constraint(constraint);
            // run condition.test()
            // restore state and get updated condition
            //println!("ok: {}, test result: {:?}", self.ok(), result);
            // run condition.update()
            //println!("constraint passed test, calling update()");
            let result = {
                let mut proxy = StateProxy::new(self);
                constraint.update(&mut proxy)
            };
            // get updated condition
            let retconstraint = match result {
                Failed => { self.restore_proxy(); self.fail(); return false; }
                Irrelevant => None,
                Unchanged => Some(constraint),
                Updated(x) => Some(Rc::new(x)),
            };
            // see if any constraints became relevant due to update(), then merge and return the
            // constraint to the list
            relevant = self.constraints.get_relevant_constraints(&self.proxy_eqs, relevant);
            self.merge_proxy();
            if let Some(x) = retconstraint {
                let x = self.update_constraint(x);
                self.constraints.constraints.push(x);
            }
        }
        true
    }

    pub fn add_constraint<A>(&mut self, a: A) where A: ToConstraint {
        if !self.ok() {
            return;
        }
        let a = a.into_constraint(self);
        let constraint: RcConstraint = Rc::new(Box::new(ConstraintWrapper(a)));
        //let constraint: Rc<Box<Constraint>> = Rc::new(Box::new(a));
        //println!("adding and testing constraint {:?}", constraint);
        self.test_constraints(vec![constraint]);
        //println!("done adding constraint {:?}", msg);
    }

    ///! Create a new variable with the provided value.
    pub fn make_var_of<A>(&mut self, value: A) -> Var<<A as ToVar>::VarType>
    where A : ToVar {
        value.into_var(self)
    }

    //pub fn has_var(&self, var: UntypedVar) -> bool {
        //self.eqs.contains_key(&var)
    //}

    pub fn update_var(&self, var: &mut UntypedVar) {
        *var = self.follow_id(*var);
    }

    fn merge_proxy(&mut self) {
        self.eqs.merge(&mut self.proxy_eqs);
    }
    fn restore_proxy(&mut self) {
        self.proxy_eqs.clear();
        self.proxy_eqs.ok = self.eqs.ok;
    }

    ///! Test whether two vars can be unified, cannot be unified, or are already equal.
    pub fn are_vars_unified<A>(&mut self, a: Var<A>, b: Var<A>) -> Unifiability where A: VarWrapper {
        use core::Unifiability::*;
        {
            let mut proxy = StateProxy::new(self);
            proxy.untyped_unify(a.var, b.var, TypeId::of::<A>(), needs_occurs_check::<A>());
        }
        let result = if self.proxy_eqs.ok {
            if self.proxy_eqs.is_empty() { AlreadyDone } else { Possible }
        } else {
            Impossible
        };
        self.restore_proxy();
        result
    }

    ///! Test whether one var occurs anywhere within another, such as a list element or sublist in
    ///! a list.
    pub fn occurs_check(&mut self, elem: UntypedVar, list: UntypedVar) -> bool {
        // TODO: this does not require &mut self in any way except that that's what StateProxy
        // requires, and VarWrapper::occurs_check can't be generic.
        // This is probably not fixable without finding a better approach for what StateProxy
        // currently does.
        let elem = self.follow_typed(elem);
        let proxy = StateProxy::new(self);
        proxy.occurs_check(elem, list)
    }
}

///! Return type for `State::are_vars_unified`.
#[derive(Eq, PartialEq, Copy, Clone)]
pub enum Unifiability {
    Impossible,
    Possible,
    AlreadyDone,
}

impl<'a> VarRetrieve for StateProxy<'a> {
    fn get_value<A: VarWrapper>(&self, var: Var<A>) -> Option<&A> {
        self.get_exact_val_opt(var.var)
    }
    fn get_untyped(&self, var: UntypedVar) -> Option<&VarWrapper> {
        self.get_exact_val(var)
    }
}

impl<'a> VarStore for StateProxy<'a> {
    fn store_value<A>(&mut self, value: A) -> Var<A>
    where A : VarWrapper + 'static { self.parent.proxy_eqs.store_value(value) }
    fn make_var<A>(&mut self) -> Var<A> where A : VarWrapper { self.parent.proxy_eqs.make_var() }
}

impl<'a> FollowRef for StateProxy<'a> {
    fn get_ref(&self, id: UntypedVar) -> &VarRef {
        match self.parent.proxy_eqs.get(&id) {
            Some(x) => x,
            None => self.parent.get_ref(id)
        }
    }
}

impl<'a> Unifier for StateProxy<'a> {
    fn unify_vars<A>(&mut self, a: Var<A>, b: Var<A>) -> &mut StateProxy<'a>
    where A : VarWrapper {
        self.untyped_unify(a.var, b.var, TypeId::of::<A>(), needs_occurs_check::<A>());
        self
    }

    fn fail(&mut self) -> &mut StateProxy<'a> {
        self.parent.proxy_eqs.ok = false;
        self
    }

    fn ok(&self) -> bool {
        self.parent.proxy_eqs.ok
    }
}

impl<'a> StateProxy<'a> {
    fn new(parent: &'a mut State) -> StateProxy<'a> {
        parent.proxy_eqs.id = parent.eqs.id;
        parent.proxy_eqs.ok = parent.eqs.ok;
        StateProxy { parent: parent }
    }

    pub fn make_var_of<A>(&mut self, value: A) -> Var<<A as ToVar>::VarType> where A: ToVar {
        value.into_var(self)
    }

    pub unsafe fn overwrite_var<A>(&mut self, var: Var<A>, new_value: A)
    where A: VarWrapper + 'static {
        self.parent.proxy_eqs.insert(var.untyped(), Exactly(ExactVal::new(new_value), TypeId::of::<A>()));
    }

    ///! Unify two variables.  Inserts an EqualTo if one or both are unset, or calls _equals_ if
    ///! both are set.  If the value is a container, this will recurse and call unify() on the
    ///! contained types; otherwise it simply compares them.
    fn untyped_unify(&mut self, a: UntypedVar, b: UntypedVar, typeid: TypeId, use_occurs_check: bool) -> bool {
        if !self.parent.ok() {
            //println!("aborting unification early, not ok");
            return false;
        }
        //println!("unifying in state {}: comparing {:?} and {:?} (resolved to {:?} and {:?}", self.depth(), a, b, a_id, b_id);
        // get values
        let (a_val, a_id, b_val, b_id) = {
            // walk references
            let (a_id, a_val, typea) = self.follow_ref(a);
            let (b_id, b_val, typeb) = self.follow_ref(b);
            
            let a_val = a_val.map(|x| x as *const _);
            let b_val = b_val.map(|x| x as *const _);
            
            if a_id == b_id {
                return true;
            }
            // check for reference equality
            if a_val.is_some() && a_val == b_val {
                return true;
            }
            assert!(typea == typeid);
            assert!(typea == typeb);

            // Return values as const ptrs so we can call _equals_ with ourself as the argument later.
            // This should be safe because they point to the boxed values, not into the hashmap
            // (so we'll be okay when it resizes) and there are no safe operations which remove values
            // from it.
            // TODO: it's still gross, though.
            (a_val, a_id, b_val, b_id)
        };
        let (eq_dst, eq_src, src_val) = match (a_val, b_val) {
            (None, b_ex) => (a_id, b_id, b_ex),
            (a_ex, None) => (b_id, a_id, a_ex),
            (Some(a_ex), Some(b_ex)) => {
                let (a_ex, b_ex): (&VarWrapper, &VarWrapper) = unsafe { (&*a_ex, &*b_ex) };
                //println!("comparing {:?} and {:?}", a_ex, b_ex);
                let equals = a_ex.unify_with(&*b_ex, self);
                let ok = match equals.0 {
                    UnifyResultInner::Success => { true },
                    UnifyResultInner::Failure => {
                        self.parent.proxy_eqs.ok = false;
                        false
                    },
                    UnifyResultInner::Overwrite(newval) => {
                        debug_assert!((&*newval).get_type_id() == typeid);
                        debug_assert!(a_ex.uses_overwrite());
                        self.parent.proxy_eqs.insert(a_id, EqualTo(b_id));
                        self.parent.proxy_eqs.insert(b_id, Exactly(Value(newval), typeid));
                        true
                    },
                };
                return ok;
            },
        };

        let src_val: VarRef = match src_val {
            Some(x) => unsafe {
                let x = &*x;

                if use_occurs_check && self.occurs_check_nofollow(TypedVar(eq_dst, typeid), eq_src, x) {
                    self.fail();
                    return false;
                }
                if x.uses_overwrite() { EqualTo(eq_src) }
                else { Exactly(ValuePtr(x), typeid) }
            },
            None => EqualTo(eq_src),
        };
        //println!("assigning {:?} equal to {:?} (= {:?})", eq_dst, eq_src, src_val);
        self.parent.proxy_eqs.insert(eq_dst, src_val);
        true
    }

    pub fn get_updated_var(&self, var: UntypedVar) -> UntypedVar { self.follow_id(var) }

    pub fn get_changed_value<A>(&self, a: Var<A>) -> Option<&A> where A : VarWrapper {
        let mut id = a.var;
        loop {
            match self.parent.proxy_eqs.get(&id).or_else(|| self.parent.eqs.get(&id)) {
                Some(x) => match x {
                    &EqualTo(new_id) => { id = new_id },
                    &Exactly(Fresh, _) => { return None; }
                    &Exactly(Value(ref val), _) => { return Some(val.get_wrapped_value()); },
                    &Exactly(ValuePtr(val), _) => unsafe { return Some((&*val).get_wrapped_value()); },
                },
                None => { return None; },
            }
        }
    }

    pub fn are_vars_unified<A>(&mut self, a: Var<A>, b: Var<A>) -> Unifiability where A: VarWrapper {
        self.inner_are_vars_unified(a.var, b.var, TypeId::of::<A>(), needs_occurs_check::<A>())
    }

    pub fn are_vars_unified_untyped(&mut self, a: UntypedVar, b: UntypedVar) -> Unifiability {
        assert!(self.parent.proxy_eqs.is_empty() && self.parent.proxy_eqs.ok);
        let (a_id, _, a_ty) = self.follow_ref(a);
        let (b_id, _, b_ty) = self.follow_ref(b);
        if a_ty != b_ty {
            return Unifiability::Impossible;
        }
       self.inner_are_vars_unified(a_id, b_id, a_ty, true) // TODO use_occurs_check
    }

    fn inner_are_vars_unified(&mut self, a: UntypedVar, b: UntypedVar, ty: TypeId, use_occurs_check: bool) -> Unifiability {
        use core::Unifiability::*;
        assert!(self.parent.proxy_eqs.is_empty() && self.parent.proxy_eqs.ok);
        self.untyped_unify(a, b, ty, use_occurs_check);
        let result = if self.parent.proxy_eqs.ok {
            if self.parent.proxy_eqs.is_empty() { AlreadyDone } else { Possible }
        } else {
            Impossible
        };
        self.parent.restore_proxy();
        result
    }

    //pub fn get_child_vars(&self, var: UntypedVar) -> Option<VarCollectionIter> {
        //self.get_exact_val(var).opt().map(|x| x.var_iter(self))
    //}

    pub fn occurs_check_typed<A>(&self, elem: TypedVar, list: Var<A>) -> bool
    where A : VarWrapper {
        let (list, listval, _) = self.follow_ref(list.untyped());
        match listval {
            Some(listval) => self.occurs_check_nofollow(elem, list, listval),
            None => list == elem.untyped(),
        }
    }

    #[inline(always)]
    pub fn occurs_check(&self, elem: TypedVar, list: UntypedVar) -> bool {
        let (list, listval, _) = self.follow_ref(list);
        match listval {
            Some(listval) => self.occurs_check_nofollow(elem, list, listval),
            None => list == elem.untyped(),
        }
    }

    fn occurs_check_nofollow(&self, elem: TypedVar, list: UntypedVar, listvar: &VarWrapper) -> bool {
        if elem.untyped() == list {
            true
        } else {
            listvar.occurs_check(self, elem)
        }
    }
}

pub type VarCollectionIter<'a> = Box<Iterator<Item=UntypedVar> + 'a>;

impl VarStore for VarMap {
    ///! Add a variable with a new value to the map.  Called by `make_var_of()`.
    fn store_value<A>(&mut self, value: A) -> Var<A>
    where A : VarWrapper + 'static {
        Var::new(self.store_value_untyped(ExactVal::new(value), TypeId::of::<A>()))
    }

    ///! Create a new variable with no value.
    fn make_var<A>(&mut self) -> Var<A>
    where A : VarWrapper {
        let var = Exactly(Fresh, TypeId::of::<A>());
        let id = self.incr_id();
        self.eqs.push((id, var));
        Var::new(id)
    }
}

impl VarMap {
    fn incr_id(&mut self) -> UntypedVar {
        let UntypedVar(id) = self.id;
        self.id = UntypedVar(id + 1);
        UntypedVar(id)
    }
    fn get(&self, id: &UntypedVar) -> Option<&VarRef> {
        if self.eqs.get(0).map(|&(x, _)| *id < x).unwrap_or(true) {
            return None;
        }
        match self.eqs.binary_search_by(|&(ref var, _)| var.cmp(id)) {
            Ok(x) => Some(&self.eqs[x].1),
            Err(_) => None,
        }
    }
    fn insert(&mut self, id: UntypedVar, val: VarRef) {
        match self.eqs.binary_search_by(|&(var, _)| var.cmp(&id)) {
            Ok(x) => {
                self.eqs[x].1 = val;
            },
            Err(x) => {
                self.eqs.insert(x, (id, val));
            },
        };
    }
    fn new() -> VarMap {
        VarMap {
            id: UntypedVar(0),
            eqs: Vec::new(),
            ok: true,
        }
    }
    fn with_parent(parent: &VarMap) -> VarMap {
        let UntypedVar(id) = parent.id;
        VarMap {
            id: UntypedVar(id + 1),
            eqs: Vec::new(),
            ok: true,
        }
    }
    pub fn contains_key(&self, id: &UntypedVar) -> bool {
        self.eqs.binary_search_by(|&(ref var, _)| var.cmp(id)).is_ok()
    }
    pub fn need_update(&self, var: UntypedVar) -> bool {
        match self.get(&var) {
            Some(&EqualTo(_)) => true,
            _ => false,
        }
    }
    fn store_value_untyped(&mut self, val: ExactVal, typeid: TypeId) -> UntypedVar {
        let id = self.incr_id();
        //println!("storing {:?} as {:?}", value, id);
        let var = Exactly(val, typeid);
        self.eqs.push((id, var));
        id
    }
    fn iter(&self) -> VarMapIter {
        VarMapIter { iter: self.eqs.iter() }
    }
    fn merge(&mut self, other: &mut VarMap) {
        let range = 0..other.eqs.len();
        // TODO: more efficient merge
        for (var, eq) in other.eqs.drain(range) {
            self.insert(var, eq);
        }
        self.id = other.id;
        self.ok = other.ok;
    }
    fn clear(&mut self) {
        self.eqs.clear();
    }
    fn is_empty(&self) -> bool { self.eqs.is_empty() }
}

struct VarMapIter<'a> {
    iter: ::std::slice::Iter<'a, (UntypedVar, VarRef)>,
}

impl<'a> Iterator for VarMapIter<'a> {
    type Item = &'a (UntypedVar, VarRef);
    fn next(&mut self) -> Option<&'a (UntypedVar, VarRef)> {
        self.iter.next()
    }
}

impl ConstraintStore {
    fn new() -> ConstraintStore {
        ConstraintStore { constraints: Vec::new() }
    }

    fn get_relevant_constraints<'a>(&mut self, vars: &VarMap, mut relevant: Vec<RcConstraint>) -> Vec<RcConstraint> {
        let max = self.constraints.len();
        for i in (1..max+1).map(|x| max - x) {
            if self.relevant_constraint_to(i, vars) {
                let constraint = self.constraints.swap_remove(i);
                relevant.push(constraint);
            }
        }
        relevant
    }

    fn relevant_constraint_to<'a>(&mut self, i: usize, vars: &VarMap) -> bool {
        let constraint = &self.constraints[i];
        constraint.relevant(vars)
    }
}

impl<A> Debug for Var<A>
where A : VarWrapper {
    fn fmt(&self, fmt: &mut Formatter) -> ::std::fmt::Result {
        write!(fmt, "Var({})", self.var.0)
    }
}
impl Debug for State {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {

        fn debug_var_ref(me: &State, val: &VarRef, fmt: &mut Formatter) -> fmt::Result {
            match *val {
                EqualTo(x) => write!(fmt, "EqualTo({:?})", x),
                Exactly(ref x, ty) => {
                    let x = unsafe { me.var_opt(x) };
                    try!(write!(fmt, "Exactly("));
                    try!(match x {
                        Some(value) => write!(fmt, "Value({:?})", value),
                        None => write!(fmt, "Fresh")
                    });
                    write!(fmt, ", {:?})", ty)
                }
            }
        }

        try!(writeln!(fmt, "State {{"));
        try!(writeln!(fmt, "\tid: {:?}", self.eqs.id));
        try!(writeln!(fmt, "\tok: {:?}", self.eqs.ok));
        try!(writeln!(fmt, "\tproxy.id: {:?}", self.proxy_eqs.id));
        try!(writeln!(fmt, "\tproxy.ok: {:?}", self.proxy_eqs.ok));
        try!(writeln!(fmt, "\tproxy.eqs: {{"));
        for &(k, ref v) in self.proxy_eqs.iter() {
            try!(write!(fmt, "\t\t{:?} => ", k));
            try!(debug_var_ref(self, v, fmt));
        }
        try!(writeln!(fmt, "\t}}"));

        try!(writeln!(fmt, "\teqs: {{"));
        let mut seen_vars = HashSet::new();
        let mut state = self;
        loop {
            for &(_, ref v) in state.eqs.iter() {
                if let &EqualTo(x) = v {
                    seen_vars.insert(x); 
                }
            }
            for &(k, _) in state.eqs.iter() {
                let tmp_eq = EqualTo(k);
                let mut eq = &tmp_eq;
                if !seen_vars.insert(k) {
                    continue;
                }
                try!(write!(fmt, "\t\t"));
                loop {
                    match eq {
                        &EqualTo(x) => {
                            try!(write!(fmt, "{:?} => ", x));
                            eq = self.get_ref(x);
                        },
                        &Exactly(ref x, _) => {
                            match x {
                                &Fresh => try!(writeln!(fmt, "Fresh")),
                                &Value(ref y) => try!(writeln!(fmt, "{:?}", y)),
                                &ValuePtr(y) => try!(writeln!(fmt, "{:?}", unsafe { &*y })),
                            }
                            break;
                        }
                    }
                }
            }
            state = match state.parent.as_ref() {
                Some(ref x) => {
                    try!(writeln!(fmt, "\t\t---"));
                    &**x
                },
                None => { break; },
            };
        }
        try!(writeln!(fmt, "\tconstraints: {{"));
        for constraint in self.constraints.constraints.iter() {
            try!(writeln!(fmt, "\t\t{:?},", constraint));
        }
        try!(writeln!(fmt, "\t}}"));
        writeln!(fmt, "}}")
    }
}
