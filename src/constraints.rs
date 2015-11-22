use std::ops::{Add, Sub};
use core::{ToVar, ToConstraint, Constraint, Var, StateProxy, State, ConstraintResult, VarStore, Unifier, VarRetrieve, VarMap, UntypedVar};
use core::ConstraintResult::*;
use finitedomain::Fd;
use finitedomain::Fd::*;
use std::collections::HashSet;
use std::borrow::Cow;
use core::disequal::Disequal as VarDisequal;

///! The Disequal constraint enforces that its arguments will never have equal values.
pub struct Disequal<A, B, C>
where A: ToVar<VarType=C>, B: ToVar<VarType=C>, C: ToVar {
    a: A,
    b: B,
}

impl<A, B, C> Disequal<A, B, C>
where A: ToVar<VarType=C>, B: ToVar<VarType=C>, C: ToVar {
    pub fn new(a: A, b: B) -> Disequal<A, B, C> {
        Disequal { a: a, b: b }
    }
}

///! The Disequal constraint enforces that its arguments will never have equal values.
impl<A, B, C> ToConstraint for Disequal<A, B, C>
where A: ToVar<VarType=C>, B: ToVar<VarType=C>, C: ToVar {
    type ConstraintType = VarDisequal;
    fn into_constraint(self, state: &mut State) -> VarDisequal {
        let mut disequal = VarDisequal::new_empty();
        let a = state.make_var_of(self.a);
        let b = state.make_var_of(self.b);
        disequal.push(state, a, b);
        disequal
    }
}

///! Constrains three number variables so that A + B = C.
#[derive(Debug, Clone)]
pub struct SumConstraint<A, B, C, D>
where A: ToVar<VarType=A> + Add<Output=A> + PartialEq, B: ToVar<VarType=A>, C: ToVar<VarType=A>, D: ToVar<VarType=A> {
    l: B,
    r: C,
    result: D,
}
pub type VarSumConstraint<A> = SumConstraint<A, Var<A>, Var<A>, Var<A>>;

impl<A, B, C, D> ToConstraint for SumConstraint<A, B, C, D>
where A: ToVar<VarType=A> + Add<Output=A> + Sub<Output=A> + PartialEq + Clone, B: ToVar<VarType=A>, C: ToVar<VarType=A>, D: ToVar<VarType=A> {
    type ConstraintType = SumConstraint<A, Var<A>, Var<A>, Var<A>>;
    fn into_constraint(self, state: &mut State) -> VarSumConstraint<A> {
        let l = state.make_var_of(self.l);
        let r = state.make_var_of(self.r);
        let result = state.make_var_of(self.result);
        SumConstraint { l: l, r: r, result: result }
    }
}

impl<A, B, C, D> SumConstraint<A, B, C, D>
where A: ToVar<VarType=A> + Add<Output=A> + Sub<Output=A> + PartialEq,
B: ToVar<VarType=A>, C: ToVar<VarType=A>, D: ToVar<VarType=A> {
    pub fn new(l: B, r: C, result: D) -> SumConstraint<A, B, C, D> {
        SumConstraint { l: l, r: r, result: result }
    }
}

impl<A> Constraint for VarSumConstraint<A> where A: ToVar<VarType=A> + Add<Output=A> + Sub<Output=A> + PartialEq + Clone {
    fn update(&self, state: &mut StateProxy) -> ConstraintResult<VarSumConstraint<A>> {
        let l = state.get_value(self.l).map(|x| x.clone());
        let r = state.get_value(self.r).map(|x| x.clone());
        let result = state.get_value(self.result).map(|x| x.clone());
        //println!("sumconstraint: l = {:?}, r = {:?}, result = {:?}", l, r, result);
        match (l, r, result) {
            (Some(l), Some(r), _) => {
                let result = state.make_var_of(l + r);
                state.unify_vars(self.result, result);
                if state.ok() { Irrelevant } else { Failed }
            },
            (Some(l), _, Some(result)) => {
                let r = state.make_var_of(result - l);
                state.unify_vars(r, self.r);
                if state.ok() { Irrelevant } else { Failed }
            },
            (_, Some(r), Some(result)) => {
                let l = state.make_var_of(result - r);
                state.unify_vars(l, self.l);
                if state.ok() { Irrelevant } else { Failed }
            },
            _ => Unchanged
        }
    }
    fn relevant(&self, proxy: &VarMap) -> bool {
        proxy.contains_key(&self.l.untyped())
            || proxy.contains_key(&self.r.untyped())
            || proxy.contains_key(&self.result.untyped())
    }
    fn update_vars(&mut self, proxy: &State) {
        proxy.update_var(self.l.untyped_mut());
        proxy.update_var(self.r.untyped_mut());
        proxy.update_var(self.result.untyped_mut());
    }
}

///! Constrains three finite domain variables so that A + B = C.
#[derive(Debug, Clone)]
pub struct FdSumConstraint<A, B, C>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=Fd>, C: ToVar<VarType=Fd> {
    l: A,
    r: B,
    result: C,
}
pub type VarFdSumConstraint = FdSumConstraint<Var<Fd>, Var<Fd>, Var<Fd>>;

impl<A, B, C> ToConstraint for FdSumConstraint<A, B, C>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=Fd>, C: ToVar<VarType=Fd> {
    type ConstraintType = FdSumConstraint<Var<Fd>, Var<Fd>, Var<Fd>>;
    fn into_constraint(self, state: &mut State) -> VarFdSumConstraint {
        let l = state.make_var_of(self.l);
        let r = state.make_var_of(self.r);
        let result = state.make_var_of(self.result);
        FdSumConstraint { l: l, r: r, result: result }
    }
}

impl<A, B, C> FdSumConstraint<A, B, C>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=Fd>, C: ToVar<VarType=Fd> {
    pub fn new(l: A, r: B, result: C) -> FdSumConstraint<A, B, C> {
        FdSumConstraint { l: l, r: r, result: result }
    }
}

impl Constraint for VarFdSumConstraint {
    fn update(&self, state: &mut StateProxy) -> ConstraintResult<VarFdSumConstraint> {
        let (l, r, result) = {
            let l = state.get_value(self.l);//.and_then(|x| x.single_value());
            let r = state.get_value(self.r);//.and_then(|x| x.single_value());
            let result = state.get_value(self.result);//.and_then(|x| x.single_value());
            //println!("sumconstraint: l = {:?}, r = {:?}, result = {:?}", l, r, result);
            (l.and_then(|x| x.single_value()),
                r.and_then(|x| x.single_value()),
                result.and_then(|x| x.single_value()))
        };

        match (l, r, result) {
            (Some(l), Some(r), _) => {
                //let result = state.make_var_of(l + r);
                let result = Fd::new_single(l + r);
                //println!("sumconstraint: creating result {:?} and unifying with {:?}", l + r, self.result);
                state.unify(self.result, result);
                if state.ok() { Irrelevant } else { Failed }
            },
            (Some(l), _, Some(result)) => {
                if l > result { return Failed; }
                let r = Fd::new_single(result - l);
                state.unify(r, self.r);
                if state.ok() { Irrelevant } else { Failed }
            },
            (_, Some(r), Some(result)) => {
                if r > result { return Failed; }
                let l = Fd::new_single(result - r);
                state.unify(l, self.l);
                if state.ok() { Irrelevant } else { Failed }
            },
            _ => Unchanged
        }
    }
    fn relevant(&self, proxy: &VarMap) -> bool {
        proxy.contains_key(&self.l.untyped())
            || proxy.contains_key(&self.r.untyped())
            || proxy.contains_key(&self.result.untyped())
    }
    fn update_vars(&mut self, proxy: &State) {
        proxy.update_var(self.l.untyped_mut());
        proxy.update_var(self.r.untyped_mut());
        proxy.update_var(self.result.untyped_mut());
    }
}

///! Constrains two finite domain variables so that A <= B.
#[derive(Debug, Clone)]
pub struct FdLessOrEqual<A, B>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=Fd> {
    l: A,
    r: B,
}
pub type VarFdLessOrEqual = FdLessOrEqual<Var<Fd>, Var<Fd>>;

impl<A, B> FdLessOrEqual<A, B>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=Fd> {
    pub fn new(l: A, r: B) -> FdLessOrEqual<A, B> {
        FdLessOrEqual { l: l, r: r }
    }
}

impl<A, B> ToConstraint for FdLessOrEqual<A, B>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=Fd> {
    type ConstraintType = FdLessOrEqual<Var<Fd>, Var<Fd>>;
    fn into_constraint(self, state: &mut State) -> VarFdLessOrEqual {
        let l = state.make_var_of(self.l);
        let r = state.make_var_of(self.r);
        FdLessOrEqual { l: l, r: r }
    }
}

fn constrain_range(min: Option<usize>, max: Option<usize>, vals: &[usize]) -> Fd {
    let end = max.map(|max| match vals.binary_search(&max) {
        Ok(x) => x + 1,
        Err(x) => x,
    }).unwrap_or(vals.len());
    let start = min.map(|min| match vals.binary_search(&min) {
        Ok(x) => x,
        Err(x) => x,
    }).unwrap_or(0);
    Fd::Values(vals[start..end].iter().map(|x| *x).collect())
}

impl Constraint for VarFdLessOrEqual {
    fn update(&self, state: &mut StateProxy) -> ConstraintResult<VarFdLessOrEqual> {
        use core::ConstraintResult::*;
        let (new_l, new_r) = {
            let (l, r) = match (state.get_value(self.l), state.get_value(self.r)) {
                (Some(l), Some(r)) => (l, r),
                _ => { return Unchanged; },
            };
            match (l, r) {
                (&Values(ref lvals), &Values(ref rvals)) => {
                    //println!("a");
                    (constrain_range(None, Some(*rvals.last().unwrap()), &*lvals),
                     constrain_range(Some(*lvals.first().unwrap()), None, &*rvals))
                },
                (&Values(ref lvals), &Single(max)) => {
                    //println!("b");
                    (constrain_range(None, Some(max), &*lvals),
                    match max < *lvals.first().unwrap() {
                        true => Fd::err(),
                        false => Fd::new_single(max),
                    })
                },
                (&Single(min), &Values(ref rvals)) => {
                    //println!("c");
                    (match *rvals.last().unwrap() < min {
                        true => Fd::err(),
                        false => Fd::new_single(min),
                    },
                    constrain_range(Some(min), None, &*rvals))
                },
                (&Single(min), &Single(max)) => {
                    //println!("d");
                    match max < min {
                        true => (Fd::err(), Fd::err()),
                        false => (Fd::new_single(min), Fd::new_single(max)),
                    }
                },
            }
        };
        //println!("got result values: {:?} and {:?}", new_l, new_r);
        if !new_l.is_valid() || !new_r.is_valid() {
            //println!("returning early, failed");
            return Failed;
        }
        let result = match new_l.single_value().is_some() || new_r.single_value().is_some() {
            true => Irrelevant,
            false => Unchanged,
        };
        unsafe {
            state.overwrite_var(self.l, new_l);
            state.overwrite_var(self.r, new_r);
        }
        result
    }
    fn relevant(&self, proxy: &VarMap) -> bool {
        proxy.contains_key(&self.l.untyped()) || proxy.contains_key(&self.r.untyped())
    }
    fn update_vars(&mut self, proxy: &State) {
        proxy.update_var(self.l.untyped_mut());
        proxy.update_var(self.r.untyped_mut());
    }
}

impl ToConstraint for AllDiffConstraint {
    type ConstraintType = AllDiffConstraint;
    fn into_constraint(self, _: &mut State) -> AllDiffConstraint { self }
}

///! Constrains a set of Fds to have distinct values from one another.
#[derive(Debug, Clone)]
pub struct AllDiffConstraint {
    fds: Vec<Var<Fd>>,
}

impl AllDiffConstraint {
    pub fn new(fds: Vec<Var<Fd>>) -> AllDiffConstraint {
        AllDiffConstraint { fds: fds }
    }

    fn remove_singles(varfds: &mut Vec<(Var<Fd>, Option<Fd>)>, singles: &mut HashSet<usize>, mut state: Option<&mut StateProxy>, remove_var: bool) -> bool {
        for i in (0..varfds.len()).rev() {
            let remove = {
                let (_, ref fd) = varfds[i];
                if let Some(ref fd) = *fd {
                    if let Some(single) = fd.single_value() {
                        //println!("value for {:?}: {:?}", fd, single);
                        if !singles.insert(single) {
                            return false;
                        }
                        true
                    } else { false }
                } else { false }
            };
            if remove {
                let (var, fd) = if remove_var {
                    varfds.swap_remove(i)
                } else {
                    let &mut (var, ref mut fd) = &mut varfds[i];
                    (var, fd.take())
                };
                let fd = fd.unwrap();
                if let Some(ref mut state) = state {
                    unsafe { state.overwrite_var(var, fd); }
                }
            }
        }
        true
    }
}

impl Constraint for AllDiffConstraint {
    fn update(&self, state: &mut StateProxy) -> ConstraintResult<AllDiffConstraint> {
        use core::ConstraintResult::*;
        // unique values which must be removed from other fds
        // indexes into self.fds, and later replace.fds, for unique fds which can be removed
        if !self.fds.iter().any(|&var| {
            state.get_changed_value(var).and_then(|fd| fd.single_value()).is_some()
        }) {
            return Unchanged;
        }
        let mut varfds: Vec<(Var<Fd>, Option<Fd>)> = self.fds.iter().map(|fd| {
            (*fd, state.get_value(*fd).map(|x| x.clone()))
        }).collect();
        let mut singles = HashSet::new();
        let all_set = varfds.iter().all(|&(_, ref val)| val.is_some());
        if !AllDiffConstraint::remove_singles(&mut varfds, &mut singles, None, all_set) {
            return Failed;
        }
        //println!("got {} singles", singles.len());
        loop {
            if singles.is_empty() {
                let overwrite = varfds.into_iter().map(|(var, fd)| {
                    //println!("overwriting {:?} with {:?}", var, fd);
                    if let Some(fd) = fd {
                        unsafe { state.overwrite_var(var, fd); }
                    }
                    var
                });
                return if all_set {
                    let replace = AllDiffConstraint::new(overwrite.collect());
                    Updated(replace)
                } else {
                    for _ in overwrite { }
                    Unchanged
                };
            }
            if varfds.is_empty() {
                return Irrelevant;
            }

            //println!("removing values {:?} from {} fds", singles, varfds.len());
            for &mut (_, ref mut fd) in varfds.iter_mut() {
                if let Some(ref mut fd) = *fd {
                    fd.remove_values(&singles);
                    if !fd.is_valid() {
                        return Failed;
                    }
                }
            }
            singles.clear();
            if !AllDiffConstraint::remove_singles(&mut varfds, &mut singles, Some(state), all_set) {
                return Failed;
            }
        }
    }
    fn relevant(&self, proxy: &VarMap) -> bool {
        self.fds.iter().any(|fd| {
            proxy.contains_key(&fd.untyped())
        })
    }
    fn update_vars(&mut self, proxy: &State) {
        for fd in self.fds.iter_mut() {
            proxy.update_var(fd.untyped_mut());
        }
    }
    fn need_update(&self, vars: &VarMap) -> bool {
        self.fds.iter().any(|fd| { vars.need_update(fd.untyped()) })
    }
}

///! Constrains an Fd and a usize to have the same value.
#[derive(Debug, Clone)]
pub struct FdUsizeConstraint<A, B>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=usize> {
    fd: A,
    u: B,
}
pub type VarFdUsizeConstraint = FdUsizeConstraint<Var<Fd>, Var<usize>>;

impl<A, B> ToConstraint for FdUsizeConstraint<A, B>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=usize> {
    type ConstraintType = FdUsizeConstraint<Var<Fd>, Var<usize>>;
    fn into_constraint(self, state: &mut State) -> VarFdUsizeConstraint {
        let fd = state.make_var_of(self.fd);
        let u = state.make_var_of(self.u);
        FdUsizeConstraint { fd: fd, u: u }
    }
}

impl<A, B> FdUsizeConstraint<A, B>
where A: ToVar<VarType=Fd>, B: ToVar<VarType=usize> {
    pub fn new(fd: A, u: B) -> FdUsizeConstraint<A, B> {
        FdUsizeConstraint { fd: fd, u: u }
    }
}

impl Constraint for VarFdUsizeConstraint {
    fn update(&self, state: &mut StateProxy) -> ConstraintResult<VarFdUsizeConstraint> {
        use core::ConstraintResult::*;
        let single_value = {
            if let Some(u) = state.get_value(self.u) { Some(*u) }
            else if let Some(fd) = state.get_value(self.fd) {
                fd.single_value()
            }
            else { None }
        };
        if let Some(x) = single_value {
            state.unify(Single(x), self.fd);
            state.unify(x, self.u);
            Irrelevant
        } else {
            Unchanged
        }
    }
    fn relevant(&self, proxy: &VarMap) -> bool {
        proxy.contains_key(&self.fd.untyped()) || proxy.contains_key(&self.u.untyped())
    }
    fn update_vars(&mut self, proxy: &State) {
        proxy.update_var(self.fd.untyped_mut());
        proxy.update_var(self.fd.untyped_mut());
    }
}

///! Constrains two variables, an element and a container, so that the element cannot be unified
///! with anything in the container.
pub struct AbsentConstraint<A, B, C>
where A: ToVar, B: ToVar<VarType=A>, C: ToVar {
    elem: B,
    list: C,
}

///! Implementation of `AbsentConstraint`.  Don't use this directly, use `AbsentConstraint`.
#[derive(Debug)]
pub struct VarAbsentConstraint<A> where A: ToVar {
    elem: Var<A>,
    list: Vec<UntypedVar>,
    fresh: Vec<UntypedVar>,
}

impl<A> Clone for VarAbsentConstraint<A> where A: ToVar {
    fn clone(&self) -> VarAbsentConstraint<A> {
        VarAbsentConstraint { elem: self.elem, list: self.list.clone(), fresh: self.fresh.clone() }
    }
}

impl<A, B, C> ToConstraint for AbsentConstraint<A, B, C>
where A: ToVar, B: ToVar<VarType=A>, C: ToVar {
    type ConstraintType = VarAbsentConstraint<A>;
    fn into_constraint(self, state: &mut State) -> VarAbsentConstraint<A> {
        let elem = state.make_var_of(self.elem);
        let listvar = state.make_var_of(self.list);
        let mut fresh = Cow::Owned(vec![listvar.untyped()]);
        let mut list = Cow::Owned(Vec::new());
        push_tail(&mut list, &mut fresh, state);
        VarAbsentConstraint { elem: elem, list: list.into_owned(), fresh: fresh.into_owned() }

        ////let 
        ////let constraint = VarAbsentConstraint { elem: elem, list: Vec::new(), fresh: vec![list.untyped()] };
        ////let mut cow = Cow::Owned(constraint);
        ////push_tail(&mut cow, state);
        //cow.into_owned()
    }
}

impl<A, B, C> AbsentConstraint<A, B, C>
where A: ToVar, B: ToVar<VarType=A>, C: ToVar {
    pub fn new(elem: B, list: C) -> AbsentConstraint<A, B, C> {
        AbsentConstraint { elem: elem, list: list }
    }
}

fn push_tail<U: VarRetrieve>(list: &mut Cow<Vec<UntypedVar>>, fresh: &mut Cow<Vec<UntypedVar>>, state: &U) {
    //use list::List::Pair as VarPair;
    //use list::Nil;

    let mut i = 0usize;
    while let Some(&var) = fresh.get(i) {
        if let Some(val) = state.get_untyped(var) {
            fresh.to_mut().swap_remove(i);
            list.to_mut().push(var);
            if let Some(iter) = val.var_iter() {
                for inner_var in iter {
                    fresh.to_mut().push(inner_var);
                }
            }
        } else {
            i += 1;
        }
    }
}

fn check_unify(state: &mut StateProxy, list: &mut Cow<Vec<UntypedVar>>, elem: UntypedVar) -> bool {
    use core::Unifiability::*;
    let mut i = 0;
    while let Some(&var) = list.get(i) {
        match state.are_vars_unified_untyped(var, elem) {
            Impossible => { list.to_mut().swap_remove(i); },
            Possible => {
                if state.get_untyped(var).is_some() && state.get_untyped(elem).is_some() {
                    return false;
                } else {
                    i += 1;
                }
            },
            AlreadyDone => { return false; }
        }
    }
    return true;
}

impl<A> Constraint for VarAbsentConstraint<A> where A: ToVar {
    fn update(&self, state: &mut StateProxy) -> ConstraintResult<VarAbsentConstraint<A>> {
        //let mut me = Cow::Borrowed(self);
        //push_tail(&mut me, state);

        let mut list = Cow::Borrowed(&self.list);
        let mut fresh = Cow::Borrowed(&self.fresh);
        //println!("started, proxy ok: {}", state.ok());
        push_tail(&mut list, &mut fresh, state);
        //println!("push_tail, proxy ok: {}", state.ok());
        if !check_unify(state, &mut list, self.elem.untyped()) {
            return ConstraintResult::Failed;
        }
        if fresh.is_empty() && list.is_empty() {
            return ConstraintResult::Irrelevant;
        }

        match (list, fresh) {
            (Cow::Borrowed(_), Cow::Borrowed(_)) => ConstraintResult::Unchanged,
            (list, fresh) => {
                ConstraintResult::Updated(VarAbsentConstraint {
                    elem: self.elem,
                    list: list.into_owned(),
                    fresh: fresh.into_owned(),
                })
            },
        }
    }

    fn relevant(&self, proxy: &VarMap) -> bool {
        proxy.contains_key(&self.elem.untyped())
            || self.list.iter().any(|x| proxy.contains_key(x))
            || self.fresh.iter().any(|x| proxy.contains_key(x))
    }
    fn update_vars(&mut self, proxy: &State) {
        proxy.update_var(self.elem.untyped_mut());
        for elem in self.list.iter_mut() {
            proxy.update_var(elem);
        }
        for elem in self.fresh.iter_mut() {
            proxy.update_var(elem);
        }
    }
}
