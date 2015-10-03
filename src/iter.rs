use core::{ToVar, State, Var, Unifier, VarRetrieve};
use std::rc::Rc;
use std::boxed::FnBox;
use std::marker::PhantomData;

pub fn single(s: State) -> TailIterResult { s.into() }
pub fn none() -> TailIterResult { TailIterResult(None, None) }

pub struct TailIterResult(pub Option<State>, pub Option<TailIter>);

pub struct TailIterIter(TailIterResult);

impl Iterator for TailIterIter {
    type Item = State;
    fn next(&mut self) -> Option<State> {
        self.0.next_boxed()
    }
}

pub type TailIter = Box<TailIterator>;

trait TailIterator {
    fn next(self: Box<Self>) -> TailIterResult;
}

impl TailIterator for Box<FnBox() -> TailIterResult + 'static> {
    fn next(self: Box<Self>) -> TailIterResult { self() }
}

pub struct TailFnWrapper<F: FnOnce() -> TailIterResult + 'static>(F);
impl<F: FnOnce() -> TailIterResult + 'static> TailIterator for TailFnWrapper<F> {
    fn next(self: Box<Self>) -> TailIterResult { self.0() }
}

pub fn wrap_fn<F: FnOnce() -> TailIterResult + 'static>(f: F) -> TailIter {
    Box::new(TailFnWrapper(f))
}

impl TailIterResult {
    pub fn chain(self, other: TailIter) -> TailIterResult {
        match self {
            TailIterResult(None, None) => other.next(),
            TailIterResult(None, Some(x)) => TailIterResult(None, Some(wrap_fn(move || {
                other.next().chain(x)
            }))),
            TailIterResult(Some(x), None) => TailIterResult(Some(x), Some(other)),
            TailIterResult(Some(x), Some(more)) => TailIterResult(Some(x), Some(wrap_fn(move || {
                other.next().chain(more)
            }))),
        }
    }
    pub fn and<F, S>(self, f: F) -> TailIterResult
    where F: Fn(State) -> S + 'static, S: Into<TailIterResult> {
        match self {
            TailIterResult(None, None) => TailIterResult(None, None),
            TailIterResult(None, Some(x)) => TailIterResult(None, Some(wrap_fn(move || x.next().and(f)))),
            TailIterResult(Some(x), None) => f(x).into(),
            TailIterResult(Some(x), Some(more)) => f(x).into().chain(wrap_fn(move || more.next().and(f))),
        }
    }
    pub fn flat_map<F>(self, f: F) -> TailIterResult
    where F: Fn(State) -> TailIterResult + 'static {
        self.and(f)
    }
    pub fn into_iter(self) -> TailIterIter { TailIterIter(self) }
    pub fn next_boxed(&mut self) -> Option<State> {
        let mut tmp = TailIterResult(None, None);
        ::std::mem::swap(&mut tmp, self);
        match tmp {
            TailIterResult(None, None) => None,
            TailIterResult(Some(x), None) => Some(x),
            TailIterResult(None, Some(x)) => {
                *self = x.next();
                self.next_boxed()
            },
            TailIterResult(Some(x), Some(more)) => {
                *self = TailIterResult(None, Some(more));
                Some(x)
            }
        }
    }
}

pub type StateIter = TailIterResult;

impl IterBuilder {
    pub fn new() -> IterBuilder {
        IterBuilder { fns: Vec::new() }
    }
    pub fn push<F, J>(&mut self, f: F)
    where F: Fn(State) -> J + 'static, J: Into<StateIter> + 'static {
        self.fns.push(Box::new(move |state| f(state).into()));
    }

    pub fn conde(self, state: State) -> StateIter {
        if !state.ok() { return TailIterResult(None, None); }
        let mut iter = self.fns.into_iter().rev();
        let state = Rc::new(state);
        let initstate = State::with_parent(state.clone());
        let initfn = iter.next().unwrap();
        let last = TailIterResult(None, Some(wrap_fn(move || initfn(initstate))));
        let chained = iter.fold(last, |accum, f| {
            let child_state = State::with_parent(state.clone());
            let mapped = wrap_fn(move || f(child_state));
            accum.chain(mapped)
        });
        chained
    }

    pub fn conda(self, state: State) -> StateIter {
        if !state.ok() { return TailIterResult(None, None); }
        let state = Rc::new(state);
        let mut iter = self.fns.into_iter();
        
        TailIterResult(None, Some(wrap_fn(move || {
            while let Some(f) = iter.next() {
                let child = State::with_parent(state.clone());
                let mut childiter = f(child);
                if let Some(result) = childiter.next_boxed() {
                    return TailIterResult(Some(result), Some(wrap_fn(move || childiter)));
                }
            }
            TailIterResult(None, None)
        })))
    }
}

pub type WrappedStateIter = Box<Fn(State) -> TailIterResult + 'static>;

pub struct IterBuilder {
    fns: Vec<WrappedStateIter>,
}

impl From<State> for StateIter {
    fn from(s: State) -> StateIter {
        if s.ok() { TailIterResult(Some(s), None) } else { TailIterResult(None, None) }
    }
}

///! An iterator which retrieves the value of a variable from each state in a `StateIter`.
pub struct VarIter<'a, A>
where A : ToVar {
    iter: &'a mut TailIterResult,
    var: Var<A>,
}


impl<'a, A> Iterator for VarIter<'a, A>
where A : ToVar + Clone {
    type Item = Option<A>;
    fn next(&mut self) -> Option<Option<A>> {
        self.iter.next_boxed().map(|x| x.get_value(self.var).map(|val| val.clone()))
    }
}

impl<'a, A> VarIter<'a, A>
where A : ToVar {
    pub fn new(iter: &'a mut StateIter, var: Var<A>) -> VarIter<'a, A> {
        VarIter { iter: iter, var: var }
    }
}

pub trait StateIterExt {
    ///! Helper method to create `VarIter`s.
    fn var_iter<A>(&mut self, var: Var<A>) -> VarIter<A> where A: ToVar;
}

impl StateIterExt for StateIter {
    fn var_iter<A>(&mut self, var: Var<A>) -> VarIter<A> where A: ToVar {
        VarIter::new(self, var)
    }
}


///! Helper to find all results for a given state and iterator.
pub struct FindAll<F>
where F: Fn(State) -> StateIter + 'static {
    state: Rc<State>,
    f: F,
}

impl<F> FindAll<F>
where F: Fn(State) -> StateIter + 'static {
    pub fn new(state: State, f: F) -> FindAll<F> {
        let state = Rc::new(state);
        FindAll { state: state, f: f }
    }
    
    ///! Return an iterator over the output states.
    pub fn iter<'a>(&'a self) -> FindAllIter<'a> {
        let iter = (self.f)(State::with_parent(self.state.clone()));
        // Tying the FindAllIter to our lifetime ensures that self.state is unique, which is
        // required by FindAll's Unifier impl.
        FindAllIter { iter: iter, r: PhantomData }
    }

    ///! Retrieve the wrapped state, destroying the FindAll.
    pub fn state(self) -> State {
        Rc::try_unwrap(self.state).unwrap_or_else(|state| State::with_parent(state.clone()))
    }
}

impl<F> Unifier for FindAll<F>
where F: Fn(State) -> StateIter + 'static {
    fn unify_vars<A>(&mut self, a: Var<A>, b: Var<A>) -> &mut FindAll<F>
    where A : ToVar { Rc::get_mut(&mut self.state).unwrap().unify_vars(a, b); self }
    fn fail(&mut self) -> &mut FindAll<F> { Rc::get_mut(&mut self.state).unwrap().fail(); self }
    fn ok(&self) -> bool { self.state.ok() }
}

///! An iterator over states produced by a FindAll.
pub struct FindAllIter<'a> {
    iter: StateIter,
    r: PhantomData<&'a ()>
}

impl<'a> Iterator for FindAllIter<'a> {
    type Item = State;
    fn next(&mut self) -> Option<State> {
        self.iter.next_boxed()
    }
}

///! An adaptation of Prolog's `findall/3`.  `findall`() enumerates all states produced by the
///! `state_fn` and for each state, unifies `var` with an element of `list`.
pub fn findall_list<F, L, T, V>(mut state: State, list: L, var: V, state_fn: F) -> State
where F: Fn(State) -> StateIter + 'static,
      L: ToVar<VarType=::list::List<Option<Var<<T as ToVar>::VarType>>>>,
      T: ToVar + Clone + PartialEq,
      V: ToVar<VarType=T> {
    use list::{Pair, Nil};
    use core::VarStore;

    let mut list = state.make_var_of(list);
    let var = state.make_var_of(var);
    let state = Rc::new(state);
    let mut return_state = State::with_parent(state.clone());
    let findall_state = State::with_parent(state);
    for state in FindAll::new(findall_state, state_fn).iter() {
        let stateval: Option<T> = state.get_value(var).map(|x| x.clone());
        fresh!(return_state, tail);
        if !return_state.unify(Pair(stateval, tail), list).ok() {
            break;
        }
        list = tail;
    }
    return_state.unify(list, Nil);
    return_state
}
