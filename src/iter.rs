use core::{ToVar, State, Var, Unifier, VarRetrieve};
use std::rc::Rc;
use std::boxed::FnBox;
use iter::TailIterResult::*;
use std::marker::PhantomData;

pub fn single(s: State) -> TailIterResult { s.into() }
pub fn none() -> TailIterResult { Nothing }

pub enum TailIterResult {
    Nothing,
    Last(State),
    Wrapped(TailIter),
    More(State, TailIter),
}

pub struct TailIterIter(TailIterResult);

impl Iterator for TailIterIter {
    type Item = State;
    fn next(&mut self) -> Option<State> {
        self.0.next_boxed()
    }
}

pub type TailIter = Box<FnBox() -> TailIterResult + 'static>;

impl TailIterResult {
    pub fn chain(self, other: TailIter) -> TailIterResult {
        match self {
            Nothing => other(),
            Wrapped(x) => Wrapped(Box::new(move || other().chain(x))),
            Last(x) => More(x, other),
            More(s, more) => More(s, Box::new(move || other().chain(more))),
        }
    }
    pub fn and<F, S>(self, f: F) -> TailIterResult
    where F: Fn(State) -> S + 'static, S: Into<TailIterResult> {
        match self {
            Nothing => Nothing,
            Wrapped(x) => Wrapped(Box::new(move || x().and(f))),
            Last(x) => f(x).into(),
            More(s, more) => f(s).into().chain(Box::new(move || more().and(f))),
        }
    }
    pub fn flat_map<F>(self, f: F) -> TailIterResult
    where F: Fn(State) -> TailIterResult + 'static {
        self.and(f)
    }
    pub fn into_iter(self) -> TailIterIter { TailIterIter(self) }
    pub fn next_boxed(&mut self) -> Option<State> {
        let mut tmp = Nothing;
        ::std::mem::swap(&mut tmp, self);
        match tmp {
            Nothing => None,
            Last(x) => Some(x),
            Wrapped(x) => {
                *self = x();
                self.next_boxed()
            },
            More(s, more) => {
                *self = Wrapped(more);
                Some(s)
            }
        }
    }
}

pub type StateIter = TailIterResult;

impl IterBuilder {
    //pub fn get_fns(self) -> Vec<Box<FnBox(State) -> StateIter + 'static>> { self.fns }
    pub fn new() -> IterBuilder {
        IterBuilder { fns: Vec::new() }
    }
    pub fn push<F, J>(&mut self, f: F)
    where F: Fn(State) -> J + 'static, J: Into<StateIter> + 'static {
        self.fns.push(Box::new(move |state| f(state).into()));
    }

    pub fn conde(self, state: State) -> StateIter {
        if !state.ok() { return Nothing; }
        //let state = Rc::new(state);
        let mut iter = self.fns.into_iter().rev();
        let state = Rc::new(state);
        //let last = Last(state);
        let initstate = State::with_parent(state.clone());
        let initfn = iter.next().unwrap();
        let last = Wrapped(Box::new(move || initfn(initstate)));
        let chained = iter.fold(last, |accum, f| {
            let child_state = State::with_parent(state.clone());
            let mapped = Box::new(move || f(child_state));
            accum.chain(mapped)
        });
        chained
    }

    pub fn conda(self, state: State) -> StateIter {
        if !state.ok() { return Nothing; }
        let state = Rc::new(state);
        let mut iter = self.fns.into_iter();
        
        Wrapped(Box::new(move || {
            while let Some(f) = iter.next() {
                let child = State::with_parent(state.clone());
                let mut childiter = f(child);
                if let Some(result) = childiter.next_boxed() {
                    return More(result, Box::new(move || childiter));
                }
            }
            Nothing
        }))
    }
}

pub type WrappedStateIter = Box<Fn(State) -> TailIterResult + 'static>;

pub struct IterBuilder {
    fns: Vec<WrappedStateIter>,
}

impl From<State> for StateIter {
    fn from(s: State) -> StateIter {
        if s.ok() { Last(s) } else { Nothing }
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
