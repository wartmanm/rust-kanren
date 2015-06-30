use core::{ToVar, State, Var, Unifier, VarRetrieve};
use std::rc::Rc;
use std::boxed::FnBox;
use tailiter::{TailIterator, TailIterHolder, TailIterItem};
use tailiter::TailIterItem::*;
use std::marker::PhantomData;

pub type StateIter = TailIterHolder<State>;

struct SingleIter {
    state: Option<State>,
}

///! Transforms a state into a `TailIterator` which returns that state.
pub fn single(state: State) -> StateIter {
    let state = match state.ok() {
        true => Some(state),
        false => None,
    };
    TailIterHolder::new(SingleIter { state: state })
}

impl TailIterator for SingleIter {
    type Item = State;
    fn next_inner(&mut self) -> TailIterItem<State> {
        self.state.take().map(SingleItem).unwrap_or(Done)
    }
}

///! Creates a `TailIterator` which returns no states at all.
pub fn none() -> StateIter { TailIterHolder::new(NoneIter) }

struct NoneIter;

impl TailIterator for NoneIter {
    type Item = State;
    fn next_inner(&mut self) -> TailIterItem<State> { Done }
}

struct CondeIter {
    fns: ::std::vec::IntoIter<WrappedStateIter>,
    current: Option<StateIter>,
    state: Option<Rc<State>>,
}

struct CondiIter {
    fns: ::std::vec::IntoIter<WrappedStateIter>,
    iters: Vec<StateIter>,
    pos: usize,
    state: Option<Rc<State>>,
}

struct CondaIter {
    fns: ::std::vec::IntoIter<WrappedStateIter>,
    current: Option<StateIter>,
    state: Rc<State>,
}

struct ConduIter {
    fns: ::std::vec::IntoIter<WrappedStateIter>,
    state: Rc<State>,
    done: bool
}

///! An iterator which retrieves the value of a variable from each state in a `StateIter`.
pub struct VarIter<'a, A>
where A : ToVar {
    iter: &'a mut StateIter,
    var: Var<A>,
}

type WrappedStateIter = Box<FnBox(State) -> StateIter + 'static>;

///! Collects `|State| -> StateIter` closures and transforms them into one of the different
///! disjoint iterators.
///!
///! These are created by the `cond!()` macros, you probably don't need to create one yourself unless
///! you want to.
pub struct IterBuilder {
    fns: Vec<WrappedStateIter>,
}

impl IterBuilder {
    pub fn new() -> IterBuilder {
        IterBuilder { fns: Vec::new() }
    }
    pub fn push<F, J>(&mut self, f: F)
    where F: FnOnce(State) -> J + 'static, J: Into<StateIter> + 'static {
        self.fns.push(Box::new(move |state| f(state).into()));
    }

    ///! Create a `TailIterator` which applies the provided `State` to each of its child functions in
    ///! depth-first fashion, exhausting one before moving on to the next.
    pub fn conde(self, state: State) -> StateIter {
        if !state.ok() { return none(); }
        TailIterHolder::new(CondeIter { fns: self.fns.into_iter(), current: None, state: Some(Rc::new(state)) })
    }

    ///! Create a `TailIterator` which applies the provided `State` to each of its child functions in
    ///! breadth-first fashion, returning one value at a time from each of them.
    pub fn condi(self, state: State) -> StateIter {
        if !state.ok() { return none(); }

        let iters = Vec::with_capacity(self.fns.len());
        TailIterHolder::new(CondiIter { fns: self.fns.into_iter(), iters: iters, pos: 0, state: Some(Rc::new(state)) })
    }

    ///! Create a `TailIterator` which applies the provided `State` to each of its child functions,
    ///! but only returns the values of the first one which produces any results, ignoring the
    ///! others.
    ///!
    ///! In the original implementation, a precondition is to determine which child to use, which
    ///! can then return zero or more results.  I'm not sure how to represent this, so it's not
    ///! likely to be very useful.
    pub fn conda(self, state: State) -> StateIter {
        if !state.ok() { return none(); }
        TailIterHolder::new(CondaIter { fns: self.fns.into_iter(), state: Rc::new(state), current: None })
    }

    ///! Create a `TailIterator` which applies the provided `State` to each of its child functions,
    ///! but returns at most a single value.
    ///!
    ///! In the original implementation, a precondition is to determine which child to use, which
    ///! can then return zero or more results.  I'm not sure how to represent this, so it's not
    ///! likely to be very useful.
    pub fn condu(self, state: State) -> StateIter {
        if !state.ok() { return none(); }
        TailIterHolder::new(ConduIter { fns: self.fns.into_iter(), state: Rc::new(state), done: false })
    }
}

fn try_unwrap_state(state: Rc<State>) -> State {
    Rc::try_unwrap(state).unwrap_or_else(State::with_parent)
}

// TODO: eliminate duplication with TailFlatMapper
impl TailIterator for CondeIter {
    type Item = State;
    fn next_inner(&mut self) -> TailIterItem<State> {
        loop {
            if let Some(ref mut current) = self.current {
                if let Some(x) = current.next_boxed() {
                    return SingleItem(x);
                }
            }
            let current_fn = self.fns.next().unwrap();
            
            if self.fns.len() == 0 {
                let state = try_unwrap_state(self.state.take().unwrap());
                return Tail(current_fn(state));
            }

            let state = State::with_parent(self.state.as_ref().unwrap().clone());
            self.current = Some(current_fn(state));
        }
    }
}

// TODO: eliminate duplication with TailFlatIMapper
impl TailIterator for CondiIter {
    type Item = State;
    fn next_inner(&mut self) -> TailIterItem<State> {
        loop {
            let f = self.fns.next();
            if let Some(f) = f {
                if self.iters.is_empty() && self.fns.len() == 0 {
                    let state = try_unwrap_state(self.state.take().unwrap());
                    return Tail(f(state));
                }
                let state = State::with_parent(self.state.as_ref().unwrap().clone());
                self.iters.push(f(state));
            } else if self.iters.len() == 1 {
                return Tail(self.iters.pop().unwrap());
            }
            self.pos = self.pos % self.iters.len();
            if let Some(x) = self.iters[self.pos].next_boxed() {
                self.pos += 1;
                return SingleItem(x);
            }
            self.iters.remove(self.pos);
        }
    }
}

impl TailIterator for CondaIter {
    type Item = State;
    fn next_inner(&mut self) -> TailIterItem<State> {
        if let Some(current) = self.current.take() {
            return Tail(current);
        }
        while let Some(f) = self.fns.next() {
            let state = State::with_parent(self.state.clone());
            let mut iter = f(state);
            if let Some(next) = iter.next_boxed() {
                self.current = Some(iter);
                return SingleItem(next);
            }
        }
        return Done;
    }
}

impl TailIterator for ConduIter {
    type Item = State;
    fn next_inner(&mut self) -> TailIterItem<State> {
        if self.done {
            return Done;
        }
        while let Some(f) = self.fns.next() {
            let state = State::with_parent(self.state.clone());
            let mut iter = f(state);
            if let Some(next) = iter.next_boxed() {
                self.done = true;
                return SingleItem(next);
            }
        }
        return Done;

    }
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

impl From<State> for StateIter {
    fn from(s: State) -> StateIter { single(s) }
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

pub trait StateExt {
    fn and<F, J>(self, f: F) -> StateIter where F: Fn(State) -> J + 'static, J: Into<StateIter>;
}

impl StateExt for State {
    fn and<F, J>(self, f: F) -> StateIter where F: Fn(State) -> J + 'static, J: Into<StateIter> {
        f(self).into()
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
