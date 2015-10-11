use core::{ToVar, State, Var, Unifier, VarRetrieve};
use std::rc::Rc;
use std::marker::PhantomData;
use std::any::*;
use std::raw::TraitObject;
use std::collections::VecDeque;

///! Creates a `TailIterResult` with one value.
pub fn single(s: State) -> TailIterResult { s.into() }
///! Creates a `TailIterResult` with no values.
pub fn none() -> TailIterResult { TailIterResult(None, None) }

///! An iterator consisting of an optional result and optional continuation.  This makes it
///! possible to shorten deep chains of iterators if one of them has been exhausted of results, in
///! addition to distinguishing iterators that need to do additional work from those that can
///! return a value immediately.
pub struct TailIterResult(pub Option<State>, pub Option<TailIter>);

///! `TailIterIter` provides a normal Rust iterator over a `TailIterResult` iterator.
pub struct TailIterIter(TailIterResult);

impl Iterator for TailIterIter {
    type Item = State;
    fn next(&mut self) -> Option<State> {
        self.0.next()
    }
}

pub type TailIter = Box<TailIterator>;

///! The trait used for the continuation portion of a TailI`terResult` iterator.
trait TailIterator: Any {
    fn next(self: Box<Self>) -> TailIterResult;
}

///! Used by wrap_fn.
struct TailFnWrapper<F: FnOnce() -> TailIterResult + 'static>(F);
impl<F: FnOnce() -> TailIterResult + Any + 'static> TailIterator for TailFnWrapper<F> {
    fn next(self: Box<Self>) -> TailIterResult { self.0() }
}

///! Transforms a function producing a `TailIterResult` into a `TailIter`.
pub fn wrap_fn<F: FnOnce() -> TailIterResult + Any + 'static>(f: F) -> TailIter {
    Box::new(TailFnWrapper(f))
}

struct ChainManyIter {
    chain:VecDeque<TailIter>,
    iter: Option<Box<Iterator<Item=TailIterResult> + 'static>>,
}

impl TailIterator for ChainManyIter {
    fn next(mut self: Box<Self>) -> TailIterResult {
        let iter_next = self.iter.as_mut().and_then(|x| x.next());
        let next = match iter_next {
            Some(x) => x,
            None => {
                if self.chain.len() <= 1 {
                    return TailIterResult(None, self.chain.pop_front());
                }
                self.chain.pop_front().unwrap().next()
            }
        };
        match next {
            TailIterResult(None, None) => {
                TailIterResult(None, Some(self)) // TODO call self.next() instead?
            }
            TailIterResult(Some(x), None) => TailIterResult(Some(x), Some(self)),
            TailIterResult(x, Some(more)) => {
                self.chain.push_back(more);
                TailIterResult(x, Some(self))
            }
        }
    }
}

struct AndIter<S: Into<TailIterResult> + Any + 'static> {
    f: Box<Fn(State) -> S + 'static>,
    iter: Option<TailIter>,
}

impl<S: Into<TailIterResult> + Any + 'static> TailIterator for AndIter<S> {
    fn next(mut self: Box<Self>) -> TailIterResult {
        let current = self.iter.take().unwrap();
        match current.next() {
            TailIterResult(None, None) => TailIterResult(None, None),
            TailIterResult(None, Some(x)) => {
                self.iter = Some(x);
                TailIterResult(None, Some(self))
            },
            TailIterResult(Some(x), None) => (self.f)(x).into(),
            TailIterResult(Some(x), Some(more)) => {
                self.iter = Some(more);
                (self.f)(x).into().chain(self)
            }
        }
    }
}

struct CondaIter {
    iter: Box<Iterator<Item=TailIterResult> + 'static>,
    return_more: bool,
}

impl TailIterator for CondaIter {
    fn next(mut self: Box<Self>) -> TailIterResult {
        let mut next = match self.iter.next() {
            Some(x) => x,
            None => { return TailIterResult(None, None); }
        };
        loop {
            next = match next {
                TailIterResult(None, None) => { return TailIterResult(None, Some(self)); },
                TailIterResult(Some(x), next_more) => {
                    let more = if self.return_more { next_more } else { None };
                    return TailIterResult(Some(x), more);
                },
                TailIterResult(None, Some(x)) => {
                    x.next()
                },
            }
        }
    }
}

impl TailIterator {
    pub fn downcast_mut<T>(&mut self) -> Option<&mut T>
    where T: Any + 'static {
        if TypeId::of::<T>() == (*self).get_type_id() {
            let x: TraitObject = unsafe { ::std::mem::transmute(self) };
            Some(unsafe { ::std::mem::transmute(x.data) })
        } else {
            None
        }
    }
}

impl TailIterResult {
    pub fn chain(self, other: TailIter) -> TailIterResult {
        match self {
            TailIterResult(None, None) => other.next(),
            TailIterResult(Some(x), None) => TailIterResult(Some(x), Some(other)),
            TailIterResult(x, Some(mut more)) => {
                if TypeId::of::<ChainManyIter>() == (*more).get_type_id() {
                    {
                        let chain = more.downcast_mut::<ChainManyIter>().unwrap();
                        chain.chain.push_front(other);
                    }
                    return TailIterResult(x, Some(more));
                }
                let mut chain = VecDeque::with_capacity(2);
                chain.push_back(other);
                chain.push_back(more);
                let iter = Box::new(ChainManyIter { chain: chain, iter: None });
                return TailIterResult(x, Some(iter));
            }
        }
    }
    ///! Synonym for `flat_map`.
    pub fn and<F, S>(self, f: F) -> TailIterResult
    where F: Fn(State) -> S + 'static, S: Into<TailIterResult> + Any + 'static {
        self.and_inner(Box::new(f))
    }

    fn and_inner<S>(self, f: Box<Fn(State) -> S + 'static>) -> TailIterResult
    where S: Into<TailIterResult> + Any + 'static {
        match self {
            TailIterResult(None, None) => TailIterResult(None, None),
            TailIterResult(None, Some(x)) => TailIterResult(None, Some(Box::new(AndIter { f: f, iter: Some(x) }))),
            TailIterResult(Some(x), None) => f(x).into(),
            TailIterResult(Some(x), Some(more)) => f(x).into().chain(Box::new(AndIter { f: f, iter: Some(more) }))
        }
    }
    pub fn flat_map<F>(self, f: F) -> TailIterResult
    where F: Fn(State) -> TailIterResult + 'static {
        self.and(f)
    }
    pub fn into_iter(self) -> TailIterIter { TailIterIter(self) }
    pub fn next(&mut self) -> Option<State> {
        let mut tmp = TailIterResult(None, None);
        ::std::mem::swap(&mut tmp, self);
        match tmp {
            TailIterResult(None, None) => None,
            TailIterResult(Some(x), None) => Some(x),
            TailIterResult(None, Some(x)) => {
                *self = x.next();
                self.next()
            },
            TailIterResult(Some(x), Some(more)) => {
                *self = TailIterResult(None, Some(more));
                Some(x)
            }
        }
    }
}

pub type StateIter = TailIterResult;

///! Used internally by IterBuilder to iterate over alternatives.
struct StateFnIter<F>
where F: Fn(usize, State) -> StateIter + 'static {
    f: F,
    state: Rc<State>,
    len: usize,
    pos: usize,
}

impl<F> Iterator for StateFnIter<F>
where F: Fn(usize, State) -> StateIter + 'static {
    type Item = StateIter;
    fn next(&mut self) -> Option<StateIter> {
        if self.pos == self.len {
            return None;
        }
        let state = State::with_parent(self.state.clone());
        let ret = Some((self.f)(self.pos, state));
        self.pos += 1;
        ret
    }
}

impl<F> IterBuilder<F>
where F: Fn(usize, State) -> StateIter + 'static {
    pub fn new(f: F, len: usize) -> IterBuilder<F> {
        IterBuilder { f: f, len: len }
    }

    pub fn conde(self, state: State) -> StateIter {
        if !state.ok() { return TailIterResult(None, None); }
        let chain = VecDeque::with_capacity(self.len);
        let iter = StateFnIter { f: self.f, state: Rc::new(state), len: self.len, pos: 0 };
        TailIterResult(None, Some(Box::new(ChainManyIter { iter: Some(Box::new(iter)), chain: chain })))
    }

    pub fn conda(self, state: State) -> StateIter {
        self.condau(state, true)
    }

    pub fn condu(self, state: State) -> StateIter {
        self.condau(state, false)
    }

    fn condau(self, state: State, return_more: bool) -> StateIter {
        if !state.ok() { return TailIterResult(None, None); }
        let iter = StateFnIter { f: self.f, state: Rc::new(state), len: self.len, pos: 0 };
        TailIterResult(None, Some(Box::new(CondaIter { iter: Box::new(iter), return_more: return_more })))
    }
}

pub type WrappedStateIter = Box<Fn(State) -> TailIterResult + 'static>;

///! Constructs iterators over alternate solutions.  You don't need to use this directly; instead,
///! use the conde! macro.
pub struct IterBuilder<F>
where F: Fn(usize, State) -> StateIter + 'static {
    f: F,
    len: usize,
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
        self.iter.next().map(|x| x.get_value(self.var).map(|val| val.clone()))
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
        self.iter.next()
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
