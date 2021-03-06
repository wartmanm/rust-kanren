use std::iter::IntoIterator;
use std::fmt::{Debug, Formatter};
use std::any::{Any, TypeId};
use core::{ToVar, VarWrapper, State, StateProxy, Var, VarStore, VarRetrieve, Unifier, UnifyResult, UntypedVar, TypedVar, TypeList};
///! The end of a singly linked list.
pub use list::List::Nil; // so you can import list::{Pair, Nil}
use list::List::Pair as VarPair;

///! A singly-linked List.
pub enum List<A>
where A: VarWrapper {
    Pair(Var<A>, Var<List<A>>),
    Nil
}

///! A struct that can be converted into a (Head, Tail) pair in a singly linked list.
#[derive(Debug)]
pub struct Pair<A, B, C>(pub B, pub C)
where A: VarWrapper, B: ToVar<VarType=A>, C: ToVar<VarType=List<A>>;

impl<A, B, C> Clone for Pair<A, B, C>
where A: VarWrapper, B: ToVar<VarType=A> + Clone, C: ToVar<VarType=List<A>> + Clone {
    fn clone(&self) -> Pair<A, B, C> { Pair(self.0.clone(), self.1.clone()) }
}
impl<A, B, C> Copy for Pair<A, B, C>
where A: VarWrapper, B: ToVar<VarType=A> + Copy, C: ToVar<VarType=List<A>> + Copy { }

impl<A, B, C> ToVar for Pair<A, B, C>
where A: VarWrapper, B: ToVar<VarType=A>, C: ToVar<VarType=List<A>> {
    type VarType = List<A>;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<List<A>> {
        let a = state.make_var_of(self.0);
        let b = state.make_var_of(self.1);
        state.store_value(VarPair(a, b))
    }
}

impl<A> Clone for List<A> where A: VarWrapper { fn clone(&self) -> List<A> { *self } }
impl<A> Copy for List<A> where A: VarWrapper { }

impl<A> VarWrapper for List<A>
where A : VarWrapper {
    fn unify_with(&self, other: &VarWrapper, ctxt: &mut StateProxy) -> UnifyResult {
        let mut a = *self;
        let mut b = *other.get_wrapped_value();
        loop {
            match (a, b) {
                (Nil, Nil) => { return true.into(); }
                (VarPair(h1, t1), VarPair(h2, t2)) => {
                    //println!("unifying List...");
                    if !ctxt.unify_vars(h1, h2).ok() {
                        return false.into();
                    }
                    if let (Some(t1val), Some(t2val)) = (ctxt.get_value(t1), ctxt.get_value(t2)) {
                        a = *t1val;
                        b = *t2val;
                        continue;
                    }
                    return ctxt.unify_vars(t1, t2).ok().into();
                },
                _ => { return false.into(); }
            }
        }
    }
    fn var_iter<'a>(&'a self) -> Option<Box<Iterator<Item=UntypedVar> + 'a>> {
        match self {
            &VarPair(h, t) => {
                Some(Box::new(PairIter { p: [h.untyped(), t.untyped()], pos: 0 }))
            },
            &Nil => None,
        }
    }
    fn can_contain_type(t: &TypeList, other: TypeId) -> bool {
        if TypeId::of::<Self>() == other { return true; }
        if t.contains_type(TypeId::of::<Self>()) { return false; }
        let new_t = TypeList::Pair(TypeId::of::<Self>(), t);
        A::can_contain_type(&new_t, other)
    }
    fn occurs_check(&self, state: &StateProxy, other: TypedVar) -> bool {
        let mut list = self;
        let check_heads = A::can_contain_type(&TypeList::Nil, other.type_id());
        loop {
            match list {
                &Nil => { return false },
                &VarPair(a, b) => {
                    if check_heads && state.occurs_check(other, a.untyped()) { return true; }
                    let b = state.get_updated_var(b.untyped());
                    if b == other.untyped() { return true; }
                    match state.get_untyped(b) {
                        Some(tail) => { list = tail.get_wrapped_value(); }
                        None => { return false; }
                    }
                }
            }
        }
    }
}

struct PairIter {
    p: [UntypedVar; 2],
    pos: u8,
}

impl Iterator for PairIter {
    type Item = UntypedVar;
    fn next(&mut self) -> Option<UntypedVar> {
        let item = self.p.get(self.pos as usize).map(|x| *x);
        self.pos += 1;
        item
        //let item = match (self.pos, self.p) {
            //0, &Pair(h, _) => Some(h.untyped()),
            //1, &Pair(_, t) => Some(t.untyped()),
            //_ => None,
        //};
    }
}

impl<A> List<A>
where A : VarWrapper {
    ///! Create a `List` from an `IntoIterator`.
    pub fn new_from_iter<B, C, U>(state: &mut U, intoiter: B) -> Var<List<A>>
    where B : IntoIterator<Item=C>, C: ToVar<VarType=A>, U: VarStore + Unifier {

        let iter = intoiter.into_iter();
        let liststart = state.make_var();
        let mut curlistvar = liststart;
        for item in iter {
            let head = state.make_var_of(item);
            let tail = state.make_var();
            let pair = VarPair(head, tail);
            state.unify(pair, curlistvar);
            curlistvar = tail;
        }
        let nilvar = state.make_var_of(Nil);
        state.unify_vars(curlistvar, nilvar);
        liststart
    }

    ///! Return an iterator over the values in this `List`.
    pub fn iter<C>(self, state: &C) -> ListIterator<A, C>
    where C : VarRetrieve {
        ListIterator { list: self, state: state }
    }

    ///! Return an iterator over the `(Head, Tail)` variable pairs in this `List`.
    pub fn var_iter<C>(self, state: &C) -> VarIterator<A, C>
    where C : VarRetrieve {
        VarIterator { list: self, state: state }
    }

    /////! Helper method to return a `VarPair` from two values, which need not have been made into
    /////! variables.
    //pub fn pair<T, Head, Tail>(state: &mut State, head: Head, tail: Tail) -> Var<List<A>>
    //where Head: ToVar<VarType=A>, Tail: ToVar<VarType=List<A>> {
        //let head = state.make_var_of(head);
        //let tail = state.make_var_of(tail);
        //let pair = VarPair(head, tail);
        //state.make_var_of(pair)
    //}

    ///! Create a new list from an iterator.
    pub fn build<B, I>(iter: I) -> ListBuilder<B, <I as IntoIterator>::IntoIter>
    where B: ToVar<VarType=A>, I: IntoIterator<Item=B>, <I as IntoIterator>::IntoIter: 'static {
        ListBuilder::new(iter)
    }
}

trait ListExt<A> where A: VarWrapper {
    fn check_elem<B>(&self, state: &mut State, elem: B) -> bool where B: ToVar<VarType=A>;
}

impl<A> ListExt<A> for List<A> where A: VarWrapper {
    fn check_elem<B>(&self, state: &mut State, elem: B) -> bool where B: ToVar<VarType=A> {
        let elem = state.make_var_of(elem);
        let mut pair = Some(*self);
        // TODO: make it possible to use var_iter() instead
        while let Some(VarPair(head, tail)) = pair {
            if state.are_vars_unified(head, elem) == ::core::Unifiability::AlreadyDone {
                return true;
            }
            pair = state.get_value(tail).map(|x| *x);
        }
        return false;
    }
}

impl<A> ListExt<A> for Var<List<A>> where A: VarWrapper {
    fn check_elem<B>(&self, state: &mut State, elem: B) -> bool where B: ToVar<VarType=A> {
        let list = state.get_value(*self).map(|&x| x).unwrap_or(Nil);
        list.check_elem(state, elem)
    }
}

impl<A> Debug for List<A>
where A : VarWrapper {
    fn fmt(&self, fmt: &mut Formatter) -> ::std::fmt::Result {
        match self {
            &VarPair(ref head, ref tail) => write!(fmt, "VarPair({:?}, {:?})", head, tail),
            &Nil => write!(fmt, "Nil"),
        }
    }
}

impl<A, B> Debug for ListBuilder<A, B> where A: ToVar, B: Iterator<Item=A> {
    fn fmt(&self, fmt: &mut Formatter) -> ::std::fmt::Result {
        write!(fmt, "ListBuilder {{ ... }}")
    }
}

pub struct ListBuilder<A, B> where A: ToVar, B: Iterator<Item=A> {
    iter: B,
}

impl<A, B> ListBuilder<A, B> where A: ToVar, B: Iterator<Item=A> {
    pub fn new<C>(intoiter: C) -> ListBuilder<A, B> where C: IntoIterator<IntoIter=B, Item=A> {
        ListBuilder { iter: intoiter.into_iter() }
    }
}

///! Helper to create a `List` from an `Iterator`, used by `List::build()`.
impl<A, B> ToVar for ListBuilder<A, B> where A: ToVar, B: Iterator<Item=A> + Any {
    type VarType = List<<A as ToVar>::VarType>;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<List<<A as ToVar>::VarType>> {
        List::new_from_iter(state, self.iter)
    }
}

///! Iterator over the `(Head, Tail)` variable pairs in a `List`.
pub struct VarIterator<'a, A, B>
where A : VarWrapper, B : VarRetrieve + 'a {
    list: List<A>,
    state: &'a B,
}

impl<'a, 'b, A, B> Iterator for VarIterator<'a, A, B>
where A : VarWrapper, B : VarRetrieve + 'a {
    type Item = (Var<A>, Var<List<A>>);
    fn next(&mut self) -> Option<(Var<A>, Var<List<A>>)> {
        match self.list {
            Nil => { return None; }
            VarPair(headid, tailid) => {
                let tail = self.state.get_value(tailid).map(|x| *x).unwrap_or(Nil);
                self.list = tail;
                Some((headid, tailid))
            },
        }
    }
}

///! Iterator over values in a `List`.
pub struct ListIterator<'a, A, B>
where A : VarWrapper, B : VarRetrieve + 'a {
    list: List<A>,
    state: &'a B,
}

impl<'a, A, B> Iterator for ListIterator<'a, A, B>
where A : VarWrapper, B: VarRetrieve {
    type Item = Option<&'a A>;
    fn next(&mut self) -> Option<Option<&'a A>> {
        let (headid, tailid) = match self.list {
            Nil => { return None; }
            VarPair(head, tail) => (head, tail)
        };
        let tail = self.state.get_value(tailid).map(|x| *x).unwrap_or(Nil);
        self.list = tail;
        Some(self.state.get_value(headid))
    }
}

impl<A> ToVar for List<A> where A : VarWrapper {
    type VarType = List<A>;
    fn into_var<U: VarStore>(self, state: &mut U) -> Var<List<A>> {
        state.store_value(self)
    }
}
