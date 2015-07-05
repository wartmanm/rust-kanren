use std::iter::IntoIterator;
use std::fmt::{Debug, Formatter};
use std::any::Any;
use core::{ToVar, VarWrapper, State, StateProxy, Var, VarStore, VarRetrieve, Unifier, UnifyResult};
pub use list::List::Nil; // so you can import list::{Pair, Nil}
use list::List::Pair as VarPair;

///! A singly-linked List.
pub enum List<A>
where A: ToVar {
    Pair(Var<A>, Var<List<A>>),
    Nil
}

#[derive(Debug)]
pub struct Pair<A, B, C>(pub B, pub C)
where A: ToVar, B: ToVar<VarType=A>, C: ToVar<VarType=List<A>>;

impl<A, B, C> Clone for Pair<A, B, C>
where A: ToVar, B: ToVar<VarType=A> + Clone, C: ToVar<VarType=List<A>> + Clone {
    fn clone(&self) -> Pair<A, B, C> { Pair(self.0.clone(), self.1.clone()) }
}
impl<A, B, C> Copy for Pair<A, B, C>
where A: ToVar, B: ToVar<VarType=A> + Copy, C: ToVar<VarType=List<A>> + Copy { }

impl<A, B, C> ToVar for Pair<A, B, C>
where A: ToVar, B: ToVar<VarType=A>, C: ToVar<VarType=List<A>> {
    type VarType = List<A>;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<List<A>> {
        let a = state.make_var_of(self.0);
        let b = state.make_var_of(self.1);
        state.store_value(VarPair(a, b))
    }
}

impl<A> Clone for List<A> where A: ToVar { fn clone(&self) -> List<A> { *self } }
impl<A> Copy for List<A> where A: ToVar { }

impl<A> VarWrapper for List<A>
where A : ToVar {
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
}

impl<A> List<A>
where A : ToVar {
    ///! Create a `List` from an `IntoIterator`.
    pub fn new_from_iter<B, U>(state: &mut U, intoiter: B) -> Var<List<<A as ToVar>::VarType>>
    where B : IntoIterator<Item=A>, U: VarStore + Unifier {

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

    ///! Helper method to return a `VarPair` from two values, which need not have been made into
    ///! variables.
    pub fn pair<T, Head, Tail>(state: &mut State, head: Head, tail: Tail) -> Var<List<A>>
    where Head: ToVar<VarType=A>, Tail: ToVar<VarType=List<A>> {
        let head = state.make_var_of(head);
        let tail = state.make_var_of(tail);
        let pair = VarPair(head, tail);
        state.make_var_of(pair)
    }

    pub fn build<I>(iter: I) -> ListBuilder<A, <I as IntoIterator>::IntoIter>
    where I: IntoIterator<Item=A>, <I as IntoIterator>::IntoIter: 'static {
        ListBuilder::new(iter)
    }
}

impl<A> Debug for List<A>
where A : ToVar {
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

impl<A, B> ToVar for ListBuilder<A, B> where A: ToVar, B: Iterator<Item=A> + Any {
    type VarType = List<<A as ToVar>::VarType>;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<List<<A as ToVar>::VarType>> {
        List::new_from_iter(state, self.iter)
    }
}

///! Iterator over the `(Head, Tail)` variable pairs in a `List`.
pub struct VarIterator<'a, A, B>
where A : ToVar, B : VarRetrieve + 'a {
    list: List<A>,
    state: &'a B,
}

impl<'a, 'b, A, B> Iterator for VarIterator<'a, A, B>
where A : ToVar, B : VarRetrieve + 'a {
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
where A : ToVar, B : VarRetrieve + 'a {
    list: List<A>,
    state: &'a B,
}

impl<'a, A, B> Iterator for ListIterator<'a, A, B>
where A : ToVar, B: VarRetrieve {
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

impl<A> ToVar for List<A> where A : ToVar {
    type VarType = List<A>;
    fn into_var<U: VarStore>(self, state: &mut U) -> Var<List<A>> {
        state.store_value(self)
    }
}
