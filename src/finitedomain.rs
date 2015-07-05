use finitedomain::Fd::*;
use std::collections::HashSet;
use core::{VarWrapper, StateProxy, Var, ToVar, VarStore, VarRetrieve, State, Unifier, UnifyResult};
use iter::{StateIter, single};
use tailiter::TailIterItem::*;
use tailiter::{TailIterItem, TailIterator, TailIterHolder};
use std::rc::Rc;

///! Represents a finite-domain value.  By storing a set of possible values from that domain, these
///! can be more performant than backtracking for each value.
#[derive(Debug, Clone)]
pub enum Fd {
    Values(Vec<usize>),
    Single(usize),
}

impl ToVar for Fd {
    default_tovar_impl!(Fd);
}

impl PartialEq for Fd {
    fn eq(&self, other: &Fd) -> bool {
        if let (Some(l), Some(r)) = (self.single_value(), other.single_value()) {
            l == r
        } else if let (&Values(ref l), &Values(ref r)) = (self, other) {
            l == r
        } else {
            false
        }
    }
}

fn combine_single(values: &[usize], value: usize) -> Fd {
    match values.binary_search(&value) {
        Ok(..) => Fd::Single(value),
        Err(..) => Fd::err(),
    }
}

impl Fd {
    pub fn new_values(values: Vec<usize>) -> Fd {
        {
            values.iter().fold(None, |a, b| {
                if let Some(a) = a { assert!(a < b); }
                Some(b)
            });
        }
        Fd::Values(values)
    }

    pub fn new_single(value: usize) -> Fd {
        Fd::Single(value)
    }

    pub fn err() -> Fd {
        Fd::Values(Vec::new())
    }

    pub fn is_valid(&self) -> bool {
        match *self {
            Fd::Values(ref values) => !values.is_empty(),
            Fd::Single(..) => true,
        }
    }

    pub fn combine(&self, other: &Fd) -> Fd {
        //println!("combining {:?} and {:?}", self, other);
        let result = match (self, other) {
            (&Single(lval), &Single(rval)) => match lval == rval {
                true => Single(lval),
                false => Values(Vec::new()),
            },
            (&Single(lval), &Values(ref rvals)) => combine_single(rvals, lval),
            (&Values(ref rvals), &Single(lval)) => combine_single(rvals, lval),
            (&Values(ref lvals), &Values(ref rvals)) => {
                let combined = RangeMerge::new(lvals.iter().map(|x| *x), rvals.iter().map(|x| *x));
                Values(combined.collect())
            },
        };
        //println!("got {:?}", result);
        result
    }
    pub fn single_value(&self) -> Option<usize> {
        match *self {
            Fd::Values(ref values) if values.len() == 1 => Some(values[0]),
            Fd::Single(x) => Some(x),
            _ => None,
        }
    }
    pub fn in_range(&self, val: usize) -> bool {
        match *self {
            Fd::Values(ref values) => { values.binary_search(&val).is_ok() },
            Fd::Single(x) => x == val,
        }
    }

    pub fn remove_values(&mut self, val: &HashSet<usize>) {
        match *self {
            Fd::Values(ref mut values) => {
                //println!("removing from {:?}", values);
                values.retain(|x| !val.contains(x));
            },
            Fd::Single(x) => {
                if val.contains(&x) {
                    *self = Fd::err();
                }
            }
        }
    }
}


impl VarWrapper for Fd {
    fn unify_with(&self, other: &VarWrapper, _: &mut StateProxy) -> UnifyResult {
        let other = other.get_wrapped_value::<Fd>();
        if let (Some(x), Some(y)) = (self.single_value(), other.single_value()) {
            return (x == y).into();
        }
        if self == other {
            return true.into();
        }
        let result = self.combine(other);
        if !result.is_valid() { return false.into(); }

        unsafe { return UnifyResult::overwrite(result); }
    }
    fn value_count(&self) -> usize {
        match *self {
            Single(_) => 1,
            Values(ref x) => x.len(),
        }
    }
    fn value_iter(&self) -> Box<Iterator<Item=Box<VarWrapper>>> {
        match *self {
            Single(_) => panic!(),
            Values(ref x) => {
                let fds: Vec<Box<VarWrapper>> = x.iter().map(|&val| {
                    Box::new(Fd::new_single(val)) as Box<VarWrapper>
                }).collect();
                Box::new(fds.into_iter())
            }
        }
    }
    fn uses_overwrite(&self) -> bool { true }
}



struct RangeMerge<A, B, C> where A: Iterator<Item=C>, B: Iterator<Item=C>, C: PartialOrd + PartialEq {
    a: A,
    b: B,
}

macro_rules! try_opt {
    ($x:expr) => {
        match $x {
            Some(x) => x,
            None => return None,
        }
    }
}

impl<A, B, C> Iterator for RangeMerge<A, B, C> where A: Iterator<Item=C>, B: Iterator<Item=C>, C: PartialOrd + PartialEq {
    type Item=C;
    fn next(&mut self) -> Option<C> {
        let mut a = try_opt!(self.a.next());
        let mut b = try_opt!(self.b.next());
        loop {
            if a == b {
                return Some(a);
            } else if a < b {
                a = try_opt!(self.a.next());
            } else {
                b = try_opt!(self.b.next());
            }
        }
    }
}

impl<A, B, C> RangeMerge<A, B, C> where A: Iterator<Item=C>, B: Iterator<Item=C>, C: PartialOrd + PartialEq {
    fn new<D, E>(a: D, b: E) -> RangeMerge<A, B, C> where D: IntoIterator<IntoIter=A, Item=C>, E: IntoIterator<IntoIter=B, Item=C> {
        RangeMerge { a: a.into_iter(), b: b.into_iter() }
    }
}

pub fn fd_values<A, B>(mut state: State, fd: A, u: B) -> StateIter
where A: ToVar<VarType=Fd>, B: ToVar<VarType=usize> {
    let fd = state.make_var_of(fd);
    let u = state.make_var_of(u);
    match state.get_value(fd).map(|x| x.clone()) {
        Some(Single(x)) => {
            state.unify(x, u);
            single(state)
        },
        None => { single(state) },
        Some(Values(values)) => {
            let valiter = values.into_iter();
            TailIterHolder::new(
                FdValueIter { state: Some(Rc::new(state)), fd: fd, vals: valiter, u: u })
        }
    }
}

struct FdValueIter {
    state: Option<Rc<State>>,
    fd: Var<Fd>,
    vals: ::std::vec::IntoIter<usize>,
    u: Var<usize>,
}

impl TailIterator for FdValueIter {
    type Item = State;
    fn next_inner(&mut self) -> TailIterItem<State> {
        while let Some(x) = self.vals.next() {
            let mut child = State::with_parent(self.state.clone().unwrap());
            //println!("fdvalueiter: unifying {} with {:?} and {:?}, {} remain",
                     //x, child.get_value(self.fd), child.get_value(self.u), self.vals.len());
            child.unify(x, self.u);
            child.unify(Single(x), self.fd);
            if child.ok() { return SingleItem(child); }
        }
        return Done;
    }
}
