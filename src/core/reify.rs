use std::collections::HashMap;
use std::collections::hash_map::Entry::*;
use core::{State, UntypedVar, Var, FollowRef, VarWrapper};
use std::fmt::{self, Debug, Display};

///! Reifies variables, providing a consistent, unique identifier for unset variables.  For
///! compatibility, it starts counting from _0 rather than using the variable's underlying usize.
pub struct Reifier<'a> {
    eqs: HashMap<UntypedVar, i32>,
    id: i32,
    parent: &'a State,
}

pub enum Reified<'a, A> where A: 'a {
    Value(&'a A),
    Unset(i32),
}

impl<'a, A> Debug for Reified<'a, A> where A: 'a + Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Reified::Value(ref x) => write!(f, "{:?}", x),
            Reified::Unset(ref x) => write!(f, "_{}", x),
        }
    }
}

impl<'a, A> Display for Reified<'a, A> where A: 'a + Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Reified::Value(ref x) => write!(f, "{}", x),
            Reified::Unset(ref x) => write!(f, "_{}", x),
        }
    }
}

impl<'a> Reifier<'a> {
    pub fn new(parent: &'a State) -> Reifier<'a> {
        Reifier { eqs: HashMap::new(), id: 0, parent: parent }
    }

    pub fn reify<A: VarWrapper>(&mut self, var: Var<A>) -> Reified<'a, A> {
        let (walked, value, _) = self.parent.follow_ref(var.var);
        match value {
            Some(x) => Reified::Value(x.get_wrapped_value()),
            None => {
                match self.eqs.entry(walked) {
                    Occupied(x) => Reified::Unset(*x.get()),
                    Vacant(x) => {
                        let id = self.id;
                        self.id += 1;
                        x.insert(id);
                        Reified::Unset(id)
                    }
                }
            }
        }
    }
}

