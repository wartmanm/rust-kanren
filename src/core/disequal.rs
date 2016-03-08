use std::any::TypeId;
use std::fmt::{self, Debug, Formatter};
use core::{ConstraintResult, StateProxy, UntypedVar, Constraint, State, Var, ToVar, FollowRef, Unifier, VarMap, VarWrapper};
use core::ConstraintResult::*;
use core::VarRef::*;

///! The Disequal constraint enforces that its arguments will never have equal values.  Don't use
///! this directly, use `kanren::constraints::Disequal` instead.
#[derive(Clone)]
pub struct Disequal {
    pairs: Vec<(UntypedVar, UntypedVar, TypeId)>,
}

impl Debug for Disequal {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        try!(write!(fmt, "Disequal ["));
        let mut pairs = self.pairs.iter().peekable();
        while let Some(&(a, b, _)) = pairs.next() {
            try!(write!(fmt, "{:?} != {:?}", a, b));
            if pairs.peek().is_some() { try!(write!(fmt, ", ")); }
        }
        write!(fmt, "]")
    }
}

impl Disequal {
    pub fn new_empty() -> Disequal {
        Disequal { pairs: Vec::new() }
    }
    pub fn push<A>(&mut self, state: &State, a: Var<A>, b: Var<A>) where A: ToVar + VarWrapper {
        let a = state.follow_id(a.var);
        let b = state.follow_id(b.var);
        self.pairs.push((a, b, TypeId::of::<A>()));
    }

    fn disequal_update_vars(&self, state: &State) -> ConstraintResult<Disequal> {
        let needs_update = self.pairs.iter().any(|&(a, b, _)| {
            if let Some(&EqualTo(..)) = state.eqs.get(&a) {
                true
            } else if let Some(&EqualTo(..)) = state.eqs.get(&b) {
                true
            } else {
                false
            }
        });
        if needs_update {
            //println!("updating vars for {:?}", self);
            let pairs = self.pairs.iter().map(|&(olda, oldb, ty)| {
                let a = match state.eqs.get(&olda) {
                    Some(&EqualTo(x)) => x,
                    _ => olda,
                };
                let b = match state.eqs.get(&oldb) {
                    Some(&EqualTo(x)) => x,
                    _ => oldb,
                };
                //println!("replacing {:?} != {:?} with {:?} != {:?}", olda, oldb, a, b);
                (a, b, ty)
            });
            Updated(Disequal { pairs: pairs.collect() })
        } else {
            Unchanged
        }
    }
    fn relevant(&self, var: UntypedVar) -> bool {
        let ret = self.pairs.iter().any(|&(a, b, _)| a == var || b == var);
        //println!("{:?} relevant to {:?}: {}", var, self, ret);
        ret
    }
    fn perform_test(&self, proxy: &mut StateProxy) -> ConstraintResult<Disequal> {
        //println!("updating {:?}", self);
        for &(a, b, ty) in self.pairs.iter() {
            proxy.untyped_unify(a, b, ty, true);
            if !proxy.ok() {
                //println!("failed unification, disequality constraint satisfied");
                return Irrelevant;
            }
        }
        if proxy.parent.proxy_eqs.is_empty() {
            //println!("succeeded unification with no additions, disequality constraint failed");
            return Failed;
        }

        let mut all_unchanged = true;
        let mut updated = Disequal::new_empty();
        for &(k, _) in proxy.parent.proxy_eqs.iter() {
            let eqvar = match proxy.get_ref(k) {
                // We don't care about values added by overwrite() -- they indicate that something
                // had to be updated (so it passes) but the value will be gone when we roll back
                &Exactly(..) => { continue; },
                &EqualTo(eqvar) => eqvar,
            };

            if all_unchanged && self.relevant(k) {
                continue;
            }
            all_unchanged = false;
            let newtype = proxy.follow_ref(eqvar).2;
            updated.pairs.push((k, eqvar, newtype));
        }
        if all_unchanged {
            //println!("returning disequal {:?} unchanged", self);
            return self.disequal_update_vars(proxy.parent)
        }

        //println!("returning updated disequal {:?}", updated);
        return Updated(updated);
    }
}

impl Constraint for Disequal {
    fn update(&self, proxy: &mut StateProxy) -> ConstraintResult<Disequal> {
        let result = self.perform_test(proxy);
        proxy.parent.proxy_eqs.clear();
        proxy.parent.proxy_eqs.ok = proxy.parent.eqs.ok;
        result
    }

    fn relevant(&self, proxy: &VarMap) -> bool {
        self.pairs.iter().any(|&(ref a, ref b, _)| proxy.contains_key(a) || proxy.contains_key(b))
    }
    fn update_vars(&mut self, proxy: &State) {
        for &mut (ref mut a, ref mut b, _) in self.pairs.iter_mut() {
            proxy.update_var(a);
            proxy.update_var(b);
        }
    }
}


