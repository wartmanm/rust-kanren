use core::{ToVar, State, Var, VarStore, VarRetrieve, Unifier};
use iter::{single, none, StateIter};
use list::List;
use list::List::Nil;

///! Assert that a list has a particular value at a particular index.  The list, value, and index
///! can all be unset.
pub fn index<A, TVar, TList, TIdx>(mut state: State, var: TVar, listvar: TList, idxvar: TIdx) -> StateIter
where A : ToVar, TVar: ToVar<VarType=A>, TList: ToVar<VarType=List<A>> + Copy, TIdx: ToVar<VarType=i32> + Copy {
    let var = state.make_var_of(var);
    let idxvar = state.make_var_of(idxvar);
    let listvar = state.make_var_of(listvar);
    fn index_inner<A>(state: State, var: Var<A>, listvar: Var<List<A>>, idxvar: Var<i32>, idx: i32) -> StateIter where A: ToVar {
        conde!(state, {
            let tailvar = state.make_var();
            state.unify(idxvar, idx);
            state.unify(listvar, List::Pair(var, tailvar));
            single(state)
        }, {
            match state.get_value(idxvar) {
                Some(x) if *x <= idx => { return none(); }
                _ => { }
            }
            fresh!(state, headvar, tailvar);
            state.unify(listvar, List::Pair(headvar, tailvar));
            index_inner(state, var, tailvar, idxvar, idx + 1)
        })
    }
    index_inner(state, var, listvar, idxvar, 0)
}

///! Assert that a list has a particular value somewhere.  The list and value can both be unset.
pub fn contains<A, TVar, TList>(mut state: State, var: TVar, list: TList) -> StateIter
where A : ToVar, TVar: ToVar<VarType=A>, TList: ToVar<VarType=List<A>> + Copy {
    let ignore = state.make_var();
    let var = state.make_var_of(var);
    index(state, var, list, ignore)
}

///! Assert that a list is of a given length.  The list and length can both be unset.
pub fn length<A, TList, TLen>(mut state: State, list: TList, lenvar: TLen) -> StateIter
where A : ToVar, TList: ToVar<VarType=List<A>>, TLen: ToVar<VarType=i32> {
    let list = state.make_var_of(list);
    let lenvar = state.make_var_of(lenvar);
    fn length_inner<'a, A>(state: State, list: Var<List<A>>, lenvar: Var<i32>, len: i32) -> StateIter
    where A : ToVar {
        conde!(state, {
            state.unify(list, Nil);
            state.unify(len, lenvar);
            single(state)
        }, {
            let lenvar = state.make_var_of(lenvar);
            match state.get_value(lenvar) {
                Some(x) if *x <= len => { return none(); }
                _ => { }
            }
            fresh!(state, headvar, tailvar);
            state.unify(List::Pair(headvar, tailvar), list);
            length_inner(state, tailvar, lenvar, len + 1)
        })
    }
    length_inner(state, list, lenvar, 0)
}
