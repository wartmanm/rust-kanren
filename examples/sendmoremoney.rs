#[macro_use]
extern crate kanren;

use kanren::core::{State, Unifier, Var, VarStore, VarRetrieve};
use kanren::core::assign_all_values;
use kanren::iter::{StateIter, single};
use std::io::Read;
use kanren::constraints::{FdSumConstraint, AllDiffConstraint};
use kanren::finitedomain::Fd;

fn main() {
    fn sumcol(mut state: State, l: Var<Fd>, r: Var<Fd>, sum: Var<Fd>, oldcarry: Var<Fd>, carry: Var<Fd>) -> StateIter {
        fresh!(state, tmp_sum, tmp_sum_carry, carry_ten);
        // L + R = tmp_sum
        state.add_constraint(FdSumConstraint::new(l, r, tmp_sum));
        // L + R + oldcarry = tmp_sum_carry
        state.add_constraint(FdSumConstraint::new(tmp_sum, oldcarry, tmp_sum_carry));
        // sum + [ 10 | 0 ] = tmp_sum_carry
        state.add_constraint(FdSumConstraint::new(sum, carry_ten, tmp_sum_carry));
        conde!(state, {
            //println!("trying to carry 1");
            state.unify(carry_ten, Fd::new_single(10));
            state.unify(carry, Fd::new_single(1));
            state
        }, {
            //println!("trying to carry 0");
            state.unify(carry_ten, Fd::new_single(0));
            state.unify(carry, Fd::new_single(0));
            state
        })
    }

    let mut state = State::new();
    fresh!(state, s, e, n, d, m, o, r, y);
    fresh!(state, carry_1, carry_2, carry_3, carry_4);
    let zero = state.make_var_of(Fd::new_single(0));

    state.add_constraint(AllDiffConstraint::new(vec![s, e, n, d, m, o, r, y]));
    // leading digits must be nonzero
    state.unify(s, Fd::new_values((1..10).collect()));
    state.unify(m, Fd::new_values((1..10).collect()));
    for &var in [e, n, d, o, r, y].iter() {
        state.unify(var, Fd::new_values((0..10).collect()));
    }

    //   0     c_1     c_2     c_3     c_4     0
    //              s       e       n       d
    //              m       o       r       e
    //      m       o       n       e       y 
    let iter = single(state)
        .and(move |state| sumcol(state, zero, zero, m, carry_1, zero))
        .and(move |state| sumcol(state, s, m, o, carry_2, carry_1))
        .and(move |state| sumcol(state, e, o, n, carry_3, carry_2))
        .and(move |state| sumcol(state, n, r, e, carry_4, carry_3))
        .and(move |state| sumcol(state, d, e, y, zero, carry_4))
        .and(assign_all_values);

    //let reifyfds = [s, e, n, d, m, o, r, e, y].iter().fold(iter, move |iter, &fdvar| {
        //iter.and(move |mut state| {
            //state.unify(fdvar, Fd::new_values((0..10).collect()));
            //finitedomain::fd_values(state, fdvar, __())
        //})
    //});

    for (i, state) in iter.into_iter().enumerate().take(100) {
        let getfd = |var: Var<Fd>| { state.get_value(var).unwrap().single_value().unwrap() };
        println!("solution {}:", i);
        println!("  {}{}{}{}\n+ {}{}{}{}\n______\n {}{}{}{}{}",
                      getfd(s), getfd(e), getfd(n), getfd(d),
                      getfd(m), getfd(o), getfd(r), getfd(e),
            getfd(m), getfd(o), getfd(n), getfd(e), getfd(y),
            );
    }
}
