//! Miscellaneous implementations from chapter 8 of The Reasoned Schemer.

#[macro_use]
extern crate kanren;

use kanren::core::{State, Var, ToVar, VarStore, Unifier};
use kanren::core::vars::__;
use kanren::core::reify::{Reifier, Reified};
use kanren::list::List;
use kanren::list::{Pair, Nil};
use kanren::iter::{StateIter, single};

use std::fmt::Write;

use Bit::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bit {
    Zero,
    One,
}
value_wrapper!(Bit);

fn bit_and(state: State, x: Var<Bit>, y: Var<Bit>, r: Var<Bit>) -> StateIter {
    conde!(state, {
        state.unify(x, Zero).unify(y, Zero).unify(r, Zero);
        state
    }, {
        state.unify(x, Zero).unify(y, One).unify(r, Zero);
        state
    }, {
        state.unify(x, One).unify(y, Zero).unify(r, Zero);
        state
    }, {
        state.unify(x, One).unify(y, One).unify(r, One);
        state
    })
}

fn bit_xor(state: State, x: Var<Bit>, y: Var<Bit>, r: Var<Bit>) -> StateIter {
    conde!(state, {
        state.unify(x, Zero).unify(y, Zero).unify(r, Zero);
        state
    }, {
        state.unify(x, Zero).unify(y, One).unify(r, One);
        state
    }, {
        state.unify(x, One).unify(y, Zero).unify(r, One);
        state
    }, {
        state.unify(x, One).unify(y, One).unify(r, Zero);
        state
    })
}

//method!(asdf(state, { args= } { vars=x: Bit, y: Bit, r: Bit, c: Bit }) {
    //bit_xor(state, x, y, r).and(move |state| bit_and(state, x, y, c))
//});


method!(half_adder(state, x: Bit, y: Bit, r: Bit, c: Bit) {
    bit_xor(state, x, y, r).and(move |state| bit_and(state, x, y, c))
});

method!(full_adder(state, b: Bit, x: Bit, y: Bit, r: Bit, c: Bit) {
    fresh!(state, w, xy, wz);
    half_adder(state, x, y, w, xy)
        .and(move |state| half_adder(state, w, b, r, wz))
        .and(move |state| bit_xor(state, xy, wz, c))
});

#[derive(Clone, Copy)]
struct NumBuilder(usize);

impl Iterator for NumBuilder {
    type Item = Bit;
    fn next(&mut self) -> Option<Bit> {
        match self.0 {
            0 => None,
            x => {
                let lowest = x & 1;
                *self = NumBuilder(x >> 1);
                Some(if lowest == 1 { One } else { Zero })
            }
        }
    }
}

fn build_num(state: &mut State, num: usize) -> Var<List<Bit>> {
    let mut bits: Vec<Bit> = NumBuilder(num).collect();
    bits.reverse();
    List::new_from_iter(state, bits.into_iter())
}

fn pos(state: &mut State, n: Var<List<Bit>>) {
    fresh!(state, a, d);
    state.unify(Pair(a, d), n);
}

fn over_one(state: &mut State, n: Var<List<Bit>>) {
    fresh!(state, a, t1, ad, dd);
    state.unify(n, Pair(a, t1));
    state.unify(t1, Pair(ad, dd));
}

fn adder<D, N, M, R>(mut state: State, d: D, n: N, m: M, r: R) -> StateIter
where D: ToVar<VarType=Bit>, N: ToVar<VarType=List<Bit>>, M: ToVar<VarType=List<Bit>>, R: ToVar<VarType=List<Bit>> {
    let d = state.make_var_of(d);
    let n = state.make_var_of(n);
    let m = state.make_var_of(m);
    let r = state.make_var_of(r);
    conde!(state, {
        state.unify(Zero, d).unify(Nil, m).unify(n,r);
        state
    }, {
        state.unify(Zero, d).unify(Nil, n).unify(m,r);
        pos(&mut state, m);
        state
    }, {
        state.unify(One, d).unify(Nil, m);
        adder(state, Zero, n, [One], r)
    }, {
        state.unify(One, d).unify(Nil, m);
        pos(&mut state, m);
        adder(state, Zero, [One], m, r)
    }, {
        state.unify([One], n).unify([One], m);
        fresh!(state, list, a, tail1, c);

        state.unify(list, Pair(a, tail1)).unify(tail1, Pair(c, Nil));
        state.unify(list, r);
        full_adder(state, d, One, One, a, c)
    }, {
        state.unify([One], n);
        gen_adder(state, d, n, m, r)
    }, {
        state.unify([One], m);
        over_one(&mut state, n);
        over_one(&mut state, r);
        adder(state, d, [One], n, r)
    }, {
        over_one(&mut state, n);
        gen_adder(state, d, n, m, r)
    })
}

fn gen_adder(mut state: State, d: Var<Bit>, n: Var<List<Bit>>, m: Var<List<Bit>>, r: Var<List<Bit>>) -> StateIter {
    fresh!(state, a, b, c, e, x, y, z);
    state.unify(Pair(a, x), n);
    pos(&mut state, y);
    state.unify(Pair(b, y), m);
    state.unify(Pair(c, z), r);
    pos(&mut state, z);
    single(state)
        .and(move |state| full_adder(state, d, a, b, c, e))
        .and(move |state| adder(state, e, x, y, z))
}

fn plus(mut state: State, n: Var<List<Bit>>, m: Var<List<Bit>>, k: Var<List<Bit>>) -> StateIter {
    let zero = state.make_var_of(Zero);
    adder(state, zero, n, m, k)
}

fn multiply(state: State, n: Var<List<Bit>>, m: Var<List<Bit>>, p: Var<List<Bit>>) -> StateIter {
    conde!(state, {
        state.unify(Nil, n).unify(Nil, p);
        state
    }, {
        pos(&mut state, n);
        state.unify(Nil, m).unify(Nil, p);
        state
    }, {
        pos(&mut state, m);
        state.unify([One], n).unify(m, p);
        state
    }, {
        over_one(&mut state, n);
        state.unify([One], m).unify(n, p);
        state
    }, {
        fresh!(state, x, z);
        state.unify(Pair(Zero, x), n).unify(Pair(Zero, z), p);
        pos(&mut state, x);
        pos(&mut state, z);
        over_one(&mut state, m);
        multiply(state, x, m, z)
    }, {
        fresh!(state, x, y);
        state.unify(Pair(One, x), n).unify(Pair(Zero, y), m);
        pos(&mut state, x);
        pos(&mut state, y);
        multiply(state, m, n, p)
    }, {
        fresh!(state, x, y);
        state.unify(Pair(One, x), n).unify(Pair(One, y), m);
        pos(&mut state, x);
        pos(&mut state, y);
        odd_multiply(state, x, n, m, p)
    })
}

fn odd_multiply(mut state: State, x: Var<List<Bit>>, n: Var<List<Bit>>, m: Var<List<Bit>>, p: Var<List<Bit>>) -> StateIter {
    fresh!(state, q);
    bound_multiply(state, q, p, n, m)
        .and(move |state| {
            multiply(state, x, m, q)
        })
        .and(move |mut state| {
            let twice_q = state.make_var_of(Pair(Zero, q));
            plus(state, twice_q, m, p)
        })
}

fn bound_multiply(state: State, q: Var<List<Bit>>, p: Var<List<Bit>>, n: Var<List<Bit>>, m: Var<List<Bit>>) -> StateIter {
    conde!(state, {
        state.unify(q, Nil).unify(p, Pair(__(), __()));
        state
    }, {
        fresh!(state, x, y, z);
        state.unify(Pair(__(), x), q).unify(Pair(__(), y), p);
        conde!(state, {
            fresh!(state, nil);
            state.unify(Nil, n).unify(Pair(__(), z), m).unify(Nil, nil);
            bound_multiply(state, x, y, z, nil)
        }, {
            state.unify(Pair(__(), z), n);
            bound_multiply(state, x, y, z, m)
        })
    })
}

fn five() {
    let mut state = State::new();
    fresh!(state, n, m);
    let five_num = build_num(&mut state, 5);
    for state in plus(state, n, m, five_num).into_iter() {
        let mut reifier = Reifier::new(&state);
        println!("{} + {} = 5", reify_list(&state, &mut reifier, n), reify_list(&state, &mut reifier, m));
    }
}

fn multiply_any(count: usize) {
    let mut state = State::new();
    fresh!(state, n, m, p);
    for state in multiply(state, n, m, p).into_iter().take(count) {
        let mut reifier = Reifier::new(&state);
        println!("{} * {} = {}", reify_list(&state, &mut reifier, n), reify_list(&state, &mut reifier, m), reify_list(&state, &mut reifier, p));
    }
}

fn reify_list<A>(state: &State, reifier: &mut Reifier, list: Var<List<A>>) -> String where A : ToVar {
    let list = match reifier.reify(list) {
        Reified::Value(x) => *x,
        x @ Reified::Unset(..) => { return format!("{:?}", x); }
    };

    let mut s = String::new();
    let mut last_tail = None;
    write!(s, "[ ").unwrap();
    let mut iter = list.var_iter(state).peekable();
    while let Some((head, tail)) = iter.next() {
        write!(s, "{:?}", reifier.reify(head)).unwrap();
        if iter.peek().is_some() {
            write!(s, ", ").unwrap();
        }
        last_tail = Some(tail);
    }
    let last_tail = last_tail.and_then(|tail| match reifier.reify(tail) {
        x @ Reified::Unset(..) => Some(x),
        _ => None
    });
    match last_tail {
        Some(x) => write!(s, " .. {:?} ]", x).unwrap(),
        None => write!(s, " ]").unwrap(),
    }
    s
}

fn main() {
    five();
    multiply_any(34);
}

