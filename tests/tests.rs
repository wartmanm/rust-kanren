#[macro_use]
extern crate kanren;

use kanren::core::{State, Var, Unifier, VarStore, VarRetrieve, VarMap};
use kanren::core::vars::__;
use kanren::core::assign_all_values;
use kanren::finitedomain::{Fd, fd_values};
use kanren::constraints::{SumConstraint, FdLessOrEqual, AllDiffConstraint, Disequal};
use kanren::core::{Constraint, ToConstraint, ConstraintResult, StateProxy, UntypedVar};
use std::fmt::{self, Write, Debug, Formatter};
use kanren::iter::{single, IterBuilder, VarIter, StateIterExt};
use kanren::list::List;
use kanren::list::{Pair, Nil};
use kanren::builtins::{index, length, contains};
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashSet;
use std::iter::FromIterator;

#[test]
fn many_vars() {
    let mut state = State::new();
    let result = state.make_var();
    let a = state.make_var();
    let b = state.make_var();
    let c = state.make_var();
    let d = state.make_var();
    state.unify(a, b);
    state.unify(c, d);
    state.unify(a, c);
    state.unify(result, a);
    state.unify(d, 1);
    let mut iter = single(state);
    let variter = VarIter::new(&mut iter, result);
    let result: Vec<i32> = variter.map(|x| x.unwrap()).collect();
    assert!(result == vec![1]);
}

#[test]
fn many_vars_macro() {
    let mut state = State::new();
    fresh!(state, a, b, c, d, result);
    state
    .unify(a, b)
    .unify(c, d)
    .unify(a, c)
    .unify(result, a)
    .unify(d, 1);
    let mut iter = single(state);
    let variter = iter.var_iter(result);
    let result: Vec<i32> = variter.map(|x| x.unwrap()).collect();
    assert!(result == vec![1]);
}

#[test]
fn simple_nested() {
    let mut state = State::new();
    let result = state.make_var();
    let iter = IterBuilder::new(move |_, state| {
        let subiter = IterBuilder::new(move |_, mut state| {
            state.unify(result, 1);
            state.into()
        }, 1);
        subiter.conde(state)
    }, 1);
    let mut iter = iter.conde(state);
    let result: Vec<i32> = VarIter::new(&mut iter, result).map(|x| x.unwrap()).collect();
    assert!(result == vec![1]);
}

#[test]
fn conditions() {
    let mut state = State::new();
    let result = state.make_var();
    let runner = IterBuilder::new(move |i, mut state| {
        state.unify(result, i);
        let subrunner = IterBuilder::new(move |j, mut state| {
            state.unify(result, j);
            println!("{:?}", state);
            state.into()
        }, 3);
        subrunner.conde(state)
    }, 3);
    let mut iter = runner.conde(state);
    let result: Vec<usize> = iter.var_iter(result).map(|x| x.unwrap()).collect();
    assert!(result == vec![0, 1, 2]);
}

#[test]
fn basic_list() {
    let mut state = State::new();
    let result = state.make_var();

    let items: Vec<i32> = vec![1,2,3];
    let list = List::new_from_iter(&mut state, items.into_iter());
    state.unify(result, list);
    let states = single(state);

    let items: Vec<Vec<i32>> = states.into_iter().map(|s| {
        let item = s.get_value(result).unwrap().clone();
        item.iter(&s).map(|x| *x.unwrap()).collect()
    }).collect();
    assert!(items == vec![vec![1, 2, 3]]);
}

#[test]
fn list_remains_empty() {
    let mut state = State::new();
    let list = state.make_var();
    let states = length(state, list, 3);
    let states = states.flat_map(move |mut state| {
        println!("in length callback");
        let pos = state.make_var();
        let states = index(state, pos, list, pos);
        println!("done length callback");
        states
    });
    let items: Vec<Vec<Option<i32>>> = states.into_iter().map(|s| {
        let item = *s.get_value(list).unwrap();
        let vars: Vec<(Var<i32>, Var<List<i32>>)> = item.var_iter(&s).collect();
        let result = item.iter(&s).map(|x| x.map(|y| *y)).collect();
        println!("items: {:?}", result);
        println!("list vars: {:?}", vars);
        println!("state: {:?}", s);
        result
    }).take(2).collect();
    let occupied: Vec<usize> = items.iter().map(|x| x.iter().filter(|y| y.is_some()).count()).collect();
    assert!(occupied.iter().all(|x| *x == 1));
}

#[test]
fn joined_condes() {
    let mut state = State::new();
    fresh!(state, vara, varb);
    let items = vec![1,2,3];
    let list = List::new_from_iter(&mut state, items.into_iter());
    fresh!(state, dontcare1, dontcare2);
    let states = single(state);
    let states = states.flat_map(move |state| index(state, vara, list, dontcare1));
    let states = states.flat_map(move |state| index(state, varb, list, dontcare2));
    let items: Vec<(i32, i32)> = states.into_iter().map(|s| {
        let a = *s.get_value(vara).unwrap();
        let b = *s.get_value(varb).unwrap();
        (a, b)
    }).collect();
    for item in items.iter() {
        println!("{:?}", item);
    }
    let hashitems: HashSet<(i32, i32)> = HashSet::from_iter(items.clone());
    assert!(hashitems == HashSet::from_iter(vec![
        (1, 1), (1, 2), (1, 3),
        (2, 1), (2, 2), (2, 3),
        (3, 1), (3, 2), (3, 3)])
    );
}

#[test]
fn bad_index_terminates() {
    let mut state = State::new();
    let var: Var<()> = state.make_var();
    fresh!(state, list);
    let states = index(state, var, list, -1);
    assert!(states.into_iter().next().is_none());
}

#[test]
fn bad_length_terminates() {
    let mut state = State::new();
    let list: Var<List<()>> = state.make_var();
    let states = length(state, list, -1);
    assert!(states.into_iter().next().is_none());
}

/*
#[test]
fn circular_list() {
    let mut state = State::new();
    fresh!(state, heada, taila, headb, tailb);
    let paira = state.make_pair(heada, taila);
    let pairb = state.make_pair(headb, tailb);
    state.unify(heada, "hello");
    state.unify(headb, "hello");
    state.unify(taila, paira);
    state.unify(tailb, pairb);
    state.unify(taila, tailb);
}
*/

#[test]
fn circular() {
    let mut state = State::new();
    fresh!(state, a, b, c, result);
    println!("a == b");
    state.unify(a, b);
    println!("b == a");
    state.unify(b, a);
    println!("a == a");
    state.unify(a, a);
    println!("c == c");
    state.unify(c, c);
    println!("a = {:?}", state.get_value(a));
    println!("b = {:?}", state.get_value(b));
    println!("c = {:?}", state.get_value(c));
    println!("c == 3");
    state.unify(3, c);
    state.unify(a, c);
    state.unify(a, result);
    state.unify(b, result);
    println!(r" a: {:?} b: {:?} c: {:?} result: {:?}", state.get_value(a), state.get_value(b), state.get_value(c), state.get_value(result));

    let mut states = single(state);
    let results: Vec<i32> = states.var_iter(result).map(|x| x.unwrap()).collect();
    assert!(results == vec![3]);
}

#[test]
fn disequal() {
    let mut state = State::new();
    fresh!(state, a, b, c);
    println!("a: {:?}, b: {:?}, c: {:?}", a, b, c);
    println!("c != a");
    state.add_constraint(Disequal::new(c, a));
    println!("a == b");
    state.unify(a, b);
    println!("b == a");
    state.unify(b, a);
    println!("b == c");
    state.unify(b, c);
    state.unify(3, a);
    assert!(!state.ok());
}

#[test]
fn disequal_onelist() {
    let mut state = State::new();
    fresh!(state, a, b, list);
    state.unify(list, Pair(a, Pair(b, Nil)));
    let input = List::new_from_iter(&mut state, vec![1,2,3]);
    let states = single(state)
        .and(move |state| contains(state, a, input))
        .and(move |state| contains(state, b, input))
        .and(move |mut state| {
            state.add_constraint(Disequal::new(a, b));
            println!("state ok: {}", state.ok());
            state
        })
        .into_iter();

    let items: Vec<(i32, i32)> = states.map(|state| {
        (*state.get_value(a).unwrap(), *state.get_value(b).unwrap())
    }).collect();
    let hashitems: HashSet<(i32, i32)> = HashSet::from_iter(items.clone());
    println!("{:?}", items);
    assert!(hashitems == HashSet::from_iter(vec![
        (1, 2), (1, 3),
        (2, 1), (2, 3),
        (3, 1), (3, 2)
    ]));
}


#[test]
fn disequal_lists() {
    let mut state = State::new();
    fresh!(state, lista, listb);
    fresh!(state, a1, a2, b1, b2);
    state.unify(Pair(a1, Pair(a2, __())), lista);
    state.unify(Pair(b1, Pair(b2, __())), listb);
    let states = single(state)
        .and(move |mut state| {
            state.add_constraint(Disequal::new(lista, listb));
            state
        })
        .and(move |state| length(state, lista, 2))
        .and(move |state| length(state, listb, 2))
        .and(move |state| contains(state, "a", lista))
        .and(move |state| contains(state, "b", lista))
        .and(move |state| contains(state, "a", listb))
        .and(move |state| contains(state, "b", listb))
        .into_iter();

    let items: Vec<(((&str, &str), (&str, &str)))> = states.map(|state| {
        ((*state.get_value(a1).unwrap(), *state.get_value(a2).unwrap()),
        (*state.get_value(b1).unwrap(), *state.get_value(b2).unwrap()))
    }).collect();
    println!("{:?}", items);
    assert!(items == [
        (("a", "b"), ("b", "a")),
        (("b", "a"), ("a", "b"))
    ]);
}

#[test]
fn fd_intersection() {
    let mut state = State::new();
    fresh!(state, a, b, c);
    state.unify(a, Fd::new_values((1..6).collect()));
    state.unify(b, Fd::new_values(vec![1, 3, 6, 8, 9]));
    state.unify(c, Fd::new_values(vec![2, 3, 4, 5, 6, 8]));
    println!("a: {:?}", state.get_value(a));
    state.unify(a, b);
    println!("a == b, a: {:?}", state.get_value(a));
    state.unify(b, c);
    println!("b == c, a: {:?}", state.get_value(a));
    assert!(state.get_value(a).unwrap().single_value() == Some(3));
    assert!(state.get_value(b).unwrap().single_value() == Some(3));
    assert!(state.get_value(c).unwrap().single_value() == Some(3));
    state.unify(c, Fd::new_values((10..31).collect()));
    assert!(!state.ok());
}

#[derive(Clone)]
struct ConstraintFn {
    f: Rc<Box<Fn(&mut StateProxy) -> ConstraintResult<ConstraintFn>>>,
    vars: Vec<UntypedVar>,
}

impl Debug for ConstraintFn {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        write!(fmt, "ConstraintFn {{ ... }}")
    }
}

impl ToConstraint for ConstraintFn {
    type ConstraintType = ConstraintFn;
    fn into_constraint(self, _: &mut State) -> ConstraintFn { self }
}

impl Constraint for ConstraintFn {
    fn update(&self, proxy: &mut StateProxy) -> ConstraintResult<ConstraintFn> { (self.f)(proxy) }
    fn relevant(&self, _: &VarMap) -> bool { true }
    fn update_vars(&mut self, vars: &State) {
        for var in self.vars.iter_mut() {
            vars.update_var(var)
        }
    }
}

impl ConstraintFn {
    fn new<F, I>(vars: I, f: F) -> ConstraintFn
    where F: Fn(&mut StateProxy) -> ConstraintResult<ConstraintFn> + 'static,
          I: IntoIterator<Item=UntypedVar>
    { ConstraintFn { f: Rc::new(Box::new(f)), vars: vars.into_iter().collect() } }
}

#[test]
fn rollback_fd() {
    let mut state = State::new();
    fresh!(state, a, b);
    state.unify(a, Fd::new_values((1..6).collect()));
    let orig_a = Fd::new_values((1..6).collect());
    let orig_b = Fd::new_values(vec![1, 3, 6, 8, 9]);
    state.unify(a, orig_a.clone());
    state.unify(b, orig_b.clone());
    let constraint_run = Rc::new(RefCell::new(false));
    let cr = constraint_run.clone();
    state.add_constraint(ConstraintFn::new(vec![a.untyped(), b.untyped()], move |proxy| {
        proxy.unify_vars(a, b);
        println!("proxy value of a: {:?}", proxy.get_value(a));
        assert!(*proxy.get_value(a).unwrap() == Fd::new_values(vec![1, 3]));
        *cr.borrow_mut() = true;
        ConstraintResult::Failed
    }));
    assert!(!state.ok());
    assert!(*constraint_run.borrow());
    println!("orig_a: {:?}, a: {:?}", orig_a, state.get_value(a).unwrap());
    println!("orig_b: {:?}, b: {:?}", orig_b, state.get_value(b).unwrap());
    assert!(*state.get_value(a).unwrap() == orig_a);
    assert!(*state.get_value(b).unwrap() == orig_b);
}

#[test]
fn disequal_and_fds() {
    let mut state = State::new();
    fresh!(state, a, b, c, d);
    state.unify(a, Fd::new_values((1..6).collect()));
    state.unify(b, Fd::new_values(vec![1, 3, 6, 8, 9]));
    state.unify(c, Fd::new_values(vec![2, 3, 4, 5, 6, 8]));
    state.unify(d, Fd::new_values(vec![3]));
    state.add_constraint(Disequal::new(a, d));
    assert!(state.ok());
    println!("unifying a and b for real");
    state.unify(a, b);
    println!("unified a and b for real");
    assert!(state.ok());
    println!("unifying b and c for real");
    state.unify(b, c);
    println!("unified b and c for real");
    assert!(!state.ok());
}

#[test]
fn sum() {
    let mut state = State::new();
    fresh!(state, a, b, c);
    
    state.add_constraint(SumConstraint::new(a, b, c));
    state.unify(a, 1).unify(b, 2);
    let c = state.get_value(c).map(|x| *x);
    println!("c: {:?}", c);
    assert!(c == Some(3));
}

#[test]
fn all_diff_enough() {
    let mut state = State::new();
    fresh!(state, a, b, c);
    state.add_constraint(AllDiffConstraint::new(vec![a, b, c]));
    state.unify(a, Fd::new_values(vec![1, 2, 3]));
    assert!(state.ok());
    state.unify(b, Fd::new_values(vec![2, 3]));
    assert!(state.ok());
    state.unify(c, Fd::new_single(1));
    assert!(state.ok());
    assert!(*state.get_value(a).unwrap() == Fd::new_values(vec![2, 3]));
    assert!(*state.get_value(b).unwrap() == Fd::new_values(vec![2, 3]));
    state.unify(b, Fd::new_values(vec![3]));
    assert!(state.ok());
    println!("a: {:?} = {:?}", a, state.get_value(a));
    println!("b: {:?} = {:?}", b, state.get_value(b));
    assert!(state.get_value(a).unwrap().single_value() == Some(2));
    assert!(state.get_value(b).unwrap().single_value() == Some(3));
}

#[test]
fn all_diff_toomany() {
    let mut state = State::new();
    fresh!(state, a, b, c, d);
    state.add_constraint(AllDiffConstraint::new(vec![a, b, c, d]));
    state.unify(a, Fd::new_values(vec![1, 2, 3]));
    assert!(state.ok());
    state.unify(b, Fd::new_values(vec![1, 2, 3]));
    assert!(state.ok());
    state.unify(c, Fd::new_values(vec![1, 2, 3]));
    assert!(state.ok());
    state.unify(d, Fd::new_values(vec![1, 2, 3]));
    assert!(assign_all_values(state).into_iter().count() == 0);
}

#[test]
fn less_fd() {
    let mut state = State::new();
    fresh!(state, a, b, c);
    state.unify(a, Fd::new_values(vec![2, 3, 4]));
    state.unify(b, Fd::new_values((1..4).collect()));
    state.unify(c, Fd::new_values(vec![0, 1, 2]));
    // should remove 4 from a, and 1 from b
    println!("a: {:?}, b: {:?}, c: {:?}", state.get_value(a).unwrap(), state.get_value(b).unwrap(), state.get_value(c).unwrap());
    state.add_constraint(FdLessOrEqual::new(a, b));
    println!("a <= b; a: {:?}, b: {:?}, c: {:?}", state.get_value(a).unwrap(), state.get_value(b).unwrap(), state.get_value(c).unwrap());
    assert!(state.ok());
    assert!(*state.get_value(a).unwrap() == Fd::new_values(vec![2, 3]));
    assert!(*state.get_value(b).unwrap() == Fd::new_values(vec![2, 3]));
    assert!(*state.get_value(c).unwrap() == Fd::new_values(vec![0, 1, 2]));
    // should remove 3 from a and b, and 0 from c
    state.add_constraint(FdLessOrEqual::new(b, c));
    println!("b <= c; a: {:?}, b: {:?}, c: {:?}", state.get_value(a).unwrap(), state.get_value(b).unwrap(), state.get_value(c).unwrap());
    assert!(state.ok());
    assert!(state.get_value(a).unwrap().single_value() == Some(2));
    assert!(*state.get_value(b).unwrap() == Fd::new_single(2));
    assert!(*state.get_value(c).unwrap() == Fd::new_values(vec![2]));

    fresh!(state, a, b, c);
    state.add_constraint(FdLessOrEqual::new(a, b));
    state.add_constraint(FdLessOrEqual::new(b, c));
    state.unify(a, Fd::new_values(vec![2, 3, 4]));
    state.unify(b, Fd::new_values(vec![1, 2, 3]));
    state.unify(c, Fd::new_values(vec![0, 1, 2]));
    println!("a: {:?}, b: {:?}, c: {:?}", state.get_value(a).unwrap(), state.get_value(b).unwrap(), state.get_value(c).unwrap());
    println!("a <= b; a: {:?}, b: {:?}, c: {:?}", state.get_value(a).unwrap(), state.get_value(b).unwrap(), state.get_value(c).unwrap());
    assert!(state.ok());
    //assert!(*state.get_value(a).unwrap() == Fd::new_values(vec![2, 3]));
    //assert!(*state.get_value(b).unwrap() == Fd::new_values(vec![2, 3]));
    //assert!(*state.get_value(c).unwrap() == Fd::new_values(vec![0, 1, 2]));
    //// should remove 3 from a and b
    //println!("b <= c; a: {:?}, b: {:?}, c: {:?}", state.get_value(a).unwrap(), state.get_value(b).unwrap(), state.get_value(c).unwrap());
    //assert!(state.ok());
    assert!(state.get_value(a).unwrap().single_value() == Some(2));
    assert!(*state.get_value(b).unwrap() == Fd::new_values(vec![2]));
    assert!(*state.get_value(c).unwrap() == Fd::new_single(2));
}

#[test]
fn fd_value_diff_test() {
    let mut state = State::new();
    let f = state.make_var_of(Fd::new_values(vec![0, 1]));
    let f2 = state.make_var_of(Fd::new_values(vec![0, 1]));
    state.add_constraint(AllDiffConstraint::new(vec![f, f2]));
    let states =
        fd_values(state, f, __())
        .and(move |state| fd_values(state, f2, __()));
    let result: Vec<(usize, usize)> = states.into_iter().map(|state| {
        let fval = state.get_value(f);
        let f2val = state.get_value(f2);
        println!("{:?}, {:?}", fval, f2val);
        (fval.unwrap().single_value().unwrap(), f2val.unwrap().single_value().unwrap())
    }).collect();
    println!("result: {:?}", result);
    assert!(result == vec![
        (0, 1), (1, 0)
    ]);
}

#[test]
fn fd_value_test() {
    let mut state = State::new();
    let f = state.make_var_of(Fd::new_values(vec![0,1,2]));
    let f2 = state.make_var_of(Fd::new_values(vec![3, 4, 5]));
    let states =
        fd_values(state, f, __())
        .and(move |state| fd_values(state, f2, __()));
    let result: Vec<(usize, usize)> = states.into_iter().map(|state| {
        let fval = state.get_value(f);
        let f2val = state.get_value(f2);
        println!("{:?}, {:?}", fval, f2val);
        (fval.unwrap().single_value().unwrap(), f2val.unwrap().single_value().unwrap())
    }).collect();
    for item in result.iter() {
        println!("{:?}", item);
    }
    let hashitems: HashSet<(usize, usize)> = HashSet::from_iter(result.clone());
    assert!(hashitems == HashSet::from_iter(vec![
        (0, 3), (0, 4), (0, 5),
        (1, 3), (1, 4), (1, 5),
        (2, 3), (2, 4), (2, 5)
    ]));
}

#[test]
fn occurs_check_test() {
    let mut state = State::new();
    fresh!(state, dupe);
    let list1 = state.make_var_of(Pair(1i32, dupe));
    let list2 = state.make_var_of(Pair(1, Pair(2, Pair(3, Pair(4, dupe)))));
    state.unify(list1, list2);
    if state.ok() {
        let mut contents = Vec::new();
        let mut node = list1;
        for _ in (1..10) {
            let (h, t) = match state.get_value(node).unwrap() {
                &List::Pair(h, t) => (h, t),
                _ => panic!(),
            };
            node = t;
            contents.push(state.get_value(h).unwrap().clone());
        }
        println!("{:?}", contents);
    }
    assert!(!state.ok());
}
