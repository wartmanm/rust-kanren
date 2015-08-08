#![feature(test)]
#[macro_use]
extern crate kanren;

extern crate test;
use test::Bencher;
use std::rc::Rc;

use kanren::core::{State, Unifier, Var, ToVar, VarStore};
use kanren::iter::{StateIter, single}; use kanren::core::vars::__;
use kanren::builtins::contains;
use kanren::list::{List, Pair};
use Cigarettes::*;
use Nationalities::*;
use Colors::*;
use Drinks::*;
use Animals::*;


#[derive(Copy, Clone, PartialEq, Debug)]
enum Cigarettes {
    OldGold,
    Kool,
    Chesterfield,
    LuckyStrike,
    Parliament,
}

#[derive(Copy, Clone, PartialEq, Debug)]
enum Nationalities {
    English,
    Spanish,
    Ukranian,
    Norwegian,
    Japanese,
}

#[derive(Copy, Clone, PartialEq, Debug)]
enum Animals {
    Dog,
    Snail,
    Fox,
    Horse,
    Zebra,
}

#[derive(Copy, Clone, PartialEq, Debug)]
enum Colors {
    Red,
    Green,
    Ivory,
    Yellow,
    Blue,
}

#[derive(Copy, Clone, PartialEq, Debug)]
enum Drinks {
    Coffee,
    Tea,
    Milk,
    OrangeJuice,
    Water,
}

value_wrapper!(Cigarettes);
value_wrapper!(Nationalities);
value_wrapper!(Animals);
value_wrapper!(Colors);
value_wrapper!(Drinks);

type VarHouse = (Var<Nationalities>, Var<Rc<Colors>>, Var<Animals>, Var<Drinks>, Var<Cigarettes>);

#[derive(Default, Debug, Clone, Copy)]
struct House {
    nationality: Option<Nationalities>,
    color: Option<Colors>,
    pet: Option<Animals>,
    drink: Option<Drinks>,
    cigarette: Option<Cigarettes>,
}

impl ToVar for House {
    type VarType = VarHouse;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<VarHouse> {
        let nationality = self.nationality.map(|x| state.make_var_of(x)).unwrap_or(state.make_var());
        let color = self.color.map(|x| state.make_var_of(Rc::new(x))).unwrap_or(state.make_var());
        let pet = self.pet.map(|x| state.make_var_of(x)).unwrap_or(state.make_var());
        let drink = self.drink.map(|x| state.make_var_of(x)).unwrap_or(state.make_var());
        let cigarette = self.cigarette.map(|x| state.make_var_of(x)).unwrap_or(state.make_var());
        state.make_var_of((nationality, color, pet, drink, cigarette))
    }
}

fn to_right<L, R>(mut state: State, left: L, right: R, list: Var<List<VarHouse>>) -> StateIter
where L: ToVar<VarType=VarHouse>, R: ToVar<VarType=VarHouse> {
    let left = state.make_var_of(left);
    let right = state.make_var_of(right);
    conde!(state, {
        state.unify(Pair(left, Pair(right, __())), list);
        state
    }, {
        fresh!(state, tail);
        state.unify(Pair(__(), tail), list);
        to_right(state, left, right, tail)
    })
    // this is about 50% slower :(
    //fresh!(state, pos, neighbor);
    //state.add_constraint(SumConstraint::new(pos, 1, neighbor));
    //state
        //.and(move |state| index(state, left, list, pos))
        //.and(move |state| index(state, right, list, neighbor))
}

#[allow(unused_mut)]
fn neighbor(mut state: State, a: House, b: House, list: Var<List<VarHouse>>) -> StateIter {
    let a = state.make_var_of(a);
    let b = state.make_var_of(b);
    conde!(state, {
        to_right(state, a, b, list)
    }, {
        to_right(state, b, a, list)
    })
}

fn neighborhood_iter() -> StateIter {
    let mut state = State::new();
    fresh!(state, houses);
    let empty = Default::default();
    fresh!(state, a, b, c, d, e);
    state.unify(houses, [a, b, c, d, e]);
    state.unify(c, House { drink: Some(Milk), .. empty });
    state.unify(a, House { nationality: Some(Norwegian), .. empty });
    let states = single(state)
        .and(move |state| neighbor(state, House { nationality: Some(Norwegian), .. empty }, House { color: Some(Blue), .. empty }, houses))
        .and(move |state| to_right(state, House { color: Some(Green), .. empty }, House { color: Some(Ivory), .. empty }, houses))
        .and(move |state| contains(state, House { nationality: Some(English), color: Some(Red), .. empty }, houses))
        .and(move |state| contains(state, House { color: Some(Yellow), cigarette: Some(Kool), .. empty }, houses))
        .and(move |state| contains(state, House { nationality: Some(Spanish), pet: Some(Dog), .. empty }, houses))
        .and(move |state| contains(state, House { color: Some(Green), drink: Some(Coffee), .. empty }, houses))
        .and(move |state| contains(state, House { nationality: Some(Ukranian), drink: Some(Tea), .. empty }, houses))
        .and(move |state| contains(state, House { drink: Some(OrangeJuice), cigarette: Some(LuckyStrike), .. empty }, houses))
        .and(move |state| contains(state, House { nationality: Some(Japanese), cigarette: Some(Parliament), .. empty }, houses))
        .and(move |state| contains(state, House { pet: Some(Snail), cigarette: Some(OldGold), .. empty }, houses))
        .and(move |state| neighbor(state, House { cigarette: Some(Kool), .. empty }, House { pet: Some(Horse), .. empty }, houses))
        .and(move |state| neighbor(state, House { cigarette: Some(Chesterfield), .. empty }, House { pet: Some(Fox), .. empty }, houses))
        .and(move |state| contains(state, House { drink: Some(Water), .. empty }, houses))
        .and(move |state| contains(state, House { pet: Some(Zebra), .. empty }, houses));
    states
}

#[bench]
fn test_neighborhood(b: &mut Bencher) {
    b.iter(|| {
        neighborhood_iter().into_iter().next()
    });
}


#[cfg(not(test))]
fn main() {
    neighborhood_iter();
}
