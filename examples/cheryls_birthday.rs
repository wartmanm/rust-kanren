//! See http://en.wikipedia.org/wiki/Cheryl%27s_Birthday.
//!
//! This solution is roughly identical to the one at http://jxf.me/entries/cheryls-birthday/, and
//! owes a substantial debt to it.

#[macro_use]
extern crate kanren;

use kanren::core::{State, Var, VarStore};
use kanren::core::reify::Reifier;
use kanren::core::vars::__;
use kanren::iter::{StateIter, findall_list};
use kanren::list::List;
use kanren::list::Nil;
use kanren::builtins::contains;

#[derive(Copy, Clone, PartialEq, Debug)]
enum Month {
    May,
    June,
    July,
    August,
}
value_wrapper!(Month);

fn main() {
    use Month::*;
    type Day = i32;
    type Date = (Var<Month>, Var<Day>);

    fn birthday_ok(mut state: State, month: Var<Month>, day: Var<Day>) -> StateIter {
        let birthdays = [
            (May, 15), (May, 16), (May, 19),
            (June, 17), (June, 18),
            (July, 14), (July, 16),
            (August, 14), (August, 15), (August, 17)
        ];
        let birthday_list = List::new_from_iter(&mut state, birthdays.iter().map(|x| *x));
        contains(state, (month, day), birthday_list)
    };

    fn s1(state: State, month: Var<Month>, _: Var<Day>) -> State {
        // There are no days in this month which correspond to this month and no other.
        findall_list(state, Nil, (), move |mut state| {
            fresh!(state, hypothetical_day);
            birthday_ok(state, month, hypothetical_day)
            .and(move |state| {
                // This day corresponds to this month and no other
                findall_list(state, [__()], (), move |mut state| {
                    fresh!(state, hypothetical_month);
                    birthday_ok(state, hypothetical_month, hypothetical_day)
                })
            })
        })
    };
    fn s2(state: State, _: Var<Month>, day: Var<Day>) -> State {
        // The provided day is unique within s1.
        findall_list(state, [__()], (), move |mut state| {
            fresh!(state, hypothetical_month);
            birthday_ok(state, hypothetical_month, day)
            .and(move |state| s1(state, hypothetical_month, day))
        })
    };
    fn s3(mut state: State, month: Var<Month>, _: Var<Day>) -> State {
        // The provided month is unique within s2.
        fresh!(state, hypothetical_day);
        findall_list(state, [__()], (), move |state| {
            birthday_ok(state, month, hypothetical_day)
            .and(move |state| s2(state, month, hypothetical_day))
        })
    };

    let mut state = State::new();
    fresh!(state, month, day);
    let mut states = birthday_ok(state, month, day)
        .and(move |state| s1(state, month, day))
        .and(move |state| s2(state, month, day))
        .and(move |state| s3(state, month, day))
        .into_iter();

    let first = states.next().unwrap();
    assert!(states.next().is_none());

    let mut reifier = Reifier::new(&first);
    println!("Solution: {:?} {:?}", reifier.reify(month), reifier.reify(day));
}
