#[macro_use]
extern crate kanren;

use kanren::core::{State, Unifier, Var, VarStore, VarRetrieve};
use kanren::iter::StateIter;
use kanren::list::List;
use kanren::list::{Pair, Nil};
use std::io::Read;
use std::fmt::{Formatter, Debug};
use kanren::finitedomain::Fd;
use kanren::constraints::AllDiffConstraint;

fn main() {
    let mut state = State::new();
    fresh!(state, orig_list);
    let mut list = orig_list;
    let mut colvars: Vec<Vec<Var<Fd>>> = (0..9).map(|_| Vec::new()).collect();
    let mut rowvars: Vec<Vec<Var<Fd>>> = (0..9).map(|_| Vec::new()).collect();
    let mut groupvars: Vec<Vec<Var<Fd>>> = (0..9).map(|_| Vec::new()).collect();
    let mut puzstr = String::new();
    let stdin = ::std::io::stdin();
    stdin.lock().read_to_string(&mut puzstr).unwrap();

    let puzzle: Vec<Option<u8>> = puzstr.chars().flat_map(|x| {
        (if x.is_numeric() { Some(Some((x as u32 - '0' as u32) as u8)) }
         else if x == '_' { Some(None) }
         else { None })
            .into_iter()
    }).collect();
    println!("Input: ");
    display_output(puzzle.iter().map(|x| *x));
    println!("");
    assert!(puzzle.len() == 81);

    let xy = (0..9).flat_map(|y| (0..9).map(move |x| (x,y)));
    for ((x, y), &puz) in xy.zip(puzzle.iter()) {
        fresh!(state, entry, tail);
        let value = match puz {
            Some(x) => Fd::new_single(x as usize),
            None => Fd::new_values((1..10).collect()),
        };
        state.unify(entry, value);
        colvars[x].push(entry);
        rowvars[y].push(entry);
        groupvars[x / 3 + (y / 3) * 3].push(entry);
        state.unify(list, Pair(entry, tail));
        list = tail;
    }
    state.unify(list, Nil);
    //println!("colvars: {:?}, rowvars: {:?}, groupvars: {:?}", colvars, rowvars, groupvars);
    for vars in colvars.into_iter().chain(rowvars).chain(groupvars) {
        state.add_constraint(AllDiffConstraint::new(vars));
    }
    #[allow(unused_variables)]
    fn get_fds(state: State, list: Var<List<Fd>>) -> StateIter {
        //conde!(state, {
            //state.unify(list, Nil);
            //single(state)
        //}, {
            //fresh!(state, head, tail);
            //state.unify(list, Pair(head, tail));
        //}
        ::kanren::core::assign_all_values(state)
    }

    struct UnderscoreWriter<T>(Option<T>);
    impl<T> Debug for UnderscoreWriter<T> where T: Debug {
        fn fmt(&self, fmt: &mut Formatter) -> ::std::fmt::Result {
            match self.0 {
                Some(ref x) => write!(fmt, "{:?}", x),
                None => write!(fmt, "_")
            }
        }
    }
    fn display_list(state: &mut State, list: Var<List<Fd>>) {
        let list = state.get_value(list).unwrap();
        display_output(list.iter(state).map(|x| x.and_then(Fd::single_value)))
    }
    fn display_output<I, T>(i: I) where I: IntoIterator<Item=Option<T>>, T: Debug {
        let items: Vec<_> = i.into_iter().map(|x| UnderscoreWriter(x)).collect();
        for chunk in items.chunks(9) {
            println!("{:?}", chunk);
        }
    }

    for (i, mut state) in get_fds(state, orig_list).into_iter().enumerate().take(100) {
        //let reifier = Reifier::new(&state);
        println!("solution {}:", i);
        display_list(&mut state, orig_list);
        println!("");
        //println!("state: {:?}\n", state);
    }
}
