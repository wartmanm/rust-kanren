#[macro_use]
extern crate kanren;

use std::env;
use std::str::FromStr;

use kanren::core::{State, Unifier, Var, ToVar, VarStore, VarRetrieve};
use kanren::core::vars::__;
use kanren::list::List;
use kanren::list::{Pair, Nil};
use kanren::builtins::{length, contains};
use kanren::iter::{StateIter, single};

type Square = (Var<i32>, Var<i32>, Var<i32>, Var<i32>);

fn nqueens<T: ToVar<VarType=i32>>(mut state: State, n: T, queens: Var<List<Square>>) -> StateIter {
    let n = state.make_var_of(n);
    fn remove_squares(count: i32, state: State, list: Var<List<Square>>, q: Var<Square>, result: Var<List<Square>>) -> StateIter {
        conde!(state, {
            // The list is finished, return.
            state.unify(Nil, list);
            state.unify(result, list);
            state
        }, {
            fresh!(state, a, b, c, d, tail, x, y, dl, dr);
            state.unify(Pair((a, b, c, d), tail), list);
            state.unify(q, (x, y, dl, dr));
            // Using conda causes only one branch to be taken.  If we used conde here, we could
            // backtrack and skip filtering.
            conda!(state, {
                state.unify(a, x); // filter for same column
                remove_squares(count, state, tail, q, result)
            }, {
                state.unify(b, y); // filter for same row
                remove_squares(count, state, tail, q, result)
            }, {
                state.unify(c, dl); // filter for same left diagonal
                remove_squares(count, state, tail, q, result)
            }, {
                state.unify(d, dr); // filter for same right diagonal
                remove_squares(count, state, tail, q, result)
            }, {
                // We passed all the filters!  Add this item to the result list and continue on.
                fresh!(state, result_tail);
                state.unify(Pair((a, b, c, d), result_tail), result);
                remove_squares(count + 1, state, tail, q, result_tail)
            })
        })
    }
    fn place_queens(pos: i32, state: State, queens: Var<List<Square>>, squares: Var<List<Square>>) -> StateIter {
        conde!(state, {
            // Done placing queens.
            state.unify(queens, Nil);
            state
        }, {
            fresh!(state, q, q_tail, remaining_squares);
            // Make sure the current queen belongs to the next row down.  This isn't essential but
            // it eliminates duplicates and is a very, very useful optimization.
            state.unify(queens, Pair(q, q_tail));
            state.unify((__(), pos, __(), __()), q);
            // Assign the current queen to a position.
            contains(state, q, squares)
            // Find out what spaces remain.
            .and(move |state| remove_squares(0, state, squares, q, remaining_squares))
            // Assign the next queen to one of those spaces.
            .and(move |state| place_queens(pos + 1, state, q_tail, remaining_squares))
        })
    }
    single(state)
    // Assign a size to the board.
    .and(move |state| length(state, queens, n))
    .and(move |mut state| {
        // Create squares as (x, y, left diagonal, right diagonal) tuples for the current board
        // size.
        let n = *state.get_value(n).unwrap();
        let squares = (0..n).flat_map(|x| (0..n).map(move |y| (x, y)))
            .map(|(x, y)| ((x, y, (x+y), (x-y))));
        let square_list = List::new_from_iter(&mut state, squares);

        place_queens(0, state, queens, square_list)
    })
}

pub fn main() {
    let args: Vec<String> = env::args().collect();
    let mut state = State::new();
    fresh!(state, n, queens);
    let firstarg = args.get(1).and_then(|x| usize::from_str(x).ok());
    if let Some(firstarg) = firstarg {
        state.unify(n, firstarg as i32);
    }
    for state in nqueens(state, n, queens) {
        let n = *state.get_value(n).unwrap();
        for q in state.get_value(queens).unwrap().iter(&state) {
            let (x,y,_,_) = *q.unwrap();
            let x = *state.get_value(x).unwrap();
            let y = *state.get_value(y).unwrap();

            let mut black_square = y % 2 == 0;
            for draw_x in (0..n) {
                match black_square {
                    _ if draw_x == x => print!("♕ "),
                    false => print!("  "),
                    true => print!("░░"),
                }
                black_square = !black_square;
            }
            print!("\n");
        }
        print!("\n");
    }
}
