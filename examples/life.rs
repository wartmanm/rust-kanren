#[macro_use]
extern crate kanren;

use kanren::core::{State, Unifier, Var, VarStore, VarRetrieve};
use kanren::iter::{StateIter, single};
use std::io::Read;
use std::rc::Rc;
use std::fmt::{Debug, Formatter};

struct CellGrid {
    size: (i32, i32),
    cells: Vec<Var<bool>>,
}

impl CellGrid {
    fn get(&self, x: i32, y: i32) -> Option<Var<bool>> {
        if x < 0 || y < 0 || x >= self.size.0 || y >= self.size.1 {
            None
        } else {
            Some(self.cells[(y * self.size.0 + x) as usize])
        }
    }

    fn neighbors(&self, x: i32, y: i32) -> Vec<Var<bool>> {
        [(-1, -1), ( 0, -1), ( 1, -1),
         (-1,  0),           ( 1,  0),
         (-1,  1), ( 0,  1), ( 1,  1)]
             .iter()
             .flat_map(|&(off_x, off_y)| {
                 self.get(x + off_x, y + off_y).into_iter()
             })
             .collect()
    }

    fn new(state: &mut State, x: i32, y: i32) -> CellGrid {
        assert!(x > 0);
        assert!(y > 0);
        let cells = (0..x*y).map(|_| state.make_var()).collect();
        CellGrid { size: (x, y), cells: cells }
    }

    fn from_strings(state: &mut State, strings: &[&str]) -> CellGrid {
        let mut cells = Vec::with_capacity(strings.len() * strings[0].len());
        for (y, line) in strings.iter().enumerate() {
            for (x, item) in line.chars().enumerate() {
                let var = match item {
                    ' ' => state.make_var_of(false),
                    '*' => state.make_var_of(true),
                    '?' => state.make_var(),
                    other => panic!("unknown character '{:?}' at {},{}", other, x, y),
                };
                cells.push(var);
            }
        }
        CellGrid { size: (strings[0].len() as i32, strings.len() as i32), cells: cells }
    }
}

struct CellGridWriter<'a> {
    state: &'a State,
    grid: &'a CellGrid,
}

impl<'a> CellGridWriter<'a> {
    fn new(state: &'a State, grid: &'a CellGrid) -> CellGridWriter<'a> {
        CellGridWriter { state: state, grid: grid }
    }
}

impl<'a> Debug for CellGridWriter<'a> {
    fn fmt(&self, fmt: &mut Formatter) -> ::std::fmt::Result {
        for chunk in self.grid.cells.chunks(self.grid.size.0 as usize) {
            for var in chunk.iter() {
                match self.state.get_value(*var) {
                    Some(&true) => write!(fmt, "█").unwrap(),
                    Some(&false) => write!(fmt, " ").unwrap(),
                    None => write!(fmt, "?").unwrap(),
                }
            }
            write!(fmt, "\n").unwrap();
        }
        Ok(())
    }
}

fn life_sum(state: State, a: Var<i32>, b: Var<i32>, cell: Var<bool>) -> StateIter {
    conde!(state, {
        state.unify(cell, false).unify(a, b);
        state
    }, {
        state.unify(cell, true).unify(a, 0).unify(b, 1);
        state
    }, {
        state.unify(cell, true).unify(a, 1).unify(b, 2);
        state
    }, {
        state.unify(cell, true).unify(a, 2).unify(b, 3);
        state
    }, {
        state.unify(cell, true).unify(a, 3).unify(b, 4);
        state
    }, {
        state.unify(cell, true).unify(a, 4).unify(b, 5);
        state
    }, {
        state.unify(cell, true).unify(a, 5).unify(b, 6);
        state
    }, {
        state.unify(cell, true).unify(a, 6).unify(b, 7);
        state
    }, {
        state.unify(cell, true).unify(a, 7).unify(b, 8);
        state
    })
}

fn neighbor_sum(mut state: State, neighbors: &[Var<bool>], total: Var<i32>) -> StateIter {
    let mut tmp_sums: Vec<Var<i32>> = neighbors.iter().map(|_| state.make_var()).collect();
    tmp_sums.push(total);
    state.unify(tmp_sums[0], 0);
    let result = neighbors.iter().enumerate().fold(single(state), |iter, (i, &cell)| {
        let a = tmp_sums[i];
        let b = tmp_sums[i + 1];
        iter.and(move |state| {
            life_sum(state, a, b, cell)
        })
    });
    result
}

fn cell_survival(state: State, focus: Var<bool>, sum: Var<i32>, result: Var<bool>) -> StateIter {
    conde!(state, {
        state.unify(sum, 3).unify(result, true);
        state
    }, {
        state.unify(focus, true).unify(sum, 2).unify(result, true);
        state
    }, {
        state.unify(focus, false).unify(sum, 2).unify(result, false);
        state
    }, {
        state.unify(sum, 0).unify(result, false);
        state
    }, {
        state.unify(sum, 1).unify(result, false);
        state
    }, {
        state.unify(sum, 4).unify(result, false);
        state
    }, {
        state.unify(sum, 5).unify(result, false);
        state
    }, {
        state.unify(sum, 6).unify(result, false);
        state
    }, {
        state.unify(sum, 7).unify(result, false);
        state
    }, {
        state.unify(sum, 8).unify(result, false);
        state
    })
}

fn step(state: State, old: &CellGrid, new: &CellGrid) -> StateIter {
    let mut iter = single(state);
    for y in 0..old.size.1 {
        for x in 0..old.size.0 {
            let neighbors = Box::new(old.neighbors(x, y));
            let oldcell = old.get(x, y).unwrap();
            let newcell = new.get(x, y).unwrap();
            iter = iter.and(move |mut state| {
                fresh!(state, sum);
                neighbor_sum(state, &**neighbors, sum)
                .and(move |state| cell_survival(state, oldcell, sum, newcell))
            });
        }
    }
    iter
}

#[allow(dead_code)]
fn reverse_glider() {
    let mut state = State::new();
    let input = [
        "     ",
        "     ",
        "  *  ",
        "   * ",
        " *** ",
        "     ",
        ];
    let grid = CellGrid::from_strings(&mut state, &input);
    let oldgrid = Rc::new(CellGrid::new(&mut state, grid.size.0, grid.size.1));
    let old2 = Rc::new(CellGrid::new(&mut state, grid.size.0, grid.size.1));
    let old3 = Rc::new(CellGrid::new(&mut state, grid.size.0, grid.size.1));
    let newgrid = grid;

    println!("beginning with\n{:?}\nand\n{:?}\n",
             CellGridWriter::new(&state, &oldgrid),
             CellGridWriter::new(&state, &newgrid));

    let printold = oldgrid.clone();
    let printold2 = old2.clone();
    let printold3 = old3.clone();
    let old2_tmp = old2.clone();

    let iter =
        step(state, &oldgrid, &newgrid)
        .and(move |state| step(state, &*old2, &*oldgrid))
        .and(move |state| step(state, &*old3, &*old2_tmp));

    for (i, state) in iter.into_iter().enumerate().take(100) {
        println!("solution {}:\n{:?}\nbecomes\n{:?}\nbecomes\n{:?}\nbecomes{:?}", i,
                 CellGridWriter::new(&state, &printold3),
                 CellGridWriter::new(&state, &printold2),
                 CellGridWriter::new(&state, &printold),
                 CellGridWriter::new(&state, &newgrid));
    }
}

fn main() {
    let mut state = State::new();
    let oldgrid = Rc::new(CellGrid::from_strings(&mut state, &[
        "       ",
        " ????? ",
        " ????? ",
        " ????? ",
        " ????? ",
        " ????? ",
        "       ",
    ]));
    let savegrid = oldgrid.clone();
    let iter = single(state)
        .and(move |state| step(state, &oldgrid, &oldgrid));
    for (i, state) in iter.into_iter().enumerate().take(100) {
        println!("still-life {}:\n{:?}", i, CellGridWriter::new(&state, &savegrid));
    }
}
