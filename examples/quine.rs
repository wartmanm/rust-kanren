#[macro_use]
extern crate kanren;
extern crate ref_slice;

use kanren::core::{State, Unifier, Var, ToVar, VarStore, TypeList};
use kanren::core::{VarWrapper, StateProxy, UnifyResult, UntypedVar, TypedVar};
use kanren::iter::StateIter;
use kanren::core::vars::__;
use kanren::core::reify::Reifier;
use kanren::core::reify::Reified::*;
use kanren::list::{List, Pair, Nil};
use kanren::list::List::Pair as VarPair;
use kanren::constraints::{Disequal, AbsentConstraint};
use Tree::*;
use std::fmt::{self, Write, Debug};
use std::cell::RefCell;
use std::rc::Rc;
use std::io;
use std::any::TypeId;
use ref_slice::ref_slice;

#[derive(Debug, Copy, Clone)]
enum Tree {
    VarSym(Var<String>),
    //VarLitStr(Var<String>),
    VarList(Var<List<Tree>>),
    VarFnBody {
        body: VarElem,
        arg: Var<String>,
        env: VarEnv,
    },
}

type VarElem = Var<Tree>;
type VarEnv = Var<Env>;
type Env = List<(Var<String>, VarElem)>;
type VarPath = Var<List<&'static str>>;

trait ReifyPrint {
    fn write(&self, _: &mut Reifier, _: &mut Write);
}

fn reify_print<A: ReifyPrint>(r: &mut Reifier, v: A) -> String {
    let mut s = String::new();
    write!(s, "{:?}", reify_fmt(r, v)).unwrap();
    s
}

fn reify_fmt<'a, 'b, A: ReifyPrint>(r: &'a mut Reifier<'b>, v: A) -> ReifyPrinter<'a, 'b, A> {
    let cell = RefCell::new(r);
    ReifyPrinter { r: cell, val: v }
}

impl<A> ReifyPrint for Var<A> where A: ReifyPrint + VarWrapper {
    fn write(&self, r: &mut Reifier, w: &mut Write) {
        let reified = r.reify(*self);
        match reified {
            Value(x) => x.write(r, w),
            Unset(x) => { write!(w, "_.{}", x).unwrap(); },
        }
    }
}

struct ReifyPrinter<'a, 'b: 'a, A: ReifyPrint> {
    r: RefCell<&'a mut Reifier<'b>>,
    val: A,
}

impl<'a, 'b, A: ReifyPrint> Debug for ReifyPrinter<'a, 'b, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.val.write(&mut **self.r.borrow_mut(), f);
        Ok(())
    }
}

impl<T: ReifyPrint + VarWrapper> ReifyPrint for List<T> {
    fn write(&self, r: &mut Reifier, w: &mut Write) {
        let mut list = *self;
        let mut started = false;
        write!(w, "(").unwrap();
        loop {
            match list {
                VarPair(h, t) => {
                    if started {
                        write!(w, " ").unwrap();
                    }
                    started = true;
                    h.write(r, w);
                    match r.reify(t) {
                        x @ Unset(..) => {
                            write!(w, " . {:?})", x).unwrap();
                            break;
                        },
                        Value(&v) => {
                            list = v;
                        }
                    }
                },
                Nil => {
                    write!(w, ")").unwrap();
                    break;

                },
            }
        }
    }
}

impl<'a> ReifyPrint for &'a str {
    fn write(&self, _: &mut Reifier, w: &mut Write) {
        write!(w, "{}", self).unwrap();
    }
}

impl ReifyPrint for String {
    fn write(&self, _: &mut Reifier, w: &mut Write) {
        write!(w, "{}", self).unwrap();
    }
}

impl<A: ReifyPrint + VarWrapper, B: ReifyPrint + VarWrapper> ReifyPrint for (Var<A>, Var<B>) {
    fn write(&self, r: &mut Reifier, w: &mut Write) {
        write!(w, "(").unwrap();
        self.0.write(r, w);
        write!(w, ", ").unwrap();
        self.1.write(r, w);
        write!(w, ")").unwrap();
    }
}

impl ReifyPrint for Tree {
    fn write(&self, r: &mut Reifier, w: &mut Write) {
        match *self {
            VarSym(x) => {
                write!(w, "{}", r.reify(x)).unwrap()
            },
            //VarLitStr(x) => {
                //write!(w, "{:?}", r.reify(x)).unwrap()
            //},
            VarList(x) => {
                x.write(r, w);
            },
            VarFnBody { body, arg, env } => {
                write!(w, "(closure ").unwrap();
                arg.write(r, w);
                write!(w, " ").unwrap();
                body.write(r, w);
                write!(w, " ").unwrap();
                env.write(r, w);
                write!(w, ")").unwrap();

                //write!(w, "Fn {{ arg: '").unwrap();
                //arg.write(r, w);
                //write!(w, "', body: ").unwrap();
                //body.write(r, w);
                //write!(w, ", env: ").unwrap();
                //env.write(r, w);
                //write!(w, "}}").unwrap();
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Sym<A>(A) where A: ToVar<VarType=String>;
//#[derive(Debug, Clone, Copy)]
//struct LitStr<A>(A) where A: ToVar<VarType=String>;
#[derive(Debug, Clone, Copy)]
struct TList<A>(A) where A: ToVar<VarType=List<Tree>>;
#[derive(Debug, Clone, Copy)]
struct TFnBody<A, B, C>(A, B, C) where A: ToVar<VarType=Tree>, B: ToVar<VarType=String>, C: ToVar<VarType=Env>;

macro_rules! treevar {
    ($x:ty => $wrapper:ident) => {
        impl ToVar for $x {
            type VarType = Tree;
            fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<Tree> {
                let a = state.make_var_of(self.0);
                state.store_value($wrapper(a))
            }
        }
    };
    ($x:ty, $($param:ident: $vartype:ty),* => $wrapper:ident) => {
        impl<$($param,)*> ToVar for $x where $($param: ToVar<VarType=$vartype>,)* {
            type VarType = Tree;
            fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<Tree> {
                let a = state.make_var_of(self.0);
                state.store_value($wrapper(a))
            }
        }
    }
}

macro_rules! list {
    ($head:expr, $($rest:expr),* $(,)*) => {
        Pair($head, list!($($rest,)*))
    };
    ($head:expr) => {
        Pair($head, Nil)
    };
    () => {
        Nil
    };

}

treevar!(Sym<A>, A: String => VarSym);
//treevar!(LitStr<A>, A: String => VarLitStr);
treevar!(TList<A>, A: List<Tree> => VarList);

impl<A, B, C> ToVar for TFnBody<A, B, C> where A: ToVar<VarType=Tree>, B: ToVar<VarType=String>, C: ToVar<VarType=List<(Var<String>, VarElem)>> {
    type VarType = Tree;
    fn into_var<U: VarStore + Unifier>(self, state: &mut U) -> Var<Tree> {
        let body = state.make_var_of(self.0);
        let arg = state.make_var_of(self.1);
        let env: VarEnv = state.make_var_of(self.2);
        state.store_value(VarFnBody { body: body, arg: arg, env: env })
    }
}


impl ToVar for Tree {
    type VarType = Tree;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<Tree> {
        state.store_value(self)
    }
}

impl VarWrapper for Tree {
    fn unify_with(&self, other: &VarWrapper, ctxt: &mut StateProxy) -> UnifyResult {
        let other = other.get_wrapped_value();
        //println!("unify {:?} with {:?}", self, other);
        match (*self, *other) {
            (VarSym(a),VarSym(b)) => ctxt.unify(a, b).ok().into(),
            //(VarLitStr(a), VarLitStr(b)) => ctxt.unify(a, b).ok().into(),
            (VarList(a), VarList(b)) => ctxt.unify(a, b).ok().into(),
            (VarFnBody { body: a1, env: a2, arg: a3 }, VarFnBody { body: b1, env: b2, arg: b3 }) => {
                ctxt.unify(a1, b1).unify(a2, b2).unify(a3, b3).ok().into()
            },
            _ => false.into()
        }
    }
    
    fn var_iter<'a>(&'a self) -> Option<Box<Iterator<Item=UntypedVar> + 'a>> {
        fn slicer<'b, A: Copy>(a: &'b A) -> Option<Box<Iterator<Item=A> + 'b>> {
            Some(Box::new(ref_slice(a).iter().map(|x| *x)))
        }
        match *self {
            VarSym(ref a) => slicer(a.untyped_ref()),
            //VarLitStr(ref a) => slicer(a.untyped_ref()),
            VarList(ref a) => slicer(a.untyped_ref()),
            VarFnBody { body, arg, env } => {
                Some(Box::new(ThreeVarIter { vars: [body.untyped(), arg.untyped(), env.untyped()], pos: 0 }))
            },
        }
    }
    fn can_contain_type(_: &TypeList, other: TypeId) -> bool {
        return other == TypeId::of::<Tree>()
            || other == TypeId::of::<List<Tree>>()
            || other == TypeId::of::<Env>()
            || other == TypeId::of::<List<&'static str>>()
    }
    fn occurs_check(&self, state: &StateProxy, other: TypedVar) -> bool {
        if !Self::can_contain_type(&TypeList::Nil, other.type_id()) { false }
        else {
            match *self {
                VarSym(_) => false,
                VarList(list) => {
                    state.occurs_check(other, list.untyped())
                },
                VarFnBody { body, arg, env } => {
                    state.occurs_check(other, body.untyped())
                    || state.occurs_check(other, arg.untyped())
                    || state.occurs_check(other, env.untyped())
                }
            }
        }
    }
}

#[test]
fn tree_occurs_check() {
    let mut s = State::new();
    fresh!(s, inner_list, outer_list);
    s.unify(outer_list, TList(list!(Sym("test".to_owned()), inner_list)));
    println!("inner_list: {:?}, outer_list: {:?}", inner_list, outer_list);
    println!("state: {:?}", s);
    s.unify(inner_list, outer_list);
    assert!(!s.ok());
}

#[test]
fn list_occurs_check() {
    let mut s = State::new();
    fresh!(s, inner_list, outer_list);
    s.unify(outer_list, Pair(Sym("test".to_owned()), inner_list));
    println!("inner_list: {:?}, outer_list: {:?}", inner_list, outer_list);
    println!("state: {:?}", s);
    s.unify(inner_list, outer_list);
    assert!(!s.ok());
}

#[test]
fn tree_contains_tree() {
    assert!(Tree::can_contain_type(&TypeList::Nil, TypeId::of::<Tree>()));
    assert!(List::<Tree>::can_contain_type(&TypeList::Nil, TypeId::of::<Tree>()));
    assert!(Tree::can_contain_type(&TypeList::Nil, TypeId::of::<List<Tree>>()));
}

struct ThreeVarIter {
    vars: [UntypedVar; 3],
    pos: usize,
}

impl Iterator for ThreeVarIter {
    type Item = UntypedVar;
    fn next(&mut self) -> Option<UntypedVar> {
        let ret = self.vars.get(self.pos).map(|x| *x);
        self.pos += 1;
        ret
    }
}

fn not_in_env(state: State, name: Var<String>, env: VarEnv) -> StateIter {
    conde!(state, {
        fresh!(state, env_name, rest);
        state.unify(env, Pair((env_name, __()), rest));
        state.add_constraint(Disequal::new(name, env_name));
        not_in_env(state, name, rest)
    }, {
        state.unify(env, Nil);
        state
    })
}

method!(eval(state, expr: Tree, env: Env, result: Tree) {
    conde!(state, {
        fresh!(state, quoted);
        state.unify(TList(list!(Sym("quote".to_owned()), quoted)), expr);
        state.add_constraint(AbsentConstraint::new(TFnBody(__(), __(), __()), quoted));
        state.unify(result, quoted);
        state
    }, {
        fresh!(state, listed, listresult);
        state.unify(TList(Pair(Sym("list".to_owned()), listed)), expr);
        state.add_constraint(AbsentConstraint::new(TFnBody(__(), __(), __()), listed));
        state.unify(result, TList(listresult));
        eval_list(state, listed, env, listresult)
    }, {
        fresh!(state, sym);
        state.unify(Sym(sym), expr);
        lookup(state, sym, env, result)
    }, {
        fresh!(state, fn_uneval, arg_uneval, actual_fn, actual_arg, argname, fnbody, fnenv);
        state.unify(TList(list!(fn_uneval, arg_uneval)), expr);
        state.unify(TFnBody(fnbody, argname, fnenv), actual_fn);

        state.add_constraint(Disequal::new(fn_uneval, Sym("quote".to_owned())));
        state.add_constraint(Disequal::new(fn_uneval, Sym("list".to_owned())));

        eval(state, fn_uneval, env, actual_fn)
        .and(move |state| eval(state, arg_uneval, env, actual_arg))
        .and(move |state| eval(state, fnbody, Pair((argname, actual_arg), fnenv), result))
    }, {
        fresh!(state, fnbody, arg1);
        let lambda = state.make_var_of("lambda".to_owned());
        state.unify(TList(list!(Sym(lambda), TList([Sym(arg1)]), fnbody)), expr);
        state.unify(result, TFnBody(fnbody, arg1, env));
        not_in_env(state, lambda, env)
    })
});

fn lookup(mut state: State, name: Var<String>, env: VarEnv, result: VarElem) -> StateIter {
    fresh!(state, k, v, rest);
    state.unify(env, Pair((k, v), rest));
    conde!(state, {
        state.unify(k, name).unify(v, result);
        state
    }, {
        state.add_constraint(Disequal::new(name, k));
        lookup(state, name, rest, result)
    })
}

fn eval_list(state: State, list: Var<List<Tree>>, env: VarEnv, result: Var<List<Tree>>) -> StateIter {
    conde!(state, {
        state.unify(list, Nil).unify(result, Nil);
        state
    }, {
        fresh!(state, head, tail, result_head, result_tail);
        state.unify(Pair(head, tail), list);
        state.unify(Pair(result_head, result_tail), result);
        eval(state, head, env, result_head)
        .and(move |state| eval_list(state, tail, env, result_tail))
    })
}

fn main() {
    let mut state = State::new();
    let env = state.make_var_of(Nil);
    let expr = state.make_var();
    state.add_constraint(AbsentConstraint::new(TFnBody(__(), __(), __()), expr));
    fresh!(state, result);
    state.unify(result, expr);
    let iter = eval(state, expr, env, result);
    print_states(iter, result, env, expr);
}

fn print_state(state: &State, result: Var<Tree>, env: VarEnv, expr: Var<Tree>) {
    let mut r = Reifier::new(&state);
    println!("expr: {}", reify_print(&mut r, expr));
    println!("result: {}", reify_print(&mut r, result));
    println!("env: {}", reify_print(&mut r, env));
}

fn print_states(iter: StateIter, result:Var<Tree>, env: VarEnv, expr: Var<Tree>) -> Option<State> {
    let mut s: Option<State> = None;
    for (i, state) in iter.into_iter().take(10).enumerate() {
        {
            println!("solution {}", i);
            print_state(&state, result, env, expr);
        }
        if i == 0 {
            s = Some(state);
        } else if i > 0 {
            s = None;
        }
    }
    s
}

#[allow(unused)]
fn repl(mut state: State) {
    let env = state.make_var_of(Nil);
    loop {
        let mut line = String::new();
        io::stdin().read_line(&mut line).unwrap();
        let parsed = parse(&mut state, &*line);
        match parsed {
            Ok(x) => {
                {
                    let mut r = Reifier::new(&state);
                    println!("parsed: {}", reify_print(&mut r, x));
                }
                fresh!(state, result);
                //let path = state.make_var_of(Nil);
                //let newpath = state.make_var();
                let rcstate = Rc::new(state);
                let tmpstate = State::with_parent(rcstate.clone());
                let mut iter = eval(tmpstate, x, env, result);
                if let Some(new_state) = iter.into_iter().next() {
                    state = new_state;
                    let mut r = Reifier::new(&state);
                    let _ = reify_print(&mut r, x); // load in unset vars
                    println!("result: {}", reify_print(&mut r, result));
                } else {
                    println!("some kind of error :(");
                    state = State::with_parent(rcstate);
                }
            },
            Err(x) => {
                println!("err: {:?}", x);
            }
        }
    }
}

#[allow(unused)]
#[derive(Debug)]
enum ParseErr {
    EOF,
    UnmatchedOpen,
    UnmatchedClose,
    UnmatchedQuote,
    Unimplemented,
}

#[allow(unused)]
fn parse(state: &mut State, s: &str) -> Result<Var<Tree>, ParseErr> {
    match parse_inner(state, s) {
        Ok((t, _)) => Ok(t),
        Err(x) => Err(x),
    }
}

#[allow(unused)]
fn parse_inner<'a>(state: &mut State, s: &'a str) -> Result<(Var<Tree>, &'a str), ParseErr> {
    let s = s.trim_left_matches(|c: char| c.is_whitespace());
    if s.is_empty() {
        return Err(ParseErr::EOF);
    }
    let c = s.chars().next().unwrap();
    if c == '(' {
        let (inner, new_s) = try!(parse_list(state, &s[1..]));
        Ok((state.make_var_of(TList(inner)), new_s))
    } else if c.is_numeric() {
        Err(ParseErr::Unimplemented)
        //let mut it = s.splitn(2, |c: char| c.is_numeric());
        //Ok((it.next().unwrap(), it.next().unwrap_or("")))
    } else if c == ')' {
        Err(ParseErr::UnmatchedClose)
    } else if c == '"' {
        Err(ParseErr::Unimplemented)
        //let (inner, new_s) = try!(parse_str(&s[1..]));
        //Ok((state.make_var_of(LitStr(inner)), new_s))
    } else {
        let mut name = s;
        let mut remaining = "";
        for (i, c) in s.char_indices() {
            if c.is_whitespace() || c == '(' || c == ')' || c == '"' {
                name = &s[..i];
                remaining = &s[i..];
                break;
            }
        }
        let sym = state.make_var_of(Sym(name.to_owned()));
        Ok((sym, remaining))
    }
}

#[allow(unused)]
fn parse_str(s: &str) -> Result<(String, &str), ParseErr> {
    let mut bs = false;
    for (i, c) in s.char_indices() {
        if bs {
            bs = false;
        } else { 
            match c {
                '\\' => { bs = true; },
                '"' => { return Ok((s[..1].to_owned(), &s[i + 1..])); },
                _ => { },
            }
        }
    }
    Err(ParseErr::UnmatchedQuote)
}

#[allow(unused)]
fn parse_list<'a>(state: &mut State, mut s: &'a str) -> Result<(Var<List<Tree>>, &'a str), ParseErr> {
    //fresh!(state, head, tail);
    let mut list = state.make_var();
    let head = list;
    loop {
        match parse_inner(state, s) {
            Ok((var, new_s)) => {
                let tail = state.make_var();
                state.unify(list, (Pair(var, tail)));
                list = tail;
                s = new_s;
            },
            Err(ParseErr::EOF) => { return Err(ParseErr::UnmatchedOpen); }
            Err(ParseErr::UnmatchedClose) => {
                state.unify(list, Nil);
                let close = &s[s.find(')').unwrap() + 1..];
                return Ok((head, close));
            },
            Err(other) => { return Err(other); }
        }
    }
}
