#![feature(fnbox)] // used by disjoint iterators.  Can be avoided by stupid tricks with FnMut and Option::take()
#![feature(rc_unique)] // used when disjoint iters return tails, as an optimization
#![feature(get_type_id)]
#![feature(raw)] // used by VarWrapper::get_wrapped_value().
#![feature(drain)] // used by StateProxyMerge (minor optimization)
#![feature(ref_slice)]

#[macro_use]
pub mod macros;
///! Contains the definition of `TailIterator`.
pub mod tailiter;
///! Contains `State`, which performs unification, and `Var`, the variable type it operates on.
#[macro_use]
pub mod core;
///! Contains `List`, a singly-linked list of variables.
pub mod list;
///! Contains iterators for combining `State`s.
pub mod iter;
///! Contains definitions of commonly used methods.  There's not much here, yet.
pub mod builtins;
pub mod finitedomain;
pub mod constraints;
