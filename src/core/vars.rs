use core::{ToVar, StateProxy, VarWrapper, Var, Unifier, VarStore};
use std::rc::Rc;
use std::marker::PhantomData;
use list::List;

// TODO: Once negative bounds work, add a blanket impl for all but Var and get rid of all of
// this.

///! Provides the body of the standard `VarWrapper` impl, which uses `==` to compare against another
///! `VarWrapper`.  Used by `value_wrapper!()`.
#[macro_export]
macro_rules! default_varwrapper_impl {
    ($x:ty) => {
        fn _equals_(&self, other: &$crate::core::VarWrapper, _: &mut $crate::core::StateProxy) -> bool {
            let other = other.get_wrapped_value::<$x>();
            self == other
        }
    }
}

///! Provides the body of the standard `ToVar` impl, which calls `State::store_value()`.  Used by
///! `value_wrapper!()`.
#[macro_export]
macro_rules! default_tovar_impl {
    ($x:ty) => {
        type VarType = $x;
        fn into_var<U: $crate::core::VarStore>(self, state: &mut U) -> $crate::core::Var<$x> {
            state.store_value(self)
        }
    }
}

///! Provides default implementations of `ToVar` and `VarWrapper` for a type.
#[macro_export]
macro_rules! value_wrapper {
    ($x:ty) => {
        impl $crate::core::VarWrapper for $x { default_varwrapper_impl!($x); }
        impl $crate::core::ToVar for $x { default_tovar_impl!($x); }
    };

    ($x:ty, $($param:ident: $($extra:ident)&*),*) => {
        impl<$($param,)*> $crate::core::VarWrapper for $x where $($param: ToVar $(+ $extra)*,)+ {
            default_varwrapper_impl!($x);
        }
        impl<$($param,)*> $crate::core::ToVar for $x where $($param: ToVar $(+ $extra)*,)+ {
            default_tovar_impl!($x);
        }
    };

    ($x:ty, $($param:ident),+) => {
        impl<$($param,)*> $crate::core::VarWrapper for $x where $($param: ToVar,)* {
            default_varwrapper_impl!($x);
        }
        impl<$($param,)*> $crate::core::ToVar for $x where $($param: ToVar,)* {
            default_tovar_impl!($x);
        }
        //TODO this ought to work...
        //value_wrapper!($x, $($param:,)+);
    };
}

value_wrapper!(i8);
value_wrapper!(i16);
value_wrapper!(i32);
value_wrapper!(i64);
value_wrapper!(isize);
value_wrapper!(u8);
value_wrapper!(u16);
value_wrapper!(u32);
value_wrapper!(u64);
value_wrapper!(f32);
value_wrapper!(f64);
value_wrapper!(usize);
value_wrapper!(String);
value_wrapper!(&'static str);
value_wrapper!(bool);
value_wrapper!(char);

value_wrapper!(Box<T>, T: PartialEq);
value_wrapper!(Rc<T>, T: PartialEq);
//value_wrapper!(Vec<T>, T: PartialEq);
//value_wrapper!(Option<T>, T: PartialEq);
//value_wrapper!(Result<A,B>, A: PartialEq, B: PartialEq);

value_wrapper!(());

value_wrapper!(*const A, A);
value_wrapper!(*mut A, A);
value_wrapper!(&'static A, A: PartialEq);
//value_wrapper!(&'static [A], A: PartialEq);

macro_rules! tuple_wrapper {
    (($($param:ident $arg:ident),*)) => {
        impl<$($param,)*> ToVar for ($($param,)*) where $($param: ToVar,)* {
            type VarType = ($(Var<<$param as ToVar>::VarType>,)*);
            #[allow(non_snake_case)]
            fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<<Self as ToVar>::VarType> {
                let ($($param,)*) = self;
                $(let $param = state.make_var_of($param);)*
                state.store_value(($($param,)*))
            }
        }
        impl<$($param,)*> VarWrapper for ($(Var<$param>,)*) where $($param: ToVar,)* {
            #[allow(non_snake_case)]
            fn _equals_(&self, other: &VarWrapper, state: &mut StateProxy) -> bool {
                let &($($param,)*) = other.get_wrapped_value::<($(Var<$param>),*)>();
                let &($($arg,)*) = self;
                state
                $(.unify_vars($param, $arg))*
                .ok()
            }
        }
    }
}

tuple_wrapper!((A a, B b));
tuple_wrapper!((A a, B b, C c));
tuple_wrapper!((A a, B b, C c, D d));
tuple_wrapper!((A a, B b, C c, D d, E e));

impl<A> VarWrapper for Option<Var<A>> where A: ToVar {
    fn _equals_(&self, other: &VarWrapper, state: &mut StateProxy) -> bool {
        let other = other.get_wrapped_value::<Option<Var<A>>>();
        match (self, other) {
            (&None, &None) => true,
            (&Some(a), &Some(b)) => state.unify_vars(a, b).ok(),
            _ => false,
        }
    }
}

impl<A> ToVar for Option<A> where A: ToVar {
    type VarType = Option<Var<<A as ToVar>::VarType>>;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<<Self as ToVar>::VarType> {
        let var = self.map(|x| x.into_var(state));
        state.store_value(var)
    }
}

impl<A, B> VarWrapper for Result<Var<A>, Var<B>> where A: ToVar, B: ToVar {
    fn _equals_(&self, other: &VarWrapper, state: &mut StateProxy) -> bool {
        let other = other.get_wrapped_value::<Result<Var<A>, Var<B>>>();
        match (self, other) {
            (&Ok(a), &Ok(b)) => state.unify_vars(a, b).ok(),
            (&Err(a), &Err(b)) => state.unify_vars(a, b).ok(),
            _ => false,
        }
    }
}

impl<A, B> ToVar for Result<Var<A>, Var<B>> where A: ToVar, B: ToVar {
    //type VarType = Result<Var<<A as ToVar>::VarType>, Var<<B as ToVar>::VarType>>;
    // FIXME This is the wrong type, what is going on here?  The one above, respecting A and B's
    // vartypes, is correct, but it doesn't compile.
    type VarType = Result<Var<A>, Var<B>>;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<<Self as ToVar>::VarType> {
        let var = match self {
            Ok(x) => Ok(x.into_var(state)),
            Err(x) => Err(x.into_var(state)),
        };
        state.store_value(var)
    }
}

#[derive(Debug)]
pub struct IgnoreVar<A>(PhantomData<A>) where A: ToVar;

///! `__`() (two underscores) provides a fresh variable each time it's called, which can be passed as
///!  an argument any time you don't care about the return value.
pub fn __<A>() -> IgnoreVar<A> where A: ToVar { IgnoreVar(PhantomData) }

impl<A> Clone for IgnoreVar<A> where A: ToVar { fn clone(&self) -> IgnoreVar<A> { *self } }
impl<A> Copy for IgnoreVar<A> where A: ToVar { }
impl<A> PartialEq for IgnoreVar<A> where A: ToVar { fn eq(&self, _: &IgnoreVar<A>) -> bool { false } }
impl<A> ToVar for IgnoreVar<A> where A: ToVar {
    type VarType = A;
    fn into_var<U: VarStore>(self, state: &mut U) -> Var<A> {
        state.make_var()
    }
}

impl<A> ToVar for &'static [A] where A: ToVar + Clone {
    type VarType=List<<A as ToVar>::VarType>;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<List<<A as ToVar>::VarType>> {
        List::new_from_iter(state, self.iter().map(|x| x.clone()))
    }
}

impl<A> ToVar for Vec<A> where A: ToVar {
    type VarType=List<<A as ToVar>::VarType>;
    fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<List<<A as ToVar>::VarType>> {
        List::new_from_iter(state, self)
    }
}

macro_rules! list_builder {
    ($count:expr) => {
        impl<A> ToVar for [A; $count] where A: ToVar + Clone {
            type VarType = List<<A as ToVar>::VarType>;
            fn into_var<U: VarStore+Unifier>(self, state: &mut U) -> Var<List<<A as ToVar>::VarType>> {
                List::new_from_iter(state, self.into_iter().map(|x| x.clone()))
            }
        }
    }
}
list_builder!(0);
list_builder!(1);
list_builder!(2);
list_builder!(3);
list_builder!(4);
list_builder!(5);
list_builder!(6);
list_builder!(7);
list_builder!(8);
list_builder!(9);
list_builder!(10);
list_builder!(11);
list_builder!(12);
list_builder!(13);
list_builder!(14);
list_builder!(15);
list_builder!(16);
list_builder!(17);
list_builder!(18);
list_builder!(19);
list_builder!(20);
list_builder!(21);
list_builder!(22);
list_builder!(23);
list_builder!(24);
list_builder!(25);
list_builder!(26);
list_builder!(27);
list_builder!(28);
list_builder!(29);
list_builder!(30);
list_builder!(31);
list_builder!(32);
