///! Define multiple new variables at once.
#[macro_export]
macro_rules! fresh {
    ($state:ident, $($var:ident),+) => (
        $(let $var = $state.make_var();)+
    )
}

///! Used internally by the other `cond!` macros.
#[macro_export]
macro_rules! cond_builder {
    ($method:ident, $state:ident, $($block:block),+,) => ({
        let mut builder = $crate::iter::IterBuilder::new();
        $(builder.push(move |mut $state| $block);)+
        builder.$method($state)
    })
}

#[macro_export]
macro_rules! conde {
    ($state:ident, $($blocks:block),*) => (
        conde_inner!($state, 0, conds:(), blocks:($($blocks,)*)).conde($state)
    );
}
#[macro_export]
macro_rules! conda {
    ($state:ident, $($blocks:block),*) => (
        conde_inner!($state, 0, conds:(), blocks:($($blocks,)*)).conda($state)
    );
}
#[macro_export]
macro_rules! condu {
    ($state:ident, $($blocks:block),*) => (
        conde_inner!($state, 0, conds:(), blocks:($($blocks,)*)).condu($state)
    );
}

#[macro_export]
macro_rules! method {
    ($name:ident($state:ident, { args=$($arg:ident: $argty:ty),* $(,)* } { vars=$($var:ident: $varty:ty),* $(,)* }) $body:expr) => (
        #[allow(non_camel_case_types)]
        fn $name<$($var,)*>(mut $state: State, $($arg: $argty,)* $($var: $var,)*) -> StateIter
        where $($var: ToVar<VarType=$varty>,)* {
            use $crate::iter::StateIter;
            $(let $var = $state.make_var_of($var);)*
            #[allow(unused_mut)]
            fn inner(mut $state: State, $($arg: $argty,)* $($var: Var<$varty>,)*) -> StateIter {
                StateIter::from({ $body })
            }
            inner($state, $($arg,)* $($var,)*)
        }
    );
    ($name:ident($state:ident, $($var:ident: $varty:ty),*) $body:expr) => (
        method!($name($state, { args= } { vars=$($var: $varty,)* }) $body);
    );
}

#[macro_export]
macro_rules! conde_inner {
    ($state:ident, $count:expr, conds:($($counts:expr => $cblocks:expr,)*), blocks:($block:expr, $($blocks:expr,)*)) => (
        conde_inner!($state, $count + 1, conds:($($counts => $cblocks,)* $count => $block,), blocks:($($blocks,)*))
    );
    ($state:ident, $count:expr, conds:($count0:expr => $block0:expr, $($counts:expr => $cblocks:expr,)*), blocks:()) => ({
        $crate::iter::IterBuilder::new(move |pos, mut $state| {
            if pos == $count0 { $block0.into() }
            $(else if pos == $counts { $cblocks.into() })*
            else { panic!() }
        }, $count)
    });
}
