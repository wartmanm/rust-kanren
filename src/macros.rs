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
    ($state:ident, $($block:block),+) => ({
        cond_builder!(conde, $state, $($block,)+)
    })
}
#[macro_export]
macro_rules! condi {
    ($state:ident, $($block:block),+) => ({
        cond_builder!(condi, $state, $($block,)+)
    })
}
#[macro_export]
macro_rules! conda {
    ($state:ident, $($block:block),+) => ({
        cond_builder!(conda, $state, $($block,)+)
    })
}
#[macro_export]
macro_rules! condu {
    ($state:ident, $($block:block),+) => ({
        cond_builder!(condu, $state, $($block,)+)
    })
}

#[macro_export]
macro_rules! method {
    ($name:ident($state:ident, { args=$($arg:ident: $argty:ty),* } { vars=$($var:ident: $varty:ty),* }) $body:expr) => (
        #[allow(non_camel_case_types)]
        fn $name<$($var,)*>(mut $state: State, $($arg: $argty,)* $($var: $var,)*) -> StateIter
        where $($var: ToVar<VarType=$varty>,)* {
            use $crate::iter::StateIter;
            $(let $var = $state.make_var_of($var);)*
            fn inner(mut $state: State, $($arg: $argty,)* $($var: Var<$varty>,)*) -> StateIter {
                StateIter::from({ $body })
            }
            inner($state, $($arg,)* $($var,)*)
        }
    )
}
