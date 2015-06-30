# rust-kanren

This is a loose interpretation of miniKanren and cKanren in Rust.  It's a work in progress, suggestions are very welcome.

    // Display all permutations of the list [1, 2, 3].
    // (Using [1,2,3].permutations() would also work, but that's too easy.)

    let mut state = State::new();
    let result = state.make_var();
    let states = state
        .and(move |state| length(state, result, 3))
        .and(move |state| contains(state, 1, result))
        .and(move |state| contains(state, 2, result))
        .and(move |state| contains(state, 3, result));

    for state in states.flatten() {
        let list = state.get_value(result).unwrap();
        let items: Vec<i32> = list.iter(&state).map(|x| *x.unwrap()).collect();
        println!("{:?}", items);
    }

    // Result:
    // [1, 2, 3]
    // [1, 3, 2]
    // [2, 1, 3]
    // [3, 1, 2]
    // [2, 3, 1]
    // [3, 2, 1]
