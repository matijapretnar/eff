let rec loop_pure n a =
    if n = 0 then
        a
    else
        loop_pure (n - 1) (a + 1)

let rec loop_incr n counter =
    if n = 0 then
        ()
    else
        (incr counter; loop_incr (n - 1) counter)

let rec loop_state n state =
    if n = 0 then
        ()
    else
        (state := !state + 1; loop_state (n - 1) state)

let pure n = loop_pure n 0

let incr n =
    let counter = ref 0 in
    loop_incr n counter

let state n =
    let state = ref 0 in
    loop_state n state
