theory VectorClock
    imports Main
begin

datatype VectorClock = Clock "nat list"

(* Initial vector clock. *)
definition "empty_clock = Clock []"

(* Increments the n-th component of the vector clock. *)
fun increment :: "nat => VectorClock => VectorClock" where
    "increment 0 (Clock []) = Clock [1]" |
    "increment 0 (Clock (x#xs)) = Clock ((x+1) # xs)" |
    "increment n (Clock []) = (
        case (increment (n-1) (Clock []))
            of (Clock tail) => Clock (0#tail)
        )" |
    "increment n (Clock (x#xs)) = (
        case (increment (n-1) (Clock xs))
            of (Clock tail) => Clock(x#tail)
    )"

(* Compares two vector clocks. *)
fun less_eq :: "VectorClock => VectorClock => bool" where
    "less_eq (Clock []) (Clock []) = True" |
    "less_eq (Clock []) (Clock (x#xs)) = True" |
    "less_eq (Clock (x#xs)) (Clock []) = False" |
    "less_eq (Clock (x#xs)) (Clock (y#ys)) = (x <= y & less_eq (Clock xs) (Clock ys))"

(* Takes the maximum of two vector clocks. *)
fun max :: "VectorClock => VectorClock => VectorClock" where
    "max (Clock []) other = other" |
    "max other (Clock []) = other" |
    "max (Clock (x#xs)) (Clock (y#ys)) = (
        case max (Clock xs) (Clock ys) of
            (Clock tail) => Clock ((if x > y then x else y) # tail)
    )"

end
