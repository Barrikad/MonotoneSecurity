module Lattices


type level1 =
    | Bottom
    | Mid1
    | Mid2
    | Top

let level1Join l1 l2 =
    match l1, l2 with
    | Bottom, l
    | l, Bottom -> l
    | Top, _
    | _, Top -> Top
    | _ when l1 = l2 -> l1
    | _ -> Top

let level1Less l1 l2 =
    match l1, l2 with
    | Bottom,_ -> true
    | _,Top -> true
    | _ when l1 = l2 -> true
    | _ -> false
