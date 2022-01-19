module Algorithms

open AST

exception UnknownAlgorithm of string

type algorithm =
    | Stack

type algorithmConcrete =
    | StackC of node list * node list

let empty algorithm =
    match algorithm with
    | Stack -> StackC ([], [])

let rec extract algorithm =
    match algorithm with
    | StackC (xsOut,xsIn) ->
        match xsOut with
        | x :: xs -> Some (x,StackC (xs,xsIn))
        | [] -> 
            if List.isEmpty xsIn
            then None
            else extract (StackC (List.rev xsIn,[]))

let insert q algorithm =
    match algorithm with
    | StackC (xsOut,xsIn) -> StackC (xsOut,q :: xsIn)