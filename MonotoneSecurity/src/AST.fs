module AST

type artm = 
    | Num of int
    | Var of uint
    | Arr of uint * artm
    | UMin of artm
    | Plus of artm * artm
    | Minus of artm * artm
    | Times of artm * artm
    | Divide of artm * artm
    | Modulo of artm * artm

type bool =
    | True 
    | Neg of bool
    | Dis of bool * bool
    | Equal of artm * artm
    | Less of artm * artm

type com =
    | Skip
    | AssignV of uint * artm
    | AssignA of uint * artm * artm
    | Sequence of com * com
    | If of gcom
    | Do of gcom
and gcom =
    | Case of bool * com
    | Choice of gcom * gcom

type action =
    | Skp
    | Tst of bool
    | AsV of uint * artm
    | AsA of uint * artm * artm

type node =
    | Start
    | Mid of uint
    | Finish

type lit = 
    | Vr of uint 
    | Ar of uint