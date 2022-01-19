module ProgramGraph
open AST

let sucNode n =
    match n with
    | Start -> Mid 0u
    | Mid i -> Mid (i + 1u)
    | Finish -> Finish

let rec notDone gc =
    match gc with
    | Case (b,_) -> b
    | Choice (gc1,gc2) -> Dis (notDone gc1, notDone gc2)

let rec freeVarsArtm artm =
    match artm with
    | Num _ -> Set.empty
    | Var v -> Set [Vr v]
    | Arr (v,_) -> Set [Ar v]
    | UMin a -> freeVarsArtm a
    | Plus (a1,a2) 
    | Minus (a1,a2) 
    | Times (a1,a2) 
    | Divide (a1,a2) 
    | Modulo (a1,a2) -> Set.union (freeVarsArtm a1) (freeVarsArtm a2)

let rec freeVarsBool bool =
    match bool with
    | True -> Set.empty
    | Neg b -> freeVarsBool b
    | Dis (b1,b2) -> Set.union (freeVarsBool b1) (freeVarsBool b2)
    | Equal (a1,a2)
    | Less (a1,a2) -> Set.union (freeVarsArtm a1) (freeVarsArtm a2)

let rec edgesC imps qm qs qf c = 
    match c with 
    | Skip -> qm, Set [(qs,Skp,imps,qf)]
    | AssignV (v,a) -> qm, Set [(qs,AsV (v,a),imps,qf)]
    | AssignA (v,a1,a2) -> qm, Set [(qs,AsA (v,a1,a2),imps,qf)]
    | Sequence (c1, c2) -> 
        let qn1 = sucNode qm
        let qn2, es = edgesC imps qn1 qs qn1 c1
        let qn3,es' = edgesC imps qn2 qn1 qf c2
        qn3, Set.union es es'
    | If gc -> edgesGC imps qm qs qf gc
    | Do gc -> 
        let qn, es = edgesGC imps qm qs qs gc
        qn, Set.add (qs,Tst (Neg (notDone gc)),imps,qf) es
and edgesGC imps qm qs qf gc =
    match gc with
    | Case (b,c) -> 
        let qn = sucNode qm
        let qn',es = edgesC (Set.union (freeVarsBool b) imps) qn qn qf c
        qn', Set.add (qs,Tst b,imps,qn) es
    | Choice (gc1,gc2) ->
        let qn,es = edgesGC imps qm qs qf gc1
        let qn',es' = edgesGC imps qn qs qf gc2
        qn', Set.union es es'