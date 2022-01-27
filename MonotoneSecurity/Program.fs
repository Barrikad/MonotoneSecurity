open System
open AST
open ProgramGraph
open Algorithms
open Classification
open Security
open Lattices


let levelLess = level1Less
let levelJoin = level1Join
let levelBottom = Bottom

let classified = Map [
    (Vr 0u,Bottom);(Vr 1u,Mid1);(Vr 2u,Mid2);(Vr 3u,Top)
    (Ar 0u,Bottom);(Ar 1u,Mid1);(Ar 2u,Mid2);(Ar 3u,Top)]

let freeVars = Set [
    Vr 0u;Vr 1u;Vr 2u;Vr 3u
    Ar 0u;Ar 1u;Ar 2u;Ar 3u
    Vr 4u;Vr 5u;Vr 6u;Vr 7u
    Ar 4u;Ar 5u;Ar 6u;Ar 7u]

let ast = 
    Sequence (
        If (
            Case(
                Equal (
                    Var 3u,
                    Num 2
                ),
                AssignV (4u,Num 1)
            )
        ),
        AssignV (0u, Var 4u)
    )

[<EntryPoint>]
let main argv =
    let pg = snd (edgesC Set.empty Start Start Finish ast)
    printfn "---------AST ---------"
    printfn "%A" ast
    printfn "----------------------"
    printfn ""
    printfn "----------PG----------"
    printfn "%A" pg
    printfn "----------------------"
    printfn ""
    printfn "----CLASSIFICATION----"
    classificationAnalysis Stack levelJoin levelBottom classified freeVars pg
    |> printfn "%A"
    printfn "----------------------"
    printfn ""
    printfn "------VIOLATIONS------"
    astViolations Stack levelLess levelJoin levelBottom classified freeVars ast
    |> printfn "%A"
    printfn "----------------------"
    0 // return an integer exit code