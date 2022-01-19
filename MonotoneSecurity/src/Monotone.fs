module Monotone

open AST
open Algorithms

let insert q = id

let extract a = Some (Start,a)

let empty = id

let analyzeEdge join analysisFun (analysis,algorithm) (qs,act,imps,qf) =
    let qfAssignment = Map.find qf analysis
    let analyzed = analysisFun (Map.find qs analysis) (qs,act,imps,qf)
    let joined = join qfAssignment analyzed
    if joined = qfAssignment
    then (analysis,algorithm)
    else (Map.add qf joined analysis,insert qf algorithm)

let rec analyze join analysisFun pg (analysis,algorithm) =
    match extract algorithm with
    | None -> (analysis,algorithm)
    | Some (q,algorithm') -> 
        Set.filter (fun (qs,_,_,_) -> qs = q) pg
        |> Set.fold (analyzeEdge join analysisFun) (analysis,algorithm')
        |> analyze join analysisFun pg

let standardAnalysis join analysisFun bottom startAssignment pg algorithmType =
    let algorithm = empty algorithmType
    let analysis = 
        Set.fold 
            (fun anls (qs,_,_,qf) -> Map.add qs bottom (Map.add qf bottom anls))
            Map.empty
            pg
        |> Map.add Start startAssignment
    fst (analyze join analysisFun pg (analysis,algorithm))