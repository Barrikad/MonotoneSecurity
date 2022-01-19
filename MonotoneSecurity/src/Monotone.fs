module Monotone

open AST
open Algorithms

let startNodes pg = Set.map (fun (q,_,_,_) -> q) pg

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

let standardAnalysis algorithmType join analysisFun bottom startAssignment pg =
    let algorithm = 
        Set.fold (fun a q -> insert q a) (empty algorithmType) (startNodes pg)
    let analysis = 
        Set.fold 
            (fun anls (qs,_,_,qf) -> Map.add qs bottom (Map.add qf bottom anls))
            Map.empty
            pg
        |> Map.add Start startAssignment
    fst (analyze join analysisFun pg (analysis,algorithm))