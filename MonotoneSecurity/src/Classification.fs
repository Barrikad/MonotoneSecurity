module Classification
open AST
open ProgramGraph
open Monotone

let classifyLit classified unclassified lit =
    match Map.tryFind lit classified with
    | Some l -> l
    | None -> Map.find lit unclassified

let joinMany join bottom xs = 
    Set.fold (fun x' x -> join x' x) bottom xs

let classificationJoin levelJoin c1 c2 =
    Map.map (fun v l -> levelJoin l (Map.find v c2)) c1

let classifier 
        levelJoin levelBottom classified unclassified (qs,act,imps,qf) = 
    let litsToLevels = Set.map (classifyLit classified unclassified)
    let joinManyLevels = joinMany levelJoin levelBottom
    match act with
    | Skp
    | Tst _ -> unclassified
    | AsV (v, a) -> 
        match Map.tryFind (Vr v) classified with
        | Some _ -> unclassified
        | None ->
            freeVarsArtm a
            |> Set.union imps
            |> litsToLevels
            |> joinManyLevels 
            |> Map.add (Vr v)
            <| unclassified
    | AsA (v, a1, a2) ->
        match Map.tryFind (Ar v) classified with
        | Some _ -> unclassified
        | None -> 
            freeVarsArtm a2
            |> Set.union (freeVarsArtm a1)
            |> Set.union imps
            |> litsToLevels
            |> joinManyLevels
            |> levelJoin (Map.find (Ar v) unclassified)
            |> Map.add (Ar v)
            <| unclassified

let classificationBottom levelBottom classified freeVars =  
    Map.toSeq classified
    |> Seq.map fst
    |> Set.ofSeq
    |> Set.difference freeVars
    |> Set.toSeq
    |> Seq.map (fun k -> (k,levelBottom))
    |> Map.ofSeq

let classificationAnalysis 
        algorithm levelJoin levelBottom classified freeVars pg =
    let analysisBottom = classificationBottom levelBottom classified freeVars 
    standardAnalysis
        algorithm 
        (classificationJoin levelJoin) 
        (classifier levelJoin levelBottom classified)
        analysisBottom
        analysisBottom
        pg