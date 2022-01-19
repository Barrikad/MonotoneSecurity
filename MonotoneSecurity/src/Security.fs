module Security
open AST
open ProgramGraph
open Algorithms
open Monotone
open Classification

let classificationBottom levelBottom classified freeVars=  
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

type violation<'level> =
    | Explicit of node * 'level * lit * node
    | Implicit of node * 'level * lit * node

let litViolations 
        levelLess levelJoin levelBottom litsToLevels 
        qs qf lit litLevel imps freeVars =
    let explicitLevel =
        freeVars
        |> litsToLevels
        |> joinMany levelJoin levelBottom
    let implicitLevel =
        litsToLevels imps
        |> joinMany levelJoin levelBottom
    ((
        if levelLess explicitLevel litLevel
        then Set []
        else Set [Explicit (qs,explicitLevel,lit,qf)]),
        if levelLess implicitLevel litLevel
        then Set []
        else Set [Implicit (qs,implicitLevel,lit,qf)]
    )
    ||> Set.union

let edgeViolations 
        levelLess levelJoin levelBottom classified 
        unclassified (qs,act,imps,qf) =
    let litsToLevels = Set.map (classifyLit classified unclassified)
    match act with
    | Skp 
    | Tst _ -> Set []
    | AsV (v,a) ->
        match Map.tryFind (Vr v) unclassified with
        | Some _ -> Set []
        | None -> 
            litViolations 
                levelLess levelJoin levelBottom litsToLevels 
                qs qf (Vr v) (Map.find (Vr v) classified) imps
                (freeVarsArtm a)
    | AsA (v,a1,a2) ->
        match Map.tryFind (Ar v) unclassified with
        | Some _ -> Set []
        | None -> 
            litViolations 
                levelLess levelJoin levelBottom litsToLevels 
                qs qf (Ar v) (Map.find (Ar v) classified) imps
                (Set.union (freeVarsArtm a1) (freeVarsArtm a2))

let pgViolations 
        levelLess levelJoin levelBottom classified unclassifiedMap pg =
    ()