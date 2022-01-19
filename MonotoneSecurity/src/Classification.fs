module Classification
open AST
open ProgramGraph

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
    match act with
    | Skp
    | Tst _ -> unclassified
    | AsV (v, a) -> 
        match Map.tryFind (Vr v) classified with
        | Some _ -> unclassified
        | None ->
            Set.map (classifyLit classified unclassified) (freeVarsArtm a)
            |> Set.union (Set.map (classifyLit classified unclassified) imps)
            |> joinMany levelJoin levelBottom     
            |> Map.add (Vr v)
            <| unclassified
    | AsA (v, a1, a2) ->
        match Map.tryFind (Ar v) classified with
        | Some _ -> unclassified
        | None -> 
            Set.map (classifyLit classified unclassified) (freeVarsArtm a2)
            |> joinMany levelJoin levelBottom
            |> Map.add (Ar v)
            <| unclassified