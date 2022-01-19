module SecurityTest
open AST
open Algorithms
open Security
open Xunit

type level =
    | Bottom
    | Mid1
    | Mid2
    | Top

let levelJoin l1 l2 =
    match l1, l2 with
    | Bottom, l
    | l, Bottom -> l
    | Top, _
    | _, Top -> Top
    | _ when l1 = l2 -> l1
    | _ -> Top

let levelLess l1 l2 =
    match l1, l2 with
    | Bottom,_ -> true
    | _,Top -> true
    | _ when l1 = l2 -> true
    | _ -> false

let classified = Map [
    (Vr 0u,Bottom);(Vr 1u,Mid1);(Vr 2u,Mid2);(Vr 3u,Top);
    (Ar 0u,Bottom);(Ar 1u,Mid1);(Ar 2u,Mid2);(Ar 3u,Top);]

let freeVars = Set [
    Vr 0u;Vr 1u;Vr 2u;Vr 3u;
    Ar 0u;Ar 1u;Ar 2u;Ar 3u;
    Vr 4u;Vr 5u;Vr 6u;Vr 7u;
    Ar 4u;Ar 5u;Ar 6u;Ar 7u]


let unclassified = classificationBottom Bottom classified freeVars

[<Fact>]
let ``Security.classificationBottom Test`` () =
    Assert.Equal<Map<lit,level>>(
        Map.map (fun k _ -> Bottom) ClassificationTest.unclassified,
        classificationBottom Bottom classified freeVars
    )

[<Fact>]
let ``Security.classificationAnalysis Test 1`` () =
    let pg = Set [
        (Start,Skp,Set [],Mid 1u)
        (Mid 1u, AsV (4u,Var 1u),Set [],Mid 2u)
        (Mid 2u, Skp, Set [], Mid 3u)
        (Mid 3u, Tst (Less (Var 4u,Num 0)), Set [], Mid 4u)
        (Mid 3u, Tst (Less (Num -1,Var 4u)), Set [], Mid 5u)
        (Mid 4u, AsV (0u,Num 1), Set [Vr 4u], Mid 6u)
        (Mid 5u, AsA (4u,Var 1u,Var 0u), Set [Vr 4u], Mid 6u)
        (Mid 6u, Tst (Equal (Num 1, Var 7u)), Set [], Mid 7u)
        (Mid 7u, AsA (4u,Var 2u,Num 1), Set [Vr 7u], Mid 6u)
        (Mid 6u, Tst (Neg (Equal (Num 1, Var 7u))), Set [], Mid 8u)
        (Mid 8u, AsV (0u,Arr (4u, Num 2)), Set [], Finish)
    ]
    let expected = Map [
        (Start, unclassified)
        (Mid 1u, unclassified)
        (Mid 2u, Map.add (Vr 4u) Mid1 unclassified)
        (Mid 3u, Map.add (Vr 4u) Mid1 unclassified)
        (Mid 4u, Map.add (Vr 4u) Mid1 unclassified)
        (Mid 5u, Map.add (Vr 4u) Mid1 unclassified)
        (Mid 6u, Map.add (Ar 4u) Top (Map.add (Vr 4u) Mid1 unclassified))
        (Mid 7u, Map.add (Ar 4u) Top (Map.add (Vr 4u) Mid1 unclassified))
        (Mid 8u, Map.add (Ar 4u) Top (Map.add (Vr 4u) Mid1 unclassified))
        (Finish, Map.add (Ar 4u) Top (Map.add (Vr 4u) Mid1 unclassified))
    ]
    Assert.Equal<Map<node,Map<lit,level>>>(
        expected,
        classificationAnalysis Stack levelJoin Bottom classified freeVars pg
    )

let edgeViolations2 = 
    edgeViolations levelLess levelJoin Bottom classified unclassified 

[<Fact>]
let ``Security.edgeViolations Test 1`` () =
    Assert.Equal<Set<violation<level>>>(
        Set [],
        edgeViolations2 (Start,Skp,Set [],Finish)
    )

[<Fact>]
let ``Security.edgeViolations Test 2`` () =
    Assert.Equal<Set<violation<level>>>(
        Set [],
        edgeViolations2 (Start,AsV (4u,Var 3u),Set [],Finish)
    )

[<Fact>]
let ``Security.edgeViolations Test 3`` () =
    Assert.Equal<Set<violation<level>>>(
        Set [Explicit (Start,Top,Vr 2u,Finish)],
        edgeViolations2 (Start,AsV (2u,Var 3u),Set [],Finish)
    )

[<Fact>]
let ``Security.edgeViolations Test 4`` () =
    Assert.Equal<Set<violation<level>>>(
        Set [Explicit (Start,Top,Vr 2u,Finish)],
        edgeViolations2 (Start,AsV (2u,Var 3u),Set [],Finish)
    )
    
[<Fact>]
let ``Security.edgeViolations Test 5`` () =
    Assert.Equal<Set<violation<level>>>(
        Set [
            Explicit (Start,Top,Vr 2u,Finish);
            Implicit (Start,Mid1,Vr 2u,Finish)
        ],
        edgeViolations2 (Start,AsV (2u,Var 3u),Set [Vr 1u],Finish)
    )