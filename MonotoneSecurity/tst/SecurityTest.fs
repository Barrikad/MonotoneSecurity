module SecurityTest
open AST
open Algorithms
open Security
open Xunit
open ClassificationTest

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

[<Fact>]
let ``Security.edgeViolations Test 6`` () =
    Assert.Equal<Set<violation<level>>>(
        Set [
            Explicit (Start,Top,Ar 2u,Finish);
            Implicit (Start,Mid1,Ar 2u,Finish)
        ],
        edgeViolations2 (Start,AsA (2u,Var 3u,Num 1),Set [Vr 1u],Finish)
    )