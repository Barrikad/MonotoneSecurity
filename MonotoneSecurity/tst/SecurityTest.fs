module SecurityTest
open AST
open Algorithms
open Security
open Xunit
open Lattices

let classified = Map [
    (Vr 0u,Bottom);(Vr 1u,Mid1);(Vr 2u,Mid2);(Vr 3u,Top);
    (Ar 0u,Bottom);(Ar 1u,Mid1);(Ar 2u,Mid2);(Ar 3u,Top);]

let freeVars = Set [
    Vr 0u;Vr 1u;Vr 2u;Vr 3u;
    Ar 0u;Ar 1u;Ar 2u;Ar 3u;
    Vr 4u;Vr 5u;Vr 6u;Vr 7u;
    Ar 4u;Ar 5u;Ar 6u;Ar 7u]

let edgeViolations2 = 
    Classification.classificationBottom Bottom classified freeVars
    |> edgeViolations level1Less level1Join Bottom classified 

[<Fact>]
let ``Security.edgeViolations Test 1`` () =
    Assert.Equal<Set<violation<level1>>>(
        Set [],
        edgeViolations2 (Start,Skp,Set [],Finish)
    )

[<Fact>]
let ``Security.edgeViolations Test 2`` () =
    Assert.Equal<Set<violation<level1>>>(
        Set [],
        edgeViolations2 (Start,AsV (4u,Var 3u),Set [],Finish)
    )

[<Fact>]
let ``Security.edgeViolations Test 3`` () =
    Assert.Equal<Set<violation<level1>>>(
        Set [Explicit (Start,Top,Vr 2u,Finish)],
        edgeViolations2 (Start,AsV (2u,Var 3u),Set [],Finish)
    )

[<Fact>]
let ``Security.edgeViolations Test 4`` () =
    Assert.Equal<Set<violation<level1>>>(
        Set [Explicit (Start,Top,Vr 2u,Finish)],
        edgeViolations2 (Start,AsV (2u,Var 3u),Set [],Finish)
    )
    
[<Fact>]
let ``Security.edgeViolations Test 5`` () =
    Assert.Equal<Set<violation<level1>>>(
        Set [
            Explicit (Start,Top,Vr 2u,Finish);
            Implicit (Start,Mid1,Vr 2u,Finish)
        ],
        edgeViolations2 (Start,AsV (2u,Var 3u),Set [Vr 1u],Finish)
    )    

[<Fact>]
let ``Security.edgeViolations Test 6`` () =
    Assert.Equal<Set<violation<level1>>>(
        Set [
            Explicit (Start,Top,Ar 2u,Finish);
            Implicit (Start,Mid1,Ar 2u,Finish)
        ],
        edgeViolations2 (Start,AsA (2u,Var 3u,Num 1),Set [Vr 1u],Finish)
    )


[<Fact>]
let ``Security.pgViolations Test 1`` () =
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
    let expected = Set [
        Implicit(Mid 4u, Mid1, Vr 0u, Mid 6u)
        Explicit(Mid 8u, Top, Vr 0u, Finish)
    ]
    let unclassifiedMap =
        Classification.classificationAnalysis 
            Stack level1Join Bottom classified freeVars pg
    Assert.Equal<Set<violation<level1>>>(
        expected,
        pgViolations level1Less level1Join Bottom classified unclassifiedMap pg
    )

let equalIgnoreNodes vio1 vio2 =
    match vio1, vio2 with
    | Implicit (_,v1,l1,_), Implicit (_,v2,l2,_)
    | Explicit (_,v1,l1,_), Explicit (_,v2,l2,_) -> v1 = v2 && l1 = l2
    | _ -> false

[<Fact>]
let ``Security.astViolations Test No Vios`` () = 
    let ast = 
        Sequence (
            If (
                Case(
                    Equal (
                        Var 0u,
                        Num 2
                    ),
                    Skip
                )
            ),
            Skip
        )
    let expected = Set []
    let actual = 
        astViolations Stack level1Less level1Join Bottom classified freeVars ast
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) expected)
            actual
    )
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) actual)
            expected
    )

[<Fact>]
let ``Security.astViolations Test Explicit Vio`` () = 
    let ast = 
        Sequence (
            If (
                Case(
                    Equal (
                        Var 0u,
                        Num 2
                    ),
                    AssignV (0u,Var 1u)
                )
            ),
            Skip
        )
    let expected = Set [Explicit (Start,Mid1,Vr 0u,Finish)]
    let actual = 
        astViolations Stack level1Less level1Join Bottom classified freeVars ast
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) expected)
            actual
    )
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) actual)
            expected
    )

[<Fact>]
let ``Security.astViolations Test Implicit Vio`` () = 
    let ast = 
        Sequence (
            If (
                Case(
                    Equal (
                        Var 1u,
                        Num 2
                    ),
                    AssignV (0u,Num 1)
                )
            ),
            Skip
        )
    let expected = Set [Implicit (Start,Mid1,Vr 0u,Finish)]
    let actual = 
        astViolations Stack level1Less level1Join Bottom classified freeVars ast
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) expected)
            actual
    )
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) actual)
            expected
    )

[<Fact>]
let ``Security.astViolations Test No Implicit Vio`` () = 
    let ast = 
        Sequence (
            If (
                Case(
                    Equal (
                        Var 1u,
                        Num 2
                    ),
                    Skip
                )
            ),
            AssignV (0u,Num 1)
        )
    let expected = Set []
    let actual = 
        astViolations Stack level1Less level1Join Bottom classified freeVars ast
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) expected)
            actual
    )
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) actual)
            expected
    )

[<Fact>]
let ``Security.astViolations Test Array Violation`` () = 
    let ast = 
        Sequence (
            AssignA (5u,Num 1,Var 3u),
            Sequence(
                AssignA (5u,Num 2,Var 0u),
                AssignV (0u,Arr (5u,Num 1))
            )
        )
    let expected = Set [Explicit(Start,Top,Vr 0u,Finish)]
    let actual = 
        astViolations Stack level1Less level1Join Bottom classified freeVars ast
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) expected)
            actual
    )
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) actual)
            expected
    )

[<Fact>]
let ``Security.astViolations Test Loop Violation Explicit`` () = 
    let ast = 
        Sequence (
            Do (
                Case (
                    Equal (
                        Var 3u,
                        Num 1
                    ),
                    AssignV (4u,Num 1)
                )
            ),
            AssignV (0u,Var 4u)
        )
    let expected = Set [Explicit(Start,Top,Vr 0u,Finish)]
    let actual = 
        astViolations Stack level1Less level1Join Bottom classified freeVars ast
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) expected)
            actual
    )
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) actual)
            expected
    )

[<Fact>]
let ``Security.astViolations Test Loop Violation Implicit`` () = 
    let ast = 
        Sequence (
            Do (
                Case (
                    Equal (
                        Var 3u,
                        Num 1
                    ),
                    AssignV (1u,Num 1)
                )
            ),
            AssignV (0u,Num 1)
        )
    let expected = Set [Implicit(Start,Top,Vr 1u,Finish)]
    let actual = 
        astViolations Stack level1Less level1Join Bottom classified freeVars ast
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) expected)
            actual
    )
    Assert.True(
        Set.forall 
            (fun vio1 -> 
                Set.exists (fun vio2 -> equalIgnoreNodes vio1 vio2) actual)
            expected
    )