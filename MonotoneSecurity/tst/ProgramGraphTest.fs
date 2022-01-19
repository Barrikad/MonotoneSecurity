module ProgramGraphTest
open AST
open ProgramGraph
open Xunit

[<Fact>]
let ``ProgramGraph.edgesC Test Individual Coms`` () =
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,Skp,Set.empty,Finish)],
        edgesC Set.empty Start Start Finish Skip 
        |> snd)
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,AsV (1u, Num 0),Set.empty,Finish)],
        edgesC Set.empty Start Start Finish (AssignV (1u, (Num 0))) 
        |> snd)
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,AsA (1u, Num 0, Num 0),Set.empty,Finish)],
        edgesC Set.empty Start Start Finish (AssignA (1u, Num 0, Num 0)) 
        |> snd)


[<Fact>]
let ``ProgramGraph.edgesC Test Sequence`` () =
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,Skp,Set.empty,Mid 0u);(Mid 0u,Skp,Set.empty,Finish)],
        edgesC Set.empty Start Start Finish (Sequence (Skip,Skip)) 
        |> snd)

[<Fact>]
let ``ProgramGraph.edgesGC Test Case`` () =
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,Tst True,Set.empty,Mid 0u);(Mid 0u,Skp,Set.empty,Finish)],
        edgesGC Set.empty Start Start Finish (Case (True,Skip)) 
        |> snd)

[<Fact>]
let ``ProgramGraph.edgesGC Test Choice`` () =
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,Tst True,Set.empty,Mid 0u);(Mid 0u,Skp,Set.empty,Finish);
            (Start,Tst True,Set.empty,Mid 1u);(Mid 1u,Skp,Set.empty,Finish)],
        edgesGC Set.empty Start Start Finish (Choice (Case (True,Skip),Case (True,Skip))) 
        |> snd)

[<Fact>]
let ``ProgramGraph.edgesC Test If`` () =
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,Tst True,Set.empty,Mid 0u);(Mid 0u,Skp,Set.empty,Finish);
            (Start,Tst True,Set.empty,Mid 1u);(Mid 1u,Skp,Set.empty,Finish)],
        edgesC Set.empty Start Start Finish (If (Choice (Case (True,Skip),Case (True,Skip))))
        |> snd)

[<Fact>]
let ``ProgramGraph.edgesC Test Do`` () =
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,Tst True,Set.empty,Mid 0u);(Mid 0u,Skp,Set.empty,Start);
            (Start,Tst (Neg True),Set.empty,Finish)],
        edgesC Set.empty Start Start Finish (Do (Case (True,Skip)))
        |> snd)

[<Fact>]
let ``ProgramGraph.edgesC Test Implicits Are Added`` () =
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,Tst (Equal (Var 0u,Num 0)),Set.empty,Mid 0u);(Mid 0u,Skp,Set [Vr 0u],Finish);
            (Start,Tst (Equal (Var 1u,Num 0)),Set.empty,Mid 1u);(Mid 1u,Skp,Set [Vr 1u],Finish)],
        edgesC Set.empty Start Start Finish (
            If (
                Choice (
                    Case (Equal (Var 0u,Num 0),Skip),
                    Case (Equal (Var 1u,Num 0),Skip))))
        |> snd)

[<Fact>]
let ``ProgramGraph.edgesC Test Implicits Are Ended`` () =
    Assert.Equal<Set<node*action*(lit Set)*node>>(
        Set [(Start,Tst (Equal (Var 0u,Num 0)),Set.empty,Mid 1u);(Mid 1u,Skp,Set [Vr 0u],Mid 0u);
            (Start,Tst (Equal (Var 1u,Num 0)),Set.empty,Mid 2u);(Mid 2u,Skp,Set [Vr 1u],Mid 0u);
            (Mid 0u,AsV (0u,Num 1),Set.empty,Finish)],
        edgesC Set.empty Start Start Finish (
            Sequence (
                If (
                    Choice (
                        Case (Equal (Var 0u,Num 0),Skip),
                        Case (Equal (Var 1u,Num 0),Skip))),
                AssignV (0u,Num 1)))
        |> snd)