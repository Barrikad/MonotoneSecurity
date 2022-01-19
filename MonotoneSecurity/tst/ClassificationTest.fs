module ClassificationTest
open AST
open Classification
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

let classified = Map [
    (Vr 0u,Bottom);(Vr 1u,Mid1);(Vr 2u,Mid2);(Vr 3u,Top);
    (Ar 0u,Bottom);(Ar 1u,Mid1);(Ar 2u,Mid2);(Ar 3u,Top);]

let unclassified = Map [
    (Vr 4u,Bottom);(Vr 5u,Mid1);(Vr 6u,Mid2);(Vr 7u,Top);
    (Ar 4u,Bottom);(Ar 5u,Mid1);(Ar 6u,Mid2);(Ar 7u,Top);]

[<Fact>]
let ``Classification.joinMany Test Empty`` () =
    Assert.Equal(Bottom,joinMany levelJoin Bottom Set.empty)

[<Fact>]
let ``Classification.joinMany Test Bottom, Mid1`` () =
    Assert.Equal(Mid1,joinMany levelJoin Bottom (Set [Bottom;Mid1]))

[<Fact>]
let ``Classification.joinMany Test Bottom, Mid1, Mid2`` () =
    Assert.Equal(Top,joinMany levelJoin Bottom (Set [Bottom;Mid1;Mid2]))

[<Fact>]
let ``Classification.classifier Test Skp, No Change`` () =
    Assert.Equal<Map<lit,level>>(
        unclassified,
        classifier 
            levelJoin Bottom classified unclassified (Start,Skp,Set [],Finish)
    )

[<Fact>]
let ``Classification.classifier Test Tst, No Change`` () =
    Assert.Equal<Map<lit,level>>(
        unclassified,
        classifier 
            levelJoin Bottom classified unclassified (Start,Tst True,Set [],Finish)
    )

[<Fact>]
let ``Classification.classifier Test AsV Classified, No Change`` () =
    Assert.Equal<Map<lit,level>>(
        unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsV (0u,Plus (Var 0u,Var 1u)),Set [],Finish)
    )

[<Fact>]
let ``Classification.classifier Test AsV unclassified, No Imps`` () =
    Assert.Equal<Map<lit,level>>(
        Map.add (Vr 4u) Mid1 unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsV (4u,Plus (Var 1u,Var 5u)),Set [],Finish)
    )

[<Fact>]
let ``Classification.classifier Test AsV unclassified, Some Imps`` () =
    Assert.Equal<Map<lit,level>>(
        Map.add (Vr 4u) Top unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsV (4u,Plus (Var 1u,Var 5u)),Set [Vr 6u],Finish)
    )

[<Fact>]
let ``Classification.classifier Test AsA classified, No Change`` () =
    Assert.Equal<Map<lit,level>>(
        unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsA (0u,Num 2,Plus (Var 1u,Var 5u)),Set [Vr 6u],Finish)
    )
    
[<Fact>]
let ``Classification.classifier Test AsA unclassified, No Imps 1`` () =
    Assert.Equal<Map<lit,level>>(
        Map.add (Ar 4u) Mid1 unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsA (4u,Num 2,Plus (Var 1u,Var 5u)),Set [],Finish))
            