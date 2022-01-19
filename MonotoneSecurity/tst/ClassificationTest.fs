module ClassificationTest
open AST
open Classification
open Xunit
open Algorithms

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
let ``Classification.classifier Test AsA unclassified, a2 is counted`` () =
    Assert.Equal<Map<lit,level>>(
        Map.add (Ar 4u) Mid1 unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsA (4u,Num 2,Plus (Var 1u,Var 5u)),Set [],Finish))
            
[<Fact>]
let ``Classification.classifier Test AsA unclassified, a1 is counted`` () =
    Assert.Equal<Map<lit,level>>(
        Map.add (Ar 4u) Top unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsA (4u,Var 6u,Plus (Var 1u,Var 5u)),Set [],Finish))
            
[<Fact>]
let ``Classification.classifier Test AsA unclassified, imps are counted`` () =
    Assert.Equal<Map<lit,level>>(
        Map.add (Ar 4u) Top unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsA (4u,Num 6,Plus (Var 1u,Var 5u)),Set [Vr 6u],Finish))
            
[<Fact>]
let ``Classification.classifier Test AsA unclassified, previous is counted`` () =
    Assert.Equal<Map<lit,level>>(
        Map.add (Ar 6u) Top unclassified,
        classifier 
            levelJoin Bottom 
            classified unclassified 
            (Start,AsA (6u,Num 6,Plus (Var 1u,Var 5u)),Set [],Finish))


let freeVars = Set [
    Vr 0u;Vr 1u;Vr 2u;Vr 3u;
    Ar 0u;Ar 1u;Ar 2u;Ar 3u;
    Vr 4u;Vr 5u;Vr 6u;Vr 7u;
    Ar 4u;Ar 5u;Ar 6u;Ar 7u]

[<Fact>]
let ``Security.classificationBottom Test`` () =
    Assert.Equal<Map<lit,level>>(
        Map.map (fun k _ -> Bottom) unclassified,
        classificationBottom Bottom classified freeVars
    )

[<Fact>]
let ``Security.classificationAnalysis Test 1`` () =
    let classBottom = classificationBottom Bottom classified freeVars
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
        (Start, classBottom)
        (Mid 1u, classBottom)
        (Mid 2u, Map.add (Vr 4u) Mid1 classBottom)
        (Mid 3u, Map.add (Vr 4u) Mid1 classBottom)
        (Mid 4u, Map.add (Vr 4u) Mid1 classBottom)
        (Mid 5u, Map.add (Vr 4u) Mid1 classBottom)
        (Mid 6u, Map.add (Ar 4u) Top (Map.add (Vr 4u) Mid1 classBottom))
        (Mid 7u, Map.add (Ar 4u) Top (Map.add (Vr 4u) Mid1 classBottom))
        (Mid 8u, Map.add (Ar 4u) Top (Map.add (Vr 4u) Mid1 classBottom))
        (Finish, Map.add (Ar 4u) Top (Map.add (Vr 4u) Mid1 classBottom))
    ]
    Assert.Equal<Map<node,Map<lit,level>>>(
        expected,
        classificationAnalysis Stack levelJoin Bottom classified freeVars pg
    )