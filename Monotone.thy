theory Monotone imports Main HOL.Option
begin
(*NOTES:
non-interference is hard with non-determinism, since you don't know that the same path will be chosen
consider changing commandeval to return set
might give problems with non-termination and side channels

*)

(*Option auxiliary*)
primrec map_foption where
  \<open>map_foption (Some f) op = map_option f op\<close> |
  \<open>map_foption None op = None\<close>

abbreviation \<open>bind_foption op f \<equiv> Option.bind f (Option.bind op)\<close>

lemma map_foption_none: \<open>f = None \<or> op = None \<Longrightarrow> map_foption f op = None\<close>
  by (metis map_foption.simps(1) map_foption.simps(2) option.exhaust_sel option.simps(8))

lemma map_foption_some: \<open>f = Some f' \<and> op = Some op' \<Longrightarrow> map_foption f op = Some (f' op')\<close>
  by simp

lemma map_foption2_equals_cases: \<open>
  map_foption (map_option f op1) op2 = (
  case (op1,op2) of 
    (None,_) \<Rightarrow> None
  | (_,None) \<Rightarrow> None
  | (Some v,Some w) \<Rightarrow> Some (f v w))\<close> 
  by (smt (verit) None_eq_map_option_iff is_none_simps(2) map_foption.simps(1) map_foption_none 
      old.prod.case option.case_eq_if option.simps(9) option.split_sel)
(*----------------*)


(*defining artm---*)
datatype artm 
  = Num int
  | Var nat
  | Arr nat artm
  | UMinus artm
  | Plus artm artm
  | Minus artm artm
  | Times artm artm
  | Divide artm artm
  | Modulo artm artm

fun artmEvaluate where
  \<open>artmEvaluate (\<sigma>,\<pi>) (Num i) = Some i\<close> |
  \<open>artmEvaluate (\<sigma>,\<pi>) (Var x) = \<sigma> x\<close> |
  \<open>artmEvaluate (\<sigma>,\<pi>) (Arr x a) = Option.bind (artmEvaluate (\<sigma>,\<pi>) a) (\<pi> x)\<close> |
  \<open>artmEvaluate (\<sigma>,\<pi>) (UMinus a) = map_option uminus (artmEvaluate (\<sigma>,\<pi>) a)\<close> |
  \<open>artmEvaluate (\<sigma>,\<pi>) (Plus a1 a2) = 
    map_foption (map_option plus (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close> |
  \<open>artmEvaluate (\<sigma>,\<pi>) (Minus a1 a2) = 
    map_foption (map_option minus (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close> |
  \<open>artmEvaluate (\<sigma>,\<pi>) (Times a1 a2) = 
    map_foption (map_option times (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close> |
  \<open>artmEvaluate (\<sigma>,\<pi>) (Divide a1 a2) = 
    map_foption (map_option divide (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close> |
  \<open>artmEvaluate (\<sigma>,\<pi>) (Modulo a1 a2) = 
    map_foption (map_option modulo (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close>

lemma artm_eval_some_implies_operation:
  \<open>artmEvaluate (\<sigma>,\<pi>) (Num i) = Some i\<close> (is \<open>?p1\<close>)
  \<open>artmEvaluate (\<sigma>,\<pi>) (Var x) = \<sigma> x\<close> (is \<open>?p2\<close>)
  \<open>artmEvaluate (\<sigma>,\<pi>) a = Some i \<Longrightarrow> artmEvaluate (\<sigma>,\<pi>) (Arr x a) = (\<pi> x i)\<close> (is \<open>?s3 \<Longrightarrow> ?p3\<close>)
  \<open>artmEvaluate (\<sigma>,\<pi>) a = Some i \<Longrightarrow> artmEvaluate (\<sigma>,\<pi>) (UMinus a) = Some (-i)\<close> (is \<open>?s4 \<Longrightarrow> ?p4\<close>)
  \<open>artmEvaluate (\<sigma>,\<pi>) a1 = Some i \<Longrightarrow> artmEvaluate (\<sigma>,\<pi>) a2 = Some j \<Longrightarrow>
    artmEvaluate (\<sigma>,\<pi>) (Plus a1 a2) = Some (i + j)\<close> (is \<open>?s51 \<Longrightarrow> ?s52 \<Longrightarrow> ?p5\<close>)
  \<open>artmEvaluate (\<sigma>,\<pi>) a1 = Some i \<Longrightarrow> artmEvaluate (\<sigma>,\<pi>) a2 = Some j \<Longrightarrow>
    artmEvaluate (\<sigma>,\<pi>) (Minus a1 a2) = Some (i - j)\<close> (is \<open>?s61 \<Longrightarrow> ?s62 \<Longrightarrow> ?p6\<close>)
  \<open>artmEvaluate (\<sigma>,\<pi>) a1 = Some i \<Longrightarrow> artmEvaluate (\<sigma>,\<pi>) a2 = Some j \<Longrightarrow>
    artmEvaluate (\<sigma>,\<pi>) (Times a1 a2) = Some (i * j)\<close>  (is \<open>?s71 \<Longrightarrow> ?s72 \<Longrightarrow> ?p7\<close>)
  \<open>artmEvaluate (\<sigma>,\<pi>) a1 = Some i \<Longrightarrow> artmEvaluate (\<sigma>,\<pi>) a2 = Some j \<Longrightarrow>
    artmEvaluate (\<sigma>,\<pi>) (Divide a1 a2) = Some (i div j)\<close> (is \<open>?s81 \<Longrightarrow> ?s82 \<Longrightarrow> ?p8\<close>)
  \<open>artmEvaluate (\<sigma>,\<pi>) a1 = Some i \<Longrightarrow> artmEvaluate (\<sigma>,\<pi>) a2 = Some j \<Longrightarrow>
    artmEvaluate (\<sigma>,\<pi>) (Modulo a1 a2) = Some (i mod j)\<close> (is \<open>?s91 \<Longrightarrow> ?s92 \<Longrightarrow> ?p9\<close>)
  by simp_all
(*----------------*)



(*defining bool---*)
datatype boolean
  = Tru
  | Neg boolean
  | Dis boolean boolean
  | Equal artm artm
  | Less artm artm

abbreviation \<open>Fals \<equiv> Neg Tru\<close>

abbreviation \<open>Con b1 b2 \<equiv> Neg (Dis (Neg b1) (Neg b2))\<close>

abbreviation \<open>LessEq a1 a2 \<equiv> Dis (Less a1 a2) (Equal a1 a2)\<close>

abbreviation \<open>NEqual a1 a2 \<equiv> Neg (Equal a1 a2)\<close>

fun booleanEvaluate where
  \<open>booleanEvaluate (\<sigma>,\<pi>) Tru = Some True\<close> |
  \<open>booleanEvaluate (\<sigma>,\<pi>) (Neg b) = map_option Not (booleanEvaluate (\<sigma>,\<pi>) b)\<close> |
  \<open>booleanEvaluate (\<sigma>,\<pi>) (Dis b1 b2) = 
    map_foption (map_option (\<or>) (booleanEvaluate (\<sigma>,\<pi>) b1)) (booleanEvaluate (\<sigma>,\<pi>) b2)\<close> |
  \<open>booleanEvaluate (\<sigma>,\<pi>) (Equal a1 a2) =
    map_foption (map_option (=) (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close> |
  \<open>booleanEvaluate (\<sigma>,\<pi>) (Less a1 a2) = 
    map_foption (map_option (<) (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close>

lemma EvaluateFals[simp]: \<open>booleanEvaluate (\<sigma>,\<pi>) Fals = Some False\<close>
  by simp

lemma EvaluateCon[simp]: \<open>booleanEvaluate (\<sigma>,\<pi>) (Con b1 b2) = 
    map_foption (map_option (\<and>) (booleanEvaluate (\<sigma>,\<pi>) b1)) (booleanEvaluate (\<sigma>,\<pi>) b2)\<close> 
  by (smt (z3) None_eq_map_option_iff booleanEvaluate.simps(2) booleanEvaluate.simps(3) 
      map_foption.simps(1) map_foption.simps(2) option.collapse option.map_sel)

lemma EvaluateLessEq[simp]: \<open>
  booleanEvaluate (\<sigma>,\<pi>) (LessEq a1 a2) =
  map_foption (map_option (\<le>) (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close> 
  (is \<open>?bol = ?artms\<close>) 
proof-
  consider (a1None) \<open>artmEvaluate (\<sigma>,\<pi>) a1 = None\<close> | (a1Some) \<open>\<exists> i. artmEvaluate (\<sigma>,\<pi>) a1 = Some i\<close>
    by auto
  then show \<open>?thesis\<close> 
  proof cases
    case a1None
    then show ?thesis 
      by simp
  next
    case a1Some
    consider \<open>artmEvaluate (\<sigma>,\<pi>) a2 = None\<close> | \<open>\<exists> j. artmEvaluate (\<sigma>,\<pi>) a2 = Some j\<close>
      by auto
    then show ?thesis
      by (smt (z3) a1Some booleanEvaluate.simps(3) booleanEvaluate.simps(4) booleanEvaluate.simps(5) 
          map_foption.simps(1) map_foption_none option.simps(9))
  qed
qed

lemma EvaluateNEqual[simp]: \<open>
  booleanEvaluate (\<sigma>,\<pi>) (NEqual a1 a2) =
  map_foption (map_option (\<noteq>) (artmEvaluate (\<sigma>,\<pi>) a1)) (artmEvaluate (\<sigma>,\<pi>) a2)\<close>
  (is \<open>?bol = ?artms\<close>)
proof-
  have \<open>artmEvaluate (\<sigma>,\<pi>) a1 = None \<or> (\<exists> i. artmEvaluate (\<sigma>,\<pi>) a1 = Some i)\<close>
    by auto
  moreover have \<open>artmEvaluate (\<sigma>,\<pi>) a2 = None \<or> (\<exists> j. artmEvaluate (\<sigma>,\<pi>) a2 = Some j)\<close>
    by auto
  ultimately show \<open>?thesis\<close> by fastforce
qed
(*----------------*)


(*defining coms---*)
datatype command 
  = Skip
  | AssignV nat artm
  | AssignA nat artm artm
  | Sequence command command
  | If gcommand
  | Do gcommand
and gcommand
  = Case boolean command
  | Choice gcommand gcommand

abbreviation \<open>evaluateIfTrue f mem i c b \<equiv> if b then f mem i c else None\<close>

primrec updateVar where \<open>updateVar x (\<sigma>,\<pi>) i = Some (\<sigma>(x := Some i), \<pi>)\<close>

primrec updateArr where \<open>updateArr x (\<sigma>,\<pi>) i j = Some (\<sigma>, \<pi>(x := ((\<pi> x) (i := Some j))))\<close>

(*scheme for termination:*)
context begin
private datatype c = A | F c | R c
private function f where
  \<open>f (i :: nat) A = A\<close> |
  \<open>f i (F c) = f i c\<close> |
  \<open>f i (R c) = (if i = 0 then A else f (i - 1) (R c))\<close> (*only check in non-termination step*)
  by pat_completeness auto
termination
  by (relation "measure (\<lambda> (i,c). i + size c)") simp_all (*both size of i and term*)
end
(*\scheme for termination*)

function commandEvaluate gcommandEvaluate where
  \<open>commandEvaluate (i :: nat) mem Skip = None\<close> |
  \<open>commandEvaluate i mem (AssignV x a) = 
    Option.bind (artmEvaluate mem a) (updateVar x mem)\<close> |
  \<open>commandEvaluate i mem (AssignA x a1 a2) = 
    bind_foption (artmEvaluate mem a2) (map_option (updateArr x mem) (artmEvaluate mem a1))\<close> |
  \<open>commandEvaluate i mem (Sequence c1 c2) = (
    case commandEvaluate i mem c1 of
      None \<Rightarrow> None
    | Some mem' \<Rightarrow> commandEvaluate i mem' c2)\<close> |
  \<open>commandEvaluate i mem (If gc) = (
    case gcommandEvaluate i mem gc of
      None \<Rightarrow> None
    | Some mem' \<Rightarrow> mem')\<close> |
  \<open>commandEvaluate i mem (Do gc) = (
    if i > 0
    then
      case gcommandEvaluate i mem gc of
        None \<Rightarrow> None
      | Some None \<Rightarrow> Some mem
      | Some (Some mem') \<Rightarrow> commandEvaluate (i - 1) mem' (Do gc)
    else None)\<close> |
  \<open>gcommandEvaluate i mem (Case b c) = (
    case booleanEvaluate mem b of
      Some True \<Rightarrow> map_option Some (commandEvaluate i mem c)
    | Some False \<Rightarrow> Some None
    | None \<Rightarrow> None)\<close> |
  \<open>gcommandEvaluate i mem (Choice gc1 gc2) = (
    case (gcommandEvaluate i mem gc1, gcommandEvaluate i mem gc2) of
      (None, _) \<Rightarrow> None
    | (_,None) \<Rightarrow> None
    | (Some m, Some None) \<Rightarrow> Some m
    | (Some None, Some m) \<Rightarrow> Some m
    | (Some (Some m1), Some (Some m2)) \<Rightarrow> Some (Some (SOME m. m = m1 \<or> m = m2)))\<close>
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>x. case x of Inl (i,_,c) \<Rightarrow> i + size c | Inr (i,_,gc) \<Rightarrow> i + size gc)") 
    simp_all
(*----------------*)

(*manual verifying*)
context begin
private abbreviation \<open>factorial \<equiv> 
    Do (
      Case 
        (Less (Num 0) (Var 1)) 
        (Sequence 
          (AssignV 0 (Times (Var 0) (Var 1)))
          (AssignV 1 (Minus (Var 1) (Num 1)))))\<close>

(*pure isar proof that the program calculates the factorial when it succeeds:*)
private proposition \<open>
  \<sigma> 0 = Some m \<Longrightarrow>
  \<sigma> 1 = Some n \<Longrightarrow> 
  n \<ge> 0 \<Longrightarrow> 
  commandEvaluate i (\<sigma>,\<pi>) factorial = Some (\<sigma>',\<pi>') \<Longrightarrow> 
  \<sigma>' 0 = Some m' \<Longrightarrow>
  m' = m * fact (nat n)\<close>
proof (induct i arbitrary: \<sigma> \<pi> m n m')
  case 0
  then show ?case by simp
next
  let ?ass0 = \<open>AssignV 0 (Times (Var 0) (Var 1))\<close>
  let ?ass1 = \<open>AssignV 1 (Minus (Var 1) (Num 1))\<close>
  let ?test = \<open>Less (Num 0) (Var 1)\<close>
  let ?body = \<open>Sequence ?ass0 ?ass1\<close>
  let ?gc = \<open>Case ?test ?body\<close>
  case (Suc i)
  then have not_none1:\<open>None \<noteq> commandEvaluate (Suc i) (\<sigma>, \<pi>) factorial\<close>
    by (metis not_Some_eq)
  then have not_none2:\<open>None \<noteq>
    gcommandEvaluate (Suc i) (\<sigma>, \<pi>) ?gc\<close> by fastforce
  consider 
    \<open>booleanEvaluate (\<sigma>, \<pi>) ?test = Some True\<close> | 
    \<open>booleanEvaluate (\<sigma>, \<pi>) ?test = Some False\<close> 
    using Suc.prems(2) by fastforce
  then show ?case 
  proof cases
    case 1
    then have gcdef:\<open>
      gcommandEvaluate (Suc i) (\<sigma>, \<pi>) ?gc =
      map_option Some (commandEvaluate (Suc i) (\<sigma>, \<pi>) ?body)\<close> 
      by (smt (verit) gcommandEvaluate.simps(1) option.simps(5))
    then have not_none11: \<open>None \<noteq> commandEvaluate (Suc i) (\<sigma>, \<pi>) ?body\<close> 
      using not_none2 by fastforce
    have not_none12: \<open>None \<noteq> commandEvaluate (Suc i) (\<sigma>, \<pi>) ?ass0\<close> 
    proof (rule ccontr)
      assume \<open>\<not>(None \<noteq> commandEvaluate (Suc i) (\<sigma>, \<pi>) ?ass0)\<close>
      then have \<open>commandEvaluate (Suc i) (\<sigma>, \<pi>) ?body = None\<close> by simp
      then show False using not_none11 by simp
    qed
    then obtain tms where  tms_def:
      \<open>artmEvaluate (\<sigma>, \<pi>) (Times (Var 0) (Var 1)) = Some tms \<and> tms = m * n\<close> 
      using Suc.prems by fastforce
    then have bodydef:
      \<open>commandEvaluate (Suc i) (\<sigma>, \<pi>) ?body = commandEvaluate (Suc i) (\<sigma>(0 := Some tms), \<pi>) ?ass1\<close> 
      using not_none11 by auto
    then have not_none13: \<open>None \<noteq> commandEvaluate (Suc i) (\<sigma>(0 := Some tms), \<pi>) ?ass1\<close>
      using not_none11 by auto
    then have mns_def:
      \<open>artmEvaluate (\<sigma>(0 := Some tms), \<pi>) (Minus (Var 1) (Num 1)) = Some (n - 1)\<close> 
      using Suc.prems by fastforce
    then have \<open>commandEvaluate (Suc i) (\<sigma>, \<pi>) ?body = Some (\<sigma>(0 := Some tms,1 := Some (n - 1)), \<pi>)\<close> 
      using not_none11 bodydef by auto
    then have   
      \<open>gcommandEvaluate (Suc i) (\<sigma>, \<pi>) ?gc = Some (Some (\<sigma>(0 := Some tms,1 := Some (n - 1)), \<pi>))\<close>
      using gcdef by simp
    then have \<open>
      commandEvaluate (Suc i) (\<sigma>, \<pi>) factorial = 
      commandEvaluate i (\<sigma>(0 := Some tms,1 := Some (n - 1)), \<pi>) factorial\<close> 
      by simp
    moreover have mns_grt_0:\<open>(n - 1) \<ge> 0\<close> using 1 mns_def by auto
    ultimately have
      \<open>commandEvaluate i (\<sigma>(0 := Some tms,1 := Some (n - 1)), \<pi>) factorial = 
      Some (\<sigma>',\<pi>') \<and> \<sigma>' 0 = Some m' \<and> m' = tms * fact (nat (n - 1))\<close> 
      by (metis (no_types, lifting) Suc.hyps Suc.prems(4) 
          Suc.prems(5) fun_upd_other fun_upd_same zero_neq_one)
    then have \<open>m' = m * n * fact (nat (n - 1))\<close> 
      by (simp add: mns_def tms_def)
    moreover have \<open>n * fact (nat (n - 1)) = fact (nat n)\<close> using mns_grt_0 mns_def 
      by (simp add: fact_num_eq_if nat_diff_distrib)
    ultimately show ?thesis
      by simp
  next
    case 2
    then have \<open>gcommandEvaluate (Suc i) (\<sigma>, \<pi>) ?gc = Some None\<close> 
      by (smt (verit) gcommandEvaluate.simps(1) option.simps(5))
    then have \<open>commandEvaluate (Suc i) (\<sigma>, \<pi>) factorial = Some (\<sigma>, \<pi>)\<close> 
      by simp
    moreover have \<open>\<sigma> 1 = Some 0\<close> 
      using 2 Suc.prems by simp
    ultimately show ?thesis 
      using Suc.prems(1) Suc.prems(2) Suc.prems(4) Suc.prems(5) by auto
  qed
qed

private abbreviation \<open>non_deterministic \<equiv> 
  If (Choice 
    (Case 
      (Equal (Var 0) (Num 0)) 
      (AssignV 0 (Num 1))) 
    (Case 
      (Equal (Var 1) (Num 0)) 
      (AssignV 1 (Num 1))))\<close>

private proposition \<open>
  commandEvaluate i mem non_deterministic = Some mem' \<Longrightarrow>
  ((fst mem) 0 = Some 0 \<and> (fst mem') 0 = Some 1) \<or> ((fst mem) 1 = Some 0 \<and> (fst mem') 1 = Some 1)\<close>
  (is \<open>?asm \<Longrightarrow> ?ex0 \<or> ?ex1\<close>)
proof-
  let ?ass0 = \<open>AssignV 0 (Num 1)\<close>
  let ?ass1 = \<open>AssignV 1 (Num 1)\<close>
  let ?tst0 = \<open>Equal (Var 0) (Num 0)\<close>
  let ?tst1 = \<open>Equal (Var 1) (Num 0)\<close>
  let ?cse0 = \<open>Case ?tst0 ?ass0\<close>
  let ?cse1 = \<open>Case ?tst1 ?ass1\<close>
  let ?gc = \<open>Choice ?cse0 ?cse1\<close>
  let ?gc_pair = \<open>(gcommandEvaluate i mem ?cse0, gcommandEvaluate i mem ?cse1)\<close>
  assume a:\<open>?asm\<close>
  have gcom_some: \<open>gcommandEvaluate i mem ?gc = Some (Some mem')\<close>
  proof-
    consider 
      \<open>\<exists> mem_x. gcommandEvaluate i mem ?gc = Some (Some mem_x)\<close> | 
      \<open>gcommandEvaluate i mem ?gc = Some None\<close> |
      \<open>gcommandEvaluate i mem ?gc = None\<close> by fastforce
    then show ?thesis
    proof cases
      case 1
      then obtain mem_x where mem_x_def:\<open>gcommandEvaluate i mem ?gc = Some (Some mem_x)\<close> by auto
      then have \<open>mem_x = mem'\<close> using a by auto
      then show ?thesis using mem_x_def by blast
    next
      case 2
      then show ?thesis using a by simp
    next
      case 3
      then show ?thesis using a by simp
    qed
  qed
  have ex0: \<open>gcommandEvaluate i mem ?cse0 = Some (Some mem') \<Longrightarrow> ?ex0\<close>
  proof-
    assume a2:\<open>gcommandEvaluate i mem ?cse0 = Some (Some mem')\<close>
    have tst0_some:\<open>booleanEvaluate mem ?tst0 = Some True\<close>
    proof (rule ccontr)
      assume \<open>booleanEvaluate mem ?tst0 \<noteq> Some True\<close>
      then have \<open>booleanEvaluate mem ?tst0 = Some False \<or> booleanEvaluate mem ?tst0 = None\<close> by auto
      then show False using a2 by auto
    qed
    have num_0_is_0:\<open>artmEvaluate mem (Num 0) = Some 0\<close>
      by (metis artmEvaluate.simps(1) old.prod.exhaust)
    moreover have \<open>artmEvaluate mem (Var 0) = artmEvaluate mem (Num 0)\<close>
    proof-
      have \<open>artmEvaluate mem (Var 0) \<noteq> None\<close> 
        using tst0_some by (metis None_eq_map_option_iff booleanEvaluate.simps(4) 
            map_foption.simps(2) old.prod.exhaust option.discI)
      then show ?thesis 
        using tst0_some num_0_is_0 
        by (smt (verit, best) booleanEvaluate.simps(4) map_foption_some old.prod.exhaust 
            option.collapse option.sel option.simps(9))
    qed
    ultimately have part1:\<open>(fst mem) 0 = Some 0\<close>
      by (metis artmEvaluate.simps(2) prod.exhaust_sel)
    have num_1_is_1: \<open>artmEvaluate mem (Num 1) = Some 1\<close>
      by (metis artmEvaluate.simps(1) surj_pair)
    moreover have \<open>commandEvaluate i mem ?ass0 = Some (mem')\<close> using a2 tst0_some by auto
    ultimately have \<open>fst mem' = (fst mem)(0 := Some 1)\<close> 
      by (metis (mono_tags, lifting) bind.bind_lunit commandEvaluate.simps(2) eq_fst_iff 
          option.inject updateVar.simps)
    then show ?thesis using part1 by simp
  qed
  have ex1: \<open>gcommandEvaluate i mem ?cse1 = Some (Some mem') \<Longrightarrow> ?ex1\<close>sorry
  consider 
    \<open>\<exists> x. ?gc_pair = (None,x)\<close> |
    \<open>\<exists> x. ?gc_pair = (x,None)\<close> |
    \<open>?gc_pair = (Some None,Some None)\<close> |
    \<open>\<exists> mem_x. 
       ?gc_pair = (Some (Some mem_x),Some None)\<close> |
    \<open>\<exists> mem_x. 
      ?gc_pair = (Some None,Some (Some mem_x))\<close> |
    \<open>\<exists> mem_x mem_y. 
      ?gc_pair = (Some (Some mem_x),Some (Some mem_y))\<close> 
    by force
  then show \<open>?ex0 \<or> ?ex1\<close>
  proof cases
    case 1
    then have \<open>False\<close> using gcom_some by simp
    then show ?thesis ..
  next
    case 2
    then have \<open>False\<close> 
      using gcom_some by (metis (no_types, lifting) case_prod_conv gcommandEvaluate.simps(2) 
          option.case_eq_if option.distinct(1))
    then show ?thesis ..
  next
    case 3
    then have \<open>False\<close> using gcom_some by simp
    then show ?thesis ..
  next
    case 4
    then show ?thesis using ex0 a by auto
  next
    case 5
    then show ?thesis using ex1 a by auto
  next
    case 6
    then show ?thesis sorry
  qed
qed
end
(*----------------*)


(*graph auxiliary-*)
fun is_path where
  empty_path: \<open>is_path graph start end [] = (start = end)\<close> |
  extend_path: \<open>
    is_path graph start end ((s,a,e) # path) = 
    (s = start \<and> (s,a,e) \<in> graph \<and> is_path graph e end path)\<close>
(*----------------*)


(*program graphs--*)
datatype node 
  = Start
  | Mid nat
  | Finish

primrec sucNode where
  \<open>sucNode Start = Mid 0\<close> |
  \<open>sucNode (Mid i) = Mid (i + 1)\<close> |
  \<open>sucNode Finish = Finish\<close>

datatype action
  = Skp
  | Tst boolean
  | AsV nat artm
  | AsA nat artm artm

primrec not_done where
  \<open>not_done (Case b _) = b\<close> |
  \<open>not_done (Choice gc1 gc2) = (Dis (not_done gc1) (not_done gc2))\<close>

lemma 
  \<open>booleanEvaluate mem (not_done gc) = Some False \<Longrightarrow> gcommandEvaluate i mem gc = Some None\<close>
proof (induct gc)
case Skip
  then show ?thesis sorry
next
  case (AssignV x1 x2)
  then show ?thesis sorry
next
  case (AssignA x1 x2 x3)
  then show ?thesis sorry
next
  case (If gc)
  then show ?thesis sorry
next
  case (Do gc)
  then show ?thesis sorry
next
  fix x1 x2
  assume \<open>gcommandEvaluate i mem gc = Some None\<close>
  assume \<open>booleanEvaluate mem (not_done (Case x1 x2)) = Some False\<close>
  then show \<open>gcommandEvaluate i mem (Case x1 x2) = Some None\<close> sorry
next
  case (Choice gc1 gc2)
  then show ?case sorry
qed auto

fun edgesC edgesGC where
  \<open>edgesC maxnode snode fnode Skip = (maxnode,{(snode,Skp,fnode)})\<close> |
  \<open>edgesC maxnode snode fnode (AssignV x a) = (maxnode,{(snode,AsV x a,fnode)})\<close> |
  \<open>edgesC maxnode snode fnode (AssignA x a1 a2) = (maxnode,{(snode,AsA x a1 a2,fnode)})\<close> |
  \<open>edgesC maxnode snode fnode (Sequence c1 c2) = (
    let 
      nnode = sucNode maxnode;
      (mnode,es) = edgesC nnode snode nnode c1;
      (mnode',es') = edgesC mnode nnode fnode c2 in
    (mnode',es \<union> es'))\<close> |
  \<open>edgesC maxnode snode fnode (If gc) = edgesGC maxnode snode fnode gc\<close> |
  \<open>edgesC maxnode snode fnode (Do gc) = (
    let (mnode,es) = edgesGC maxnode snode snode gc in
    (mnode,es \<union> {(snode,Tst (Neg (not_done gc)),fnode)}))\<close> |
  \<open>edgesGC maxnode snode fnode (Case b c) = (
    let
      nnode = sucNode maxnode;
      (mnode,es) = edgesC nnode nnode fnode c in
    (mnode,es \<union> {(snode,Tst b,nnode)}))\<close> |
  \<open>edgesGC maxnode snode fnode (Choice gc1 gc2) = (
    let 
      (mnode,es) = edgesGC maxnode snode fnode gc1;
      (mnode',es') = edgesGC mnode snode fnode gc2 in
    (mnode',es \<union> es'))\<close>


(*----------------*)
end