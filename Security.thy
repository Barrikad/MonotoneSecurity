theory Security imports Main
begin

datatype ('a,'b) var
  = T1 'a
  | T2 'b

datatype ('c,'d) arr
  = T3 'c
  | T4 'd

datatype ('a,'b,'c,'d) artm
  = Num int
  | Var \<open>('a,'b) var\<close>
  | Arr \<open>('c,'d) arr\<close> \<open>('a,'b,'c,'d) artm\<close>
  | Plus \<open>('a,'b,'c,'d) artm\<close> \<open>('a,'b,'c,'d) artm\<close>
  | Minus \<open>('a,'b,'c,'d) artm\<close> \<open>('a,'b,'c,'d) artm\<close>
  | Times \<open>('a,'b,'c,'d) artm\<close> \<open>('a,'b,'c,'d) artm\<close>

fun evalArtm where
  \<open>evalArtm (\<sigma>,\<pi>) (Num i) = i\<close> |
  \<open>evalArtm (\<sigma>,\<pi>) (Var x) = \<sigma> x\<close> |
  \<open>evalArtm (\<sigma>,\<pi>) (Arr x a) = \<pi> x (evalArtm (\<sigma>,\<pi>) a)\<close> |
  \<open>evalArtm (\<sigma>,\<pi>) (Plus a1 a2) = (evalArtm (\<sigma>,\<pi>) a1) + (evalArtm (\<sigma>,\<pi>) a2)\<close> |
  \<open>evalArtm (\<sigma>,\<pi>) (Minus a1 a2) = (evalArtm (\<sigma>,\<pi>) a1) - (evalArtm (\<sigma>,\<pi>) a2)\<close> |
  \<open>evalArtm (\<sigma>,\<pi>) (Times a1 a2) = (evalArtm (\<sigma>,\<pi>) a1) * (evalArtm (\<sigma>,\<pi>) a2)\<close>

datatype ('a,'b,'c,'d) bool
  = Tru
  | Neg \<open>('a,'b,'c,'d) bool\<close>
  | Dis \<open>('a,'b,'c,'d) bool\<close> \<open>('a,'b,'c,'d) bool\<close>
  | Equal \<open>('a,'b,'c,'d) artm\<close> \<open>('a,'b,'c,'d) artm\<close>
  | Less \<open>('a,'b,'c,'d) artm\<close> \<open>('a,'b,'c,'d) artm\<close>

fun evalBool where
  \<open>evalBool (\<sigma>,\<pi>) Tru = True\<close> |
  \<open>evalBool (\<sigma>,\<pi>) (Neg b) = (\<not>evalBool (\<sigma>,\<pi>) b)\<close> |
  \<open>evalBool (\<sigma>,\<pi>) (Dis b1 b2) = (evalBool (\<sigma>,\<pi>) b1 \<or> evalBool (\<sigma>,\<pi>) b2)\<close> |
  \<open>evalBool (\<sigma>,\<pi>) (Equal a1 a2) = (evalArtm (\<sigma>,\<pi>) a1 = evalArtm (\<sigma>,\<pi>) a2)\<close> |
  \<open>evalBool (\<sigma>,\<pi>) (Less a1 a2) = (evalArtm (\<sigma>,\<pi>) a1 < evalArtm (\<sigma>,\<pi>) a2)\<close>

datatype ('a,'b,'c,'d) action
  = Skip
  | Tst \<open>('a,'b,'c,'d) bool\<close>
  | AsV \<open>('a,'b) var\<close> \<open>('a,'b,'c,'d) artm\<close>
  | AsA \<open>('c,'d) arr\<close> \<open>('a,'b,'c,'d) artm\<close> \<open>('a,'b,'c,'d) artm\<close>


(*UNNUSED*)
fun evalAction where
  \<open>evalAction (\<sigma>,\<pi>) Skip = (\<sigma>,\<pi>)\<close> |
  \<open>evalAction (\<sigma>,\<pi>) (Tst b) = (\<sigma>,\<pi>)\<close> |
  \<open>evalAction (\<sigma>,\<pi>) (AsV x a) = (\<sigma>(x := evalArtm (\<sigma>,\<pi>) a),\<pi>)\<close> |
  \<open>evalAction (\<sigma>,\<pi>) (AsA x a1 a2) = (\<sigma>,\<pi>(x := (\<pi> x)((evalArtm (\<sigma>,\<pi>) a1) := evalArtm (\<sigma>,\<pi>) a2)))\<close> 

fun isPath where
  \<open>isPath pg Q (\<Sigma>,\<Pi>) q (\<sigma>,\<pi>) [] = 
    (q = Q \<and> (\<sigma>,\<pi>) = (\<Sigma>,\<Pi>))\<close> |
  \<open>isPath pg Q (\<Sigma>,\<Pi>) q (\<sigma>,\<pi>) ((qs,Skip,imps,qf) # path) = (
    q = qs \<and>
    (qs,Skip,imps,qf) \<in> pg \<and> 
    isPath pg Q (\<Sigma>,\<Pi>) qf (\<sigma>,\<pi>) path)\<close> |
  \<open>isPath pg Q (\<Sigma>,\<Pi>) q (\<sigma>,\<pi>) ((qs,Tst b,imps,qf) # path) = (
    q = qs \<and>
    (qs,Tst b,imps,qf) \<in> pg \<and> evalBool (\<sigma>,\<pi>) b \<and> 
    isPath pg Q (\<Sigma>,\<Pi>) qf (\<sigma>,\<pi>) path)\<close> |
  \<open>isPath pg Q (\<Sigma>,\<Pi>) q (\<sigma>,\<pi>) ((qs,AsV x a,imps,qf) # path) = (
    q = qs \<and>
    (qs,AsV x a,imps,qf) \<in> pg \<and> 
    isPath pg Q (\<Sigma>,\<Pi>) qf (\<sigma>(x := evalArtm (\<sigma>,\<pi>) a),\<pi>) path)\<close> |
  \<open>isPath pg Q (\<Sigma>,\<Pi>) q (\<sigma>,\<pi>) ((qs,AsA x a1 a2,imps,qf) # path) = (
    q = qs \<and>
    (qs,AsA x a1 a2,imps,qf) \<in> pg \<and> 
    isPath pg Q (\<Sigma>,\<Pi>) qf (\<sigma>,\<pi>(x := (\<pi> x)((evalArtm (\<sigma>,\<pi>) a1) := evalArtm (\<sigma>,\<pi>) a2))) path)\<close>

lemma join_paths: \<open>
  isPath pg q_m mem_m q_s mem_s p1 \<Longrightarrow> 
  isPath pg q_f mem_f q_m mem_m p2 \<Longrightarrow>
  isPath pg q_f mem_f q_s mem_s (p1 @ p2)\<close>
proof (induct p1 arbitrary: q_s mem_s)
  case Nil
  then have \<open>q_m = q_s \<and> mem_m = mem_s\<close> 
    by (metis isPath.simps(1) old.prod.exhaust)
  then show ?case
    using Nil.prems(2) by auto
next
  case (Cons a p1)
  then obtain q1 q2 imp act where adef:\<open>a = (q1,act,imp,q2)\<close>
    using prod_cases4 by blast
  then consider 
    \<open>act = Skip\<close> | \<open>\<exists> b. act = Tst b\<close> | \<open>\<exists> x a. act = AsV x a\<close> | \<open>\<exists> x a1 a2. act = AsA x a1 a2\<close>
    by (meson action.exhaust)
  then show ?case 
  proof cases
    case 1
    then have \<open>isPath pg q_m mem_m q2 mem_s p1\<close> 
      by (metis Cons.prems(1) adef isPath.simps(2) surj_pair)
    then have \<open>isPath pg q_f mem_f q2 mem_s (p1 @ p2)\<close> 
      by (simp add: Cons.hyps Cons.prems(2))
    moreover have \<open>(q1,Skip,imp,q2) \<in> pg\<close> 
      by (metis "1" Cons.prems(1) adef isPath.simps(2) surj_pair)
    moreover have \<open>q1 = q_s\<close> 
      by (metis "1" Cons.prems(1) adef isPath.simps(2) surj_pair)
    ultimately show ?thesis
      by (metis "1" Cons_eq_appendI adef isPath.simps(2) surj_pair)
  next
    case 2
    then show ?thesis sorry
  next
    case 3
    then show ?thesis sorry
  next
    case 4
    then show ?thesis sorry
  qed
qed

datatype ('a,'c) classified
  = T1' 'a
  | T3' 'c

datatype ('b,'d) unclassified
  = T2' 'b
  | T4' 'd

datatype ('a,'b,'c,'d) literal
  = T1'' 'a
  | T2'' 'b
  | T3'' 'c
  | T4'' 'd

fun classifyArtm where
  \<open>classifyArtm levelJoin levelBottom classified unclassified (Num i) = 
    levelBottom\<close> |
  \<open>classifyArtm levelJoin levelBottom classified unclassified (Var (T1 v)) = 
    classified (T1' v)\<close> |
  \<open>classifyArtm levelJoin levelBottom classified unclassified (Var (T2 v)) = 
    unclassified (T2' v)\<close> |
  \<open>classifyArtm levelJoin levelBottom classified unclassified (Arr (T3 v) a) = 
    levelJoin 
      (classified (T3' v)) 
      (classifyArtm levelJoin levelBottom classified unclassified a)\<close> |
  \<open>classifyArtm levelJoin levelBottom classified unclassified (Arr (T4 v) a) = 
    levelJoin 
      (unclassified (T4' v)) 
      (classifyArtm levelJoin levelBottom classified unclassified a)\<close> |
  \<open>classifyArtm levelJoin levelBottom classified unclassified (Plus a1 a2) = 
    levelJoin 
      (classifyArtm levelJoin levelBottom classified unclassified a1) 
      (classifyArtm levelJoin levelBottom classified unclassified a2)\<close> |
  \<open>classifyArtm levelJoin levelBottom classified unclassified (Minus a1 a2) = 
    levelJoin 
      (classifyArtm levelJoin levelBottom classified unclassified a1) 
      (classifyArtm levelJoin levelBottom classified unclassified a2)\<close> |
  \<open>classifyArtm levelJoin levelBottom classified unclassified (Times a1 a2) = 
    levelJoin 
      (classifyArtm levelJoin levelBottom classified unclassified a1) 
      (classifyArtm levelJoin levelBottom classified unclassified a2)\<close>

primrec classifyLiteral where
  \<open>classifyLiteral classified unclassified (T1'' v) = classified (T1' v)\<close> |
  \<open>classifyLiteral classified unclassified (T2'' v) = unclassified (T2' v)\<close> |
  \<open>classifyLiteral classified unclassified (T3'' v) = classified (T3' v)\<close> |
  \<open>classifyLiteral classified unclassified (T4'' v) = unclassified (T4' v)\<close>

definition \<open>
  classifyImps 
      (levelJoin :: 'e \<Rightarrow> 'e \<Rightarrow> 'e) levelBottom 
      (classified :: ('a,'c) classified \<Rightarrow> 'e) unclassified 
      imps \<equiv> 
    Finite_Set.fold (levelJoin \<circ> classifyLiteral classified unclassified) levelBottom imps\<close>

fun securityAnalyzer where
  \<open>securityAnalyzer 
      levelJoin (levelBottom :: 'e) 
      (classified :: ('a,'c) classified \<Rightarrow> 'e) unclassified 
      (qs :: 'f,Skip,imps,qf :: 'f) = 
    unclassified\<close> |
  \<open>securityAnalyzer levelJoin levelBottom classified unclassified (qs,Tst b,imps,qf) = 
    unclassified\<close> |
  \<open>securityAnalyzer levelJoin levelBottom classified unclassified (qs,AsV (T1 v) artm,imps,qf) = 
    unclassified\<close> |
  \<open>securityAnalyzer levelJoin levelBottom classified unclassified (qs,AsV (T2 v) artm,imps,qf) = 
    unclassified(
      (T2' v) := 
        levelJoin 
          (classifyArtm levelJoin levelBottom classified unclassified artm)
          (classifyImps levelJoin levelBottom classified unclassified imps))\<close> |
  \<open>securityAnalyzer 
      levelJoin levelBottom classified unclassified (qs,AsA (T3 v) artm1 artm2,imps,qf) = 
    unclassified\<close> |
  \<open>securityAnalyzer 
      levelJoin levelBottom classified unclassified (qs,AsA (T4 v) artm1 artm2,imps,qf) = 
    unclassified(
      (T4' v) := 
        levelJoin 
          (levelJoin 
            (classifyArtm levelJoin levelBottom classified unclassified artm1)
            (classifyArtm levelJoin levelBottom classified unclassified artm2))
          (classifyImps levelJoin levelBottom classified unclassified imps))\<close>

definition \<open>
  unclassifiedLess (levelLess :: 'a \<Rightarrow> 'a \<Rightarrow> HOL.bool) unclassified1 unclassified2 \<equiv>
    \<forall> v. levelLess (unclassified1 v) (unclassified2 v)\<close>

definition \<open>
  unclassifiedJoin (levelJoin :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) unclassified1 unclassified2 \<equiv>
    \<lambda> v. levelJoin (unclassified1 v) (unclassified2 v)\<close>

theorem security_analyzer_monotone: \<open>
  unclassifiedLess levelLess unclassified1 unclassified2 \<Longrightarrow> 
  unclassifiedLess levelLess
    (securityAnalyzer levelJoin levelBottom classified unclassified1 edge)
    (securityAnalyzer levelJoin levelBottom classified unclassified2 edge)\<close>
  sorry

definition \<open>
  constraintsSolved levelLess levelJoin levelBottom classified unclassifiedMap pg \<equiv>
    \<forall> (qs,act,imps,qf) \<in> pg. 
      unclassifiedLess levelLess 
        (securityAnalyzer levelJoin levelBottom classified (unclassifiedMap qs) (qs,act,imps,qf))
        (unclassifiedMap qf)\<close>

(*TODO*)
definition \<open>
  impsConsistent pg \<equiv> True\<close> 

fun noEdgeViolation where
  \<open>noEdgeViolation levelLess levelJoin levelBottom classified unclassified imps Skip =
    True\<close> |
  \<open>noEdgeViolation levelLess levelJoin levelBottom classified unclassified imps (Tst b) =
    True\<close> |
  \<open>noEdgeViolation levelLess levelJoin levelBottom classified unclassified imps (AsV (T1 v) artm) =
    True\<close> |
  \<open>noEdgeViolation levelLess levelJoin levelBottom classified unclassified imps (AsV (T2 v) artm) =
    levelLess 
      (levelJoin 
        (classifyArtm levelJoin levelBottom classified unclassified artm)
        (classifyImps levelJoin levelBottom classified unclassified imps)) 
      (unclassified (T2' v))\<close> |
  \<open>noEdgeViolation 
      levelLess levelJoin levelBottom classified unclassified imps (AsA (T3 v) artm1 artm2) =
    True\<close> |
  \<open>noEdgeViolation 
      levelLess levelJoin levelBottom classified unclassified imps (AsA (T4 v) artm1 artm2) =
    levelLess 
      (levelJoin
        (levelJoin
          (classifyArtm levelJoin levelBottom classified unclassified artm1)
          (classifyArtm levelJoin levelBottom classified unclassified artm2))
        (classifyImps levelJoin levelBottom classified unclassified imps)) 
      (unclassified (T4' v))\<close>

definition \<open>
  noPGViolations levelLess levelJoin levelBottom classified unclassifiedMap pg \<equiv>
    \<forall> (qs,act,imps,qf) \<in> pg. 
      noEdgeViolation levelLess levelJoin levelBottom classified (unclassifiedMap qs) imps act\<close>

(*TODO*)
definition \<open>
  nonInterference levelLess classified pg \<equiv> True\<close>

theorem non_interference: 
  assumes 
    \<open>impsConsistent pg\<close>
    \<open>constraintsSolved levelLess levelJoin levelBottom classified unclassifiedMap pg\<close>
    \<open>noPGViolations levelLess levelJoin levelBottom classified unclassifiedMap pg\<close>
  shows \<open>nonInterference levelLess classified pg\<close>
  sorry

end