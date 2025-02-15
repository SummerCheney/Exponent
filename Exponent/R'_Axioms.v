Require Export MK_1_6.

Close Scope nat_scope.

Declare Scope R'_scope.
Delimit Scope R'_scope with r'.
Open Scope R'_scope.

(* 实数集 *)
Parameter R' : Class.

Axiom Ensemble_R' : Ensemble R'.

(* 加法函数 *)
Parameter fp' : Class.

Axiom PlusR' : (Function fp') /\ (dom(fp') = R' × R')
  /\ (ran(fp') ⊂ R').

(* 加法 *)
Notation "x + y" := fp'[[x, y]] : R'_scope.

(* 加法公理 *)
(* 加法单位元 *)
Parameter zeroR' : Class.

Notation "0 '''" := zeroR' : R'_scope.

Axiom zero_in_R' : 0' ∈ R'.

Axiom Plus_P1' : ∀ x, x ∈ R' -> x + 0' = x.

Axiom Plus_P2' : ∀ x, x ∈ R' -> ∃ y, y ∈ R' /\ x + y = 0'.

Axiom Plus_P3' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> x + (y + z) = (x + y) + z.

Axiom Plus_P4' : ∀ x y, x ∈ R' -> y ∈ R' -> x + y = y + x.

(* 乘法函数 *)
Parameter fm' : Class.

Axiom MultR' : (Function fm') /\ (dom(fm') = R' × R')
  /\ (ran(fm') ⊂ R').

(* 乘法 *)
Notation "x · y" := fm'[[x, y]](at level 40) : R'_scope.

(* 乘法公理 *)
(* 乘法单位元 *)
Parameter oneR' : Class.

Notation "1 '''" := oneR' : R'_scope.

Axiom one_in_R' : 1' ∈ (R' ~ [0']).

Axiom Mult_P1' : ∀ x, x ∈ R' -> x · 1' = x.

Axiom Mult_P2' : ∀ x, x ∈ (R' ~ [0']) -> ∃ y, y ∈ R' /\ x · y = 1'.

Axiom Mult_P3' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> x · (y · z) = (x · y) · z.

Axiom Mult_P4' : ∀ x y, x ∈ R' -> y ∈ R' -> x · y = y · x.

Axiom Mult_P5' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> (x + y) · z = (x · z) + (y · z).

(* 序公理 *)
Parameter Leq' : Class.

Axiom LeqR' : Leq' ⊂ R' × R'.

Notation "x ≤ y" := ([x, y] ∈ Leq')(at level 60) : R'_scope.

Axiom Leq_P1' : ∀ x, x ∈ R' -> x ≤ x.

Axiom Leq_P2' : ∀ x y, x ∈ R' -> y ∈ R' -> x ≤ y -> y ≤ x -> x = y.

Axiom Leq_P3' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R' -> x ≤ y
  -> y ≤ z -> x ≤ z.

Axiom Leq_P4' : ∀ x y, x ∈ R' -> y ∈ R' -> x ≤ y \/ y ≤ x.

Axiom Plus_Leq' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R' -> x ≤ y
  -> x + z ≤ y + z.

Axiom Mult_Leq' : ∀ x y, x ∈ R' -> y ∈ R' -> 0' ≤ x -> 0' ≤ y
  -> 0' ≤ x · y.

(* 完备性公理 *)
Axiom Completeness' : ∀ X Y, X ⊂ R' -> Y ⊂ R' -> X <> Φ -> Y <> Φ
  -> (∀ x y, x ∈ X -> y ∈ Y -> x ≤ y) -> ∃ c, c ∈ R'
    /\ (∀ x y, x ∈ X -> y ∈ Y -> (x ≤ c /\ c ≤ y)).

(* 推论 加法公理的推论 *)
Corollary Plus_Co1' : ∀ x y, x ∈ R' -> y ∈ R' -> x + y = x -> y = 0'.
Proof.
  intros. pose proof zero_in_R'. apply NNPP; intro.
  pose proof H2. apply (Leq_P4' y 0') in H2 as []; auto;
  pose proof H; apply Plus_P2' in H5 as [x0[]]; pose proof H6;
  rewrite <- H1,(Plus_P4' x y),<- Plus_P3',H7,Plus_P1' in H6; auto.
Qed.

Corollary Plus_Co2' : ∀ x, x ∈ R' -> (exists ! x0, x0 ∈ R'
  /\ x + x0 = 0').
Proof.
  intros. pose proof H. apply Plus_P2' in H0 as [x0[]].
  exists x0. split; auto. intros x1 []. rewrite <-H1 in H3.
  assert ((x + x0) + x1 = (x + x0) + x0).
  { rewrite <- Plus_P3',(Plus_P4' x0 x1),Plus_P3',H3; auto. }
  rewrite H1,Plus_P4',Plus_P1',Plus_P4',Plus_P1' in H4; auto;
  apply zero_in_R'.
Qed.

Notation "- a" := (∩(\{ λ u, u ∈ R' /\ u + a = 0' \})) : R'_scope.

Notation "x - y" := (x + (-y)) : R'_scope.

Corollary Plus_Co3' : ∀ a x b, a ∈ R' -> x ∈ R' -> b ∈ R'
  -> a + x = b -> x = b + (-a).
Admitted.

(* 推论 乘法公理的推论 *)
Corollary Mult_Co1' : ∀ x y, x ∈ (R' ~ [0']) -> y ∈ R' -> x · y = x
  -> y = 1'.
Admitted.

Corollary Mult_Co2' : ∀ x, x ∈ (R' ~ [0'])
  -> (exists ! x0, x0 ∈ (R' ~ [0']) /\ x · x0 = 1').
Admitted.

Notation "a ⁻" := (∩(\{ λ u, u ∈ (R' ~ [0']) /\ u · a = 1' \}))
  (at level 5) : R'_scope.

Notation "m / n" := (m · (n⁻)) : R'_scope.

Corollary Mult_Co3' : ∀ a x b, a ∈ (R' ~ [0']) -> x ∈ R' -> b ∈ R'
  -> a · x = b -> x = b · (a⁻).
Admitted.

(* 推论 加法与乘法联系的公理推论 *)
Corollary PlusMult_Co1' : ∀ x, x ∈ R' -> x · 0' = 0' /\ 0' · x = 0'.
Admitted.

Corollary PlusMult_Co2' : ∀ x y, x ∈ R' -> y ∈ R' -> x · y = 0'
  -> x = 0' \/ y = 0'.
Admitted.

Corollary PlusMult_Co3' : ∀ x, x ∈ R' -> -x = (-(1')) · x.
Admitted.

Corollary PlusMult_Co4' : ∀ x, x ∈ R' -> (-(1')) · (-x) = x.
Admitted.

Corollary PlusMult_Co5' : ∀ x, x ∈ R' -> (-x) · (-x) = x · x.
Admitted.

Corollary PlusMult_Co6' : ∀ x, x ∈ (R' ~ [0']) <-> (x⁻) ∈ (R' ~ [0']).
Admitted.

Definition lt' x y := x ≤ y /\ x <> y.

Notation "x < y" := (lt' x y) : R'_scope.

(* 推论 序公理推论 *)
Corollary Order_Co1' : ∀ x y, x ∈ R' -> y ∈ R'
  -> x < y \/ y < x \/ x = y.
Admitted.

Corollary Order_Co2' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> (x < y /\ y ≤ z) \/ (x ≤ y /\ y < z) -> x < z.
Admitted.

(* 推论 序与加法及乘法联系的公理推论 *)
Corollary OrderPM_Co1' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> x < y -> x + z < y + z.
Admitted.

Corollary OrderPM_Co2' : ∀ x, x ∈ R' -> 0' < x -> (-x) < 0'.
Admitted.

Corollary OrderPM_Co3' : ∀ x y z w, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> w ∈ R' -> x ≤ y -> z ≤ w -> x + z ≤ y + w.
Admitted.

Corollary OrderPM_Co4' : ∀ x y z w, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> w ∈ R' -> x ≤ y -> z < w -> x + z < y + w.
Admitted.

Corollary OrderPM_Co5' : ∀ x y, x ∈ R' -> y ∈ R'
  -> (0' < x /\ 0' < y) \/ (x < 0' /\ y < 0') -> 0' < x · y.
Admitted.

Corollary OrderPM_Co6' : ∀ x y, x ∈ R' -> y ∈ R' -> x < 0' -> 0' < y
  -> x · y < 0'.
Admitted.

Corollary OrderPM_Co7' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> x < y -> 0' < z -> x · z < y · z.
Admitted.

Corollary OrderPM_Co8' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> x < y -> z < 0' -> y · z < x · z.
Admitted.

Corollary OrderPM_Co9' : 0' < 1'.
Proof.
  pose proof zero_in_R'. pose proof one_in_R'.
  apply MKT4' in H0 as []. apply AxiomII in H1 as [].
  pose proof H. apply (Order_Co1' 0' 1') in H3 as [H3|[|]]; auto.
  - assert (0' < 1' · 1'). { apply OrderPM_Co5'; auto. }
    rewrite Mult_P1' in H4; auto.
  - elim H2. apply MKT41; eauto.
Qed.

Corollary OrderPM_Co10' : ∀ x, x ∈ R' -> 0' < x -> 0' < (x⁻).
Admitted.

Corollary OrderPM_Co11' : ∀ x y, x ∈ R' -> y ∈ R' -> 0' < x
  -> x < y -> 0' < (y⁻) /\ (y⁻) < (x⁻).
Admitted.

(* 完备公理与数集确界的存在性 *)
Definition Upper' X c := X ⊂ R' /\ c ∈ R' /\ (∀ x, x ∈ X -> x ≤ c).

Definition Lower' X c := X ⊂ R' /\ c ∈ R' /\ (∀ x, x ∈ X -> c ≤ x).

Definition Bounded' X := ∃ c1 c2, Upper' X c1 /\ Lower' X c2.

Definition Max' X c := X ⊂ R' /\ c ∈ X /\ (∀ x, x ∈ X -> x ≤ c).

Definition Min' X c := X ⊂ R' /\ c ∈ X /\ (∀ x, x ∈ X -> c ≤ x).

Corollary Max_Corollary' : ∀ X c1 c2, Max' X c1 -> Max' X c2 -> c1 = c2.
Admitted.

Corollary Min'_Corollary' : ∀ X c1 c2, Min' X c1 -> Min' X c2 -> c1 = c2.
Admitted.

Definition Sup1' X s := Upper' X s /\ (∀ s1, s1 ∈ R' -> s1 < s
  -> (∃ x1, x1 ∈ X /\ s1 < x1)).

Definition Sup2' X s := Min' (\{ λ u, Upper' X u \}) s.

Corollary Sup_Corollary' : ∀ X s, Sup1' X s <-> Sup2' X s.
Admitted.

Definition Inf1' X i := Lower' X i /\ (∀ i1, i1 ∈ R' -> i < i1
  -> (∃ x1, x1 ∈ X /\ x1 < i1)).

Definition Inf2' X i := Max' (\{ λ u, Lower' X u \}) i.

Corollary Inf_Corollary' : ∀ X i, Inf1' X i <-> Inf2' X i.
Admitted.

Theorem SupT' : ∀ X, X ⊂ R' -> X <> Φ -> ∃ c, Upper' X c
  -> exists ! s, Sup1' X s.
Admitted.

Theorem InfT' : ∀ X, X ⊂ R' -> X <> Φ -> ∃ c, Lower' X c
  -> exists ! i, Inf1' X i.
Admitted.

(* 自然数集的定义 *)
(* 归纳集的定义 *)
Definition IndSet' X := X ⊂ R' /\ (∀ x, x ∈ X -> (x + 1') ∈ X).

Proposition IndSet_P1' : ∀ X, X <> Φ -> (∀ x, x ∈ X -> IndSet' x)
  -> IndSet' (∩X).
Admitted.

(* 自然数集 *)
Definition N' := ∩(\{ λ u, IndSet' u /\ 1' ∈ u \}).

(* 数学归纳原理 *)
Theorem MathInd' : ∀ E, E ⊂ N' -> 1' ∈ E -> (∀ x, x ∈ E
  -> (x + 1') ∈ E) -> E = N'.
Admitted.

(* 自然数的性质 *)
Proposition Nat_P1' : ∀ m n, m ∈ N' -> n ∈ N'
  -> (m + n) ∈ N' /\ (m · n) ∈ N'.
Admitted.

Proposition Nat_P2' : ∀ n, n ∈ N' -> n <> 1' -> (n - 1') ∈ N'.
Admitted.

(* 书打错集合里的n应该是x *)
Proposition Nat_P3' : ∀ n, n ∈ N'
  -> Min' (\{ λ u, u ∈ N' /\ n < u \}) (n + 1').
Admitted.

Proposition Nat_P4' : ∀ m n, m ∈ N' -> n ∈ N' -> n < m -> (n + 1') ≤ m.
Admitted.

Proposition Nat_P5' : ∀ n, n ∈ N'
  -> ~ (∃ x, x ∈ N' /\ n < x /\ x < (n + 1')).
Admitted.

(* 书上和性质2有重复 *)
Proposition Nat_P6' : ∀ n, n ∈ N' -> n <> 1'
  -> ~ (∃ x, x ∈ N' /\ (n - 1') < x /\ n < x).
Admitted.

Proposition Nat_P7' : ∀ E, E ⊂ N' -> E <> Φ -> ∃ n, Min' E n.
Admitted.

(* 整数的定义 *)
Definition Z' := N' ∪ \{ λ u, (-u) ∈ N' \} ∪ [0'].

(* 整数的性质 *)
Corollary Z_Corollary' : N' ⊂ Z' /\ Z' ⊂ R'.
Admitted.

Proposition Int_P1' : ∀ m n, m ∈ Z' -> n ∈ Z'
  -> (m + n) ∈ Z' /\ (m · n) ∈ Z'.
Admitted.

Proposition Int_P2' : ∀ n, n ∈ Z' -> n + 0' = n /\ 0' + n = n.
Admitted.

Proposition Int_P3' : ∀ n, n ∈ Z' -> (-n) ∈ Z' /\ n + (-n) = 0'
  /\ (-n) + n = 0'.
Admitted.

Proposition Int_P4' : ∀ m n k, m ∈ Z' -> n ∈ Z' -> k ∈ Z'
  -> m + (n + k) = (m + n) + k.
Admitted.

Proposition Int_P5' : ∀ m n, m ∈ Z' -> n ∈ Z' -> m + n = n + m.
Admitted.

(* 有理数的定义 *)
Definition Q' := \{ λ u, ∃ m n, m ∈ Z' /\ n ∈ (Z' ~ [0'])
  /\ u = m / n \}.

Corollary Q_Corollary' : Z' ⊂ Q' /\ Q' ⊂ R'.
Admitted.

Proposition Frac_P1' : ∀ m n k, m ∈ Z' -> n ∈ (Z' ~ [0'])
  -> k ∈ (Z' ~ [0']) -> m / n = (m · k) / (n · k).
Admitted.

Proposition Rat_P1' : ∀ x y, x ∈ Q' -> y ∈ Q'
  -> (x + y) ∈ Q' /\ (x · y) ∈ Q'.
Admitted.

Proposition Rat_P2' : ∀ x, x ∈ Q' -> x + 0' = x /\ 0' + x = x.
Admitted.

Proposition Rat_P3' : ∀ n, n ∈ Q' -> (-n) ∈ Q' /\ n + (-n) = 0'
  /\ (-n) + n = 0'.
Admitted.

Proposition Rat_P4' : ∀ x y z, x ∈ Q' -> y ∈ Q' -> z ∈ Q'
  -> x + (y + z) = (x + y) + z.
Admitted.

Proposition Rat_P5' : ∀ x y, x ∈ Q' -> y ∈ Q' -> x + y = x + y.
Admitted.

Proposition Rat_P6' : ∀ x, x ∈ Q' -> x · 1' = x /\ 1' · x = x.
Admitted.

Proposition Rat_P7' : ∀ x, x ∈ (Q' ~ [0'])
  -> (x⁻) ∈ Q' /\ x · (x⁻) = 1'.
Admitted.

Proposition Rat_P8' : ∀ x y z, x ∈ Q' -> y ∈ Q' -> z ∈ Q'
  -> x · (y · z) = (x · y) · z.
Admitted.

Proposition Rat_P9' : ∀ x y, x ∈ Q' -> y ∈ Q' -> x · y = y · x.
Admitted.

Proposition Rat_P10' : ∀ x y z, x ∈ Q' -> y ∈ Q' -> z ∈ Q'
  -> (x + y) · z = (x · z) + (y · z).
Admitted.

Theorem Existence_of_irRational_Number' : (R' ~ Q') <> Φ.
Admitted.

(* 阿基米德原理 *)
Proposition Arch_P1' : ∀ E, E ⊂ N' -> E <> Φ -> Bounded' E
  -> ∃ n, Max' E n.
Admitted.

Proposition Arch_P2' : ~ ∃ n, Upper' N' n.
Admitted.

Proposition Arch_P3' : ∀ E, E ⊂ Z' -> E <> Φ -> (∃ x, Upper' E x)
  -> ∃ n, Max' E n.
Admitted.

Proposition Arch_P4' : ∀ E, E ⊂ N' -> E <> Φ -> Bounded' E
  -> ∃ n, Min' E n.
Admitted.

Proposition Arch_P5' : ~ (∃ n, Lower' Z' n) /\ ~ (∃ n, Upper' Z' n).
Admitted.

Proposition Arch_P6' : ∀ h x, h ∈ R' -> 0' < h -> x ∈ R'
  -> (exists ! k, (k - 1') · h ≤ x /\ x < k · h).
Admitted.

Proposition Arch_P7' : ∀ x, x ∈ R' -> 0' < x
  -> (∃ n, n ∈ N' /\ 0' < 1' / n /\ 1' / n < x).
Admitted.

Proposition Arch_P8' : ∀ x, x ∈ R' -> 0' ≤ x
  -> (∀ n, n ∈ N' -> x < 1' / n) -> x = 0'.
Admitted.

Proposition Arch_P9' : ∀ a b, a ∈ R' -> b ∈ R' -> a < b
  -> (∃ r, r ∈ Q' /\ a < r /\ r < b).
Admitted.

Proposition Arch_P10' : ∀ x, x ∈ R'
  -> (exists ! k, k ∈ Z' /\ k ≤ x /\ x < k + 1').
Admitted.

(* 实数的几何解释 *)
(* 有界区间 *)
(* 开区间 *)
Notation "］ a , b ［" := (\{ λ x, x ∈ R' /\ a < x /\ x < b \})
  (at level 5, a at level 0, b at level 0) : R'_scope.

(* 闭区间 *)
Notation "［ a , b ］" := (\{ λ x, x ∈ R' /\ a ≤ x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0) : R'_scope.

(* 左开右闭 *)
Notation "］ a , b ］" := (\{ λ x, x ∈ R' /\ a < x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0) : R'_scope.

(* 左闭右开 *)
Notation "［ a , b ［" := (\{ λ x, x ∈ R' /\ a ≤ x /\ x < b \})
  (at level 5, a at level 0, b at level 0) : R'_scope.

(* 无界区间 *)
Notation "］ a , +∞［" := (\{ λ x, x ∈ R' /\ a < x \})
  (at level 5, a at level 0) : R'_scope.

Notation "［ a , +∞［" := (\{ λ x, x ∈ R' /\ a ≤ x \})
  (at level 5, a at level 0) : R'_scope.

Notation "］-∞ , b ］" := (\{ λ x, x ∈ R' /\ x ≤ b \})
  (at level 5, b at level 0) : R'_scope.

Notation "］]-∞ , b ［" := (\{ λ x, x ∈ R' /\ x < b \})
  (at level 5, b at level 0) : R'_scope.

Notation "]-∞ , +∞[" := (R')(at level 0) : R'_scope.

(* 邻域 *)
Definition Neighbourhood' x δ := x ∈ R' /\ δ ∈ R'
  /\ x ∈ ］(x - δ),(x + δ)［.

(* 绝对值函数 *)
Definition Abs' := \{\ λ u v, u ∈ R'
  /\ ((0' ≤ u /\ v = u) \/ (u < 0' /\ v = (-u))) \}\.

Corollary Abs_Corollary' : Function Abs' /\ dom(Abs') = R'
  /\ ran(Abs') ⊂ R'.
Admitted.

Notation "｜ x ｜" := (Abs'[x])(at level 5, x at level 0) : R'_scope.

Definition Distance' x y := ｜(x - y)｜.

(* 绝对值的性质 *)
Proposition Abs_P1' : ∀ x, x ∈ R' -> 0' ≤ ｜x｜ /\ (｜x｜ = 0' <-> x = 0').
Admitted.

Proposition Abs_P2' : ∀ x, x ∈ R' -> ｜x｜ = ｜(-x)｜ /\ -｜x｜ ≤ x
  /\ x ≤ ｜x｜.
Admitted.

Proposition Abs_P3' : ∀ x y, x ∈ R' -> y ∈ R' -> ｜(x · y)｜ = ｜x｜ · ｜y｜.
Admitted.

Proposition Abs_P4' : ∀ x y, x ∈ R' -> y ∈ R' -> 0' < y
  -> ｜x｜ ≤ y <-> -y ≤ x /\ x ≤ y.
Admitted.

Proposition Abs_P5' : ∀ x y, x ∈ R' -> y ∈ R' -> ｜(x + y)｜ ≤ ｜x｜ + ｜y｜
  /\ ｜(x - y)｜ ≤ ｜x｜ + ｜y｜ /\ ｜(｜x｜ - ｜y｜)｜ ≤ ｜(x - y)｜.
Admitted.

Proposition Abs_P6' : ∀ x y, x ∈ R' -> y ∈ R'
  -> ｜(x - y)｜ = 0' <-> x = y.
Admitted.

Proposition Abs_P7' : ∀ x y, x ∈ R' -> y ∈ R' -> ｜(x - y)｜ = ｜(y - x)｜.
Admitted.

Proposition Abs_P8' : ∀ x y z, x ∈ R' -> y ∈ R' -> z ∈ R'
  -> ｜(x - y)｜ ≤ ｜(x - z)｜ + ｜(z - y)｜.
Admitted.

























