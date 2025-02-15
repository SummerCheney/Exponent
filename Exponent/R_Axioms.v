
Require Export MK_1_6.

Close Scope nat_scope.
Declare Scope R_scope.
Delimit Scope R_scope with r.
Open Scope R_scope.


(* 实数集 *)
Parameter R : Class.

Axiom Ensemble_R : Ensemble R.

(* 加法函数 *)
Parameter fp : Class.

Axiom PlusR : (Function fp) /\ (dom(fp) = R × R) /\ (ran(fp) ⊂ R).

(* 加法 *)
Notation "x + y" := fp[[x, y]] : R_scope.

Corollary Plus_close : ∀ x y, x ∈ R -> y ∈ R -> (x + y) ∈ R.
Proof.
  intros. destruct PlusR as [H1[]].
  apply H3, (@ Property_ran ([x,y])), Property_Value; auto.
  rewrite H2. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Global Hint Resolve Plus_close : real.

(* 加法公理 *)
(* 加法单位元 *)
Parameter zeroR : Class.

Notation "0" := zeroR : R_scope.

Axiom zero_in_R : 0 ∈ R.

Global Hint Resolve zero_in_R : real.

Axiom Plus_P1 : ∀ x, x ∈ R -> x + 0 = x.

Axiom Plus_P2 : ∀ x, x ∈ R -> ∃ y, y ∈ R /\ x + y = 0.

Axiom Plus_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> x + (y + z) = (x + y) + z.

Axiom Plus_P4 : ∀ x y, x ∈ R -> y ∈ R -> x + y = y + x.

(* 乘法函数 *)
Parameter fm : Class.

Axiom MultR : (Function fm) /\ (dom(fm) = R × R) /\ (ran(fm) ⊂ R).

(* 乘法 *)
Notation "x · y" := fm[[x, y]](at level 40) : R_scope.

Corollary Mult_close : ∀ x y, x ∈ R -> y ∈ R -> (x · y) ∈ R.
Proof.
  intros. destruct MultR as [H1[]].
  apply H3, (@ Property_ran ([x,y])),Property_Value; auto.
  rewrite H2. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Global Hint Resolve Mult_close : real.

(* 乘法公理 *)
(* 乘法单位元 *)
Parameter oneR : Class.

Notation "1" := oneR : R_scope.

Axiom one_in_R : 1 ∈ (R ~ [0]).

Corollary one_in_R_Co : 1 ∈ R.
Proof.
  pose proof one_in_R. apply MKT4' in H as []; auto.
Qed.

Global Hint Resolve one_in_R one_in_R_Co : real.

Axiom Mult_P1 : ∀ x, x ∈ R -> x · 1 = x.

Axiom Mult_P2 : ∀ x, x ∈ (R ~ [0])
  -> ∃ y, y ∈ (R ~ [0]) /\ x · y = 1.

Axiom Mult_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> x · (y · z) = (x · y) · z.

Axiom Mult_P4 : ∀ x y, x ∈ R -> y ∈ R -> x · y = y · x.

Axiom Mult_P5 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> (x + y) · z = (x · z) + (y · z).

(* 序公理 *)
Parameter Leq : Class.

Axiom LeqR : Leq ⊂ R × R.

Notation "x ≤ y" := ([x, y] ∈ Leq)(at level 60) : R_scope.

Axiom Leq_P1 : ∀ x, x ∈ R -> x ≤ x.

Axiom Leq_P2 : ∀ x y, x ∈ R -> y ∈ R -> x ≤ y -> y ≤ x -> x = y.

Axiom Leq_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y -> y ≤ z
  -> x ≤ z.

Axiom Leq_P4 : ∀ x y, x ∈ R -> y ∈ R -> x ≤ y \/ y ≤ x.

Axiom Plus_Leq : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y
  -> x + z ≤ y + z.

Axiom Mult_Leq : ∀ x y, x ∈ R -> y ∈ R -> 0 ≤ x -> 0 ≤ y
  -> 0 ≤ x · y.

(* 完备性公理 *)
Axiom Completeness : ∀ X Y, X ⊂ R -> Y ⊂ R -> X <> Φ -> Y <> Φ
  -> (∀ x y, x ∈ X -> y ∈ Y -> x ≤ y) -> ∃ c, c ∈ R
    /\ (∀ x y, x ∈ X -> y ∈ Y -> (x ≤ c /\ c ≤ y)).

(* 推论 加法公理的推论 *)
Corollary Plus_Co1 : ∀ x, x ∈ R -> (∀ y, y ∈ R -> y + x = y)
  -> x = 0.
Proof.
  intros. pose proof zero_in_R. pose proof (Plus_P1 x H).
  rewrite <-H2,Plus_P4; auto.
Qed.

Corollary Plus_Co2 : ∀ x, x ∈ R -> (exists ! x0, x0 ∈ R
  /\ x + x0 = 0).
Proof.
  intros. pose proof H. apply Plus_P2 in H0 as [x0[]].
  exists x0. split; auto. intros x1 []. rewrite <-H1 in H3.
  assert ((x + x0) + x1 = (x + x0) + x0).
  { rewrite <- Plus_P3,(Plus_P4 x0 x1),Plus_P3,H3; auto. }
  rewrite H1,Plus_P4,Plus_P1,Plus_P4,Plus_P1 in H4; auto;
  apply zero_in_R.
Qed.

Notation "- a" := (∩(\{ λ u, u ∈ R /\ u + a = 0 \})) : R_scope.

Corollary Plus_neg1a : ∀ a, a ∈ R -> (-a) ∈ R.
Proof.
  intros.
  pose proof H. apply Plus_Co2 in H0 as [a0[[]]].
  assert (\{ λ u, u ∈ R /\ u + a = 0 \} = [a0]).
  { apply AxiomI; split; intros. apply AxiomII in H3 as [H3[]].
    apply MKT41; eauto. symmetry. apply H2. rewrite Plus_P4; auto.
    apply MKT41 in H3; eauto. apply AxiomII.
    rewrite H3,Plus_P4; auto. split; eauto. }
  rewrite H3. assert (∩[a0] = a0). { apply MKT44; eauto. }
  rewrite H4; auto.  
Qed.

Corollary Plus_neg1b : ∀ a, (-a) ∈ R -> a ∈ R.
Proof.
  intros. apply NNPP. intro. 
  assert ((\{ λ u, u ∈ R /\ u + a = 0 \} = Φ )).
  { apply AxiomI; split; intros. apply AxiomII in H1 as [H1[]].
    assert ([z,a] ∉ (dom( fp ))). 
    { destruct PlusR as [H4[]]. unfold NotIn. intro.
      rewrite H5 in H7. apply AxiomII' in H7 as [H7[]]. auto. }
    apply MKT69a in H4. rewrite H3 in H4. pose proof zero_in_R.
    rewrite H4 in H5. pose proof MKT39. elim H6. eauto.
    apply MKT16 in H1. destruct H1. }
  rewrite H1 in H. rewrite MKT24 in H. pose proof MKT39.
  elim H2. eauto.
Qed.

Corollary Plus_neg2 : ∀ a, a ∈ R -> a + (-a) = 0.
Proof.
  intros. pose proof H. apply Plus_Co2 in H0 as [a0[[]]].
  assert (\{ λ u, u ∈ R /\ u + a = 0 \} = [a0]).
  { apply AxiomI; split; intros. apply AxiomII in H3 as [H3[]].
    apply MKT41; eauto. symmetry. apply H2. rewrite Plus_P4; auto.
    apply MKT41 in H3; eauto. apply AxiomII.
    rewrite H3,Plus_P4; auto. split; eauto. }
  rewrite H3. assert (∩[a0] = a0). { apply MKT44; eauto. }
  rewrite H4; auto.
Qed.

Notation "x - y" := (x + (-y)) : R_scope.

Corollary Minus_P1 : ∀ a, a ∈ R -> a - a = 0.
Proof.
  intros. apply Plus_neg2; auto.
Qed.

Corollary Minus_P2 : ∀ a, a ∈ R -> a - 0 = a.
Proof.
  intros. pose proof zero_in_R.
  assert (\{ λ u, u ∈ R /\ u + 0 = 0 \} = [0]).
  { apply AxiomI; split; intros. apply AxiomII in H1 as [H1[]].
    apply MKT41; eauto. rewrite Plus_P1 in H3; auto.
    apply MKT41 in H1; eauto. rewrite H1. apply AxiomII;
    repeat split; eauto. rewrite Plus_P1; auto. }
  rewrite H1. assert (∩[0] = 0). { apply MKT44; eauto. }
  rewrite H2,Plus_P1; auto.
Qed.

Global Hint Resolve Plus_neg1a Plus_neg1b
  Plus_neg2 Minus_P1 Minus_P2 : real.    

Corollary Plus_Co3 : ∀ a x b, a ∈ R -> x ∈ R -> b ∈ R -> a + x = b
  -> x = b + (-a).
Proof.
  intros. pose proof H. apply Plus_Co2 in H3 as [a0[[]]].
  assert (x + a + a0 = b + a0). { rewrite (Plus_P4 x),H2; auto. }
  rewrite <-Plus_P3,H4,Plus_P1 in H6; auto.
  assert (\{ λ u, u ∈ R /\ u + a = 0 \} = [a0]).
  { apply AxiomI; split; intros. apply AxiomII in H7 as [H7[]].
    apply MKT41; eauto. symmetry. apply H5. rewrite Plus_P4; auto.
    apply MKT41 in H7; eauto. rewrite H7. rewrite Plus_P4 in H4;
    auto. apply AxiomII; split; eauto. }
  assert (Ensemble a0); eauto. apply MKT44 in H8 as [H8 _].
  rewrite H7,H8; auto.
Qed.

(* 推论 乘法公理的推论 *)
Corollary Mult_Co1 : ∀ x, x ∈ (R ~ [0]) -> (∀ y, y ∈ R
  -> y · x = y) -> x = 1.
Proof.
  intros. pose proof H. apply MKT4' in H1 as [].
  pose proof one_in_R. apply MKT4' in H3 as [].
  pose proof (Mult_P1 x H1). rewrite <-H5,Mult_P4; auto.
Qed.

Corollary Mult_Co2 : ∀ x, x ∈ (R ~ [0])
  -> (exists ! x0, x0 ∈ (R ~ [0]) /\ x · x0 = 1).
Proof.
  intros. pose proof H. pose proof zero_in_R.
  apply Mult_P2 in H0 as [x0[]]. exists x0.
  split; auto. intros x1 []. apply MKT4' in H as [H _].
  apply MKT4' in H3 as [H3 _]. apply MKT4' in H0 as [H0 _].
  assert (x0 · (x · x1) = x1).
  { rewrite Mult_P3,(Mult_P4 x0),H2,Mult_P4,Mult_P1;
    auto with real. }
  rewrite H4,Mult_P1 in H5; auto.
Qed.

Notation "a ⁻" := (∩(\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \}))
  (at level 5) : R_scope.

Corollary Mult_inv1 : ∀ a, a ∈ (R ~ [0]) -> (a⁻) ∈ (R ~ [0]).
Proof.
  intros. pose proof H. apply Mult_Co2 in H0 as [a1[[]]].
  pose proof H. pose proof H0. apply MKT4' in H3 as [H3 _].
  apply MKT4' in H4 as [H4 _].
  assert (\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \} = [a1]).
  { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
    apply MKT41; eauto. symmetry. apply H2. rewrite Mult_P4; auto.
    apply MKT4' in H6; tauto. apply MKT41 in H5; eauto.
    rewrite H5. apply AxiomII. rewrite Mult_P4; auto. split; eauto. }
  rewrite H5. assert (∩[a1] = a1). { apply MKT44; eauto. }
  rewrite H6; auto.
Qed.

Corollary Mult_inv2 : ∀ a, a ∈ (R ~ [0]) -> a · (a⁻) = 1.
Proof.
  intros. pose proof H. apply Mult_Co2 in H0 as [a1[[]]].
  pose proof H. pose proof H0. apply MKT4' in H3 as [H3 _].
  apply MKT4' in H4 as [H4 _].
  assert (\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \} = [a1]).
  { apply AxiomI; split; intros. apply AxiomII in H5 as [H5[]].
    apply MKT41; eauto. symmetry. apply H2. rewrite Mult_P4; auto.
    apply MKT4' in H6; tauto. apply MKT41 in H5; eauto.
    rewrite H5. apply AxiomII. rewrite Mult_P4; auto. split; eauto. }
  rewrite H5. assert (∩[a1] = a1). { apply MKT44; eauto. }
  rewrite H6; auto.
Qed.

Notation "m / n" := (m · (n⁻)) : R_scope.

Corollary Divide_P1 : ∀ a, a ∈ (R ~ [0]) -> a / a = 1.
Proof.
  intros. apply Mult_inv2; auto.
Qed.

Corollary Divide_P2 : ∀ a, a ∈ R -> a / 1 = a.
Proof.
  intros. assert (\{ λ u, u ∈ (R ~ [0]) /\ u · 1 = 1 \} = [1]).
  { apply AxiomI; split; intros. apply AxiomII in H0 as [H0[]].
    apply MKT41; eauto with real. rewrite Mult_P1 in H2; auto.
    apply MKT4' in H1; tauto. apply MKT41 in H0; eauto with real.
    rewrite H0. apply AxiomII; repeat split; eauto with real.
    rewrite Mult_P1; auto with real. }
  rewrite H0. assert (∩[1] = 1). { apply MKT44; eauto with real. }
  rewrite H1,Mult_P1; auto.
Qed.

Global Hint Resolve Mult_inv1 Mult_inv2 Divide_P1 Divide_P2 : real.

Corollary Mult_Co3 : ∀ a x b, a ∈ (R ~ [0]) -> x ∈ R -> b ∈ R
  -> a · x = b -> x = b · (a⁻).
Proof.
  intros. pose proof H. apply Mult_Co2 in H3 as [a0[[]]].
  apply MKT4' in H as []. pose proof H3. apply MKT4' in H3 as[].
  assert (x · a · a0 = b · a0). 
  { rewrite (Mult_P4 x), H2; auto. }
  rewrite <-Mult_P3,H4,Mult_P1 in H9; auto.
  assert (\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1\} = [a0]).
  { apply AxiomI; split; intros. apply AxiomII in H10 as [H10[]].
    apply MKT41; eauto. symmetry. apply H5. rewrite Mult_P4; auto.
    apply MKT4' in H11 as []; auto. apply MKT41 in H10; eauto. 
    rewrite H10. rewrite Mult_P4 in H4; auto. 
    apply AxiomII; split; eauto. }
  assert (Ensemble a0); eauto. apply MKT44 in H11 as [H11 _].
  rewrite H10,H11; auto.
Qed.

(* 推论 加法与乘法联系的公理推论 *)
Corollary PlusMult_Co1 : ∀ x, x ∈ R -> x · 0 = 0.
Proof.
  intros. pose proof zero_in_R.
  assert (0 + 0 = 0). {apply Plus_P1; auto. }
  rewrite <- H1. pose proof (Mult_P5 0 0 x H0 H0 H). 
  rewrite H1 in *. rewrite Mult_P4; auto with real.
  assert (0 · x = ((0 · x) + (0 · x)) - (0 · x)).
  { rewrite <- Plus_P3; auto with real. 
    rewrite Minus_P1,Plus_P1; auto with real. } 
  rewrite <- H2 in H3. rewrite Minus_P1 in H3; auto with real.
Qed.

Corollary PlusMult_Co2 : ∀ x y, x ∈ R -> y ∈ R -> x · y = 0
  -> x = 0 \/ y = 0.
Proof.
  intros. destruct (classic (y = 0)); auto. left. (* 排中律 *)
  rewrite Mult_P4 in H1; auto with real.
  apply Mult_Co3 in H1; auto with real.
  assert (y⁻ ∈ R ~ [0]). 
  { apply Mult_inv1. apply MKT4'.
    split; auto. apply AxiomII. split; eauto. unfold NotIn.
    unfold not. intro. apply MKT41 in H3; eauto with real. }
  pose proof H3. apply MKT4' in H4 as [H4 _]. 
  rewrite Mult_P4, PlusMult_Co1 in H1; auto with real.  
  apply MKT4'. split; eauto. apply AxiomII; split; eauto.
  unfold NotIn. intro. apply MKT41 in H3; eauto with real.
Qed.

Corollary PlusMult_Co3 : ∀ x, x ∈ R -> -x = (-(1))· x.
Proof.
  intros. pose proof one_in_R_Co. 
  pose proof (Mult_P5 1 (-(1)) x ). apply H1 in H0; auto with real.
  pose proof one_in_R_Co. pose proof (Minus_P1 1 H2).
  rewrite H3 in H0. pose proof (PlusMult_Co1 x H). 
  rewrite Mult_P4 in H4; auto with real. rewrite H4 in H0.
  rewrite Mult_P4,Mult_P1 in H0; eauto with real.
  assert (x + (-(x)) = 0); auto with real. pose proof H. 
  apply Plus_Co2 in H as [x0[[]]].
  assert (x0 = - (1) · x). { apply H8. split; auto with real. }
  assert (x0 = - x). { apply H8. split; auto with real. }
  rewrite <- H9,H10; auto.
Qed.
   
Corollary PlusMult_Co4 : ∀ x, x ∈ R -> (-(1)) · (-x) = x.
Admitted.

Corollary PlusMult_Co5 : ∀ x, x ∈ R -> (-x) · (-x) = x · x.
Admitted.

Corollary PlusMult_Co6 : ∀ x, x ∈ (R ~ [0]) <-> (x⁻) ∈ (R ~ [0]).
Admitted.

Definition lt x y := x ≤ y /\ x <> y.

Notation "x < y" := (lt x y) : R_scope.

(* 推论 序公理推论 *)
Corollary Order_Co1 : ∀ x y, x ∈ R -> y ∈ R
  -> x < y \/ y < x \/ x = y.
Proof.
  intros. pose proof H. pose proof H0.
  destruct (classic (x = y)); auto.
  apply Leq_P1 in H1.
  pose proof (Leq_P4 x y H H0).
  destruct H4. unfold lt. auto.
  right. left. unfold lt. auto.
Qed.

Corollary Order_Co2 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> (x < y /\ y ≤ z) \/ (x ≤ y /\ y < z) -> x < z.
Proof.
  intros. destruct H2.
  - destruct H2. unfold lt in H2. destruct H2.
    destruct (classic (x = z)).
    unfold lt. split.
    pose proof (Leq_P3 x y z H H0 H1 H2 H3); auto.
    destruct H5.
Admitted. 

(* 推论 序与加法及乘法联系的公理推论 *)
Corollary OrderPM_Co1 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> x < y -> x + z < y + z.
Proof.
  intros. destruct H2. split. apply Plus_Leq; auto.
  intro. assert (x + z - z = y + z - z). { rewrite H4; auto. }
  rewrite <-Plus_P3,<-Plus_P3,Minus_P1,Plus_P1,Plus_P1 in H5;
  auto with real.
Qed.

Corollary OrderPM_Co2 : ∀ x, x ∈ R -> 0 < x -> (-x) < 0.
Proof.
  intros. apply (OrderPM_Co1 0 x (-x)) in H0; auto with real.
  rewrite Minus_P1,Plus_P4,Plus_P1 in H0; auto with real.
Qed.

Corollary OrderPM_Co3 : ∀ x y z w, x ∈ R -> y ∈ R -> z ∈ R
  -> w ∈ R -> x ≤ y -> z ≤ w -> x + z ≤ y + w.
Proof.
  intros. assert (x + z ≤ y + z). { apply Plus_Leq; auto. }
  assert (y + z ≤ y + w).
  { rewrite Plus_P4,(Plus_P4 y); auto. apply Plus_Leq; auto. }
  apply (Leq_P3 _ (y + z)); auto with real.
Qed.

Corollary OrderPM_Co4 : ∀ x y z w, x ∈ R -> y ∈ R -> z ∈ R
  -> w ∈ R -> x ≤ y -> z < w -> x + z < y + w.
Proof.
  intros. assert (x + z ≤ y + z). { apply Plus_Leq; auto. }
  assert (y + z < y + w).
  { rewrite Plus_P4,(Plus_P4 y); auto. apply OrderPM_Co1; auto. }
  destruct H6. split. apply (Leq_P3 _ (y + z)); auto with real.
  intro. rewrite H8 in H5. elim H7. apply Leq_P2; auto with real.
Qed.

Corollary OrderPM_Co5 : ∀ x y, x ∈ R -> y ∈ R
  -> (0 < x /\ 0 < y) \/ (x < 0 /\ y < 0) -> 0 < x · y.
Proof.
  intros. destruct H1 as [[[][]]|[[][]]]; split;
  try (intro; symmetry in H5; apply PlusMult_Co2 in H5 as []; auto).
  apply Mult_Leq; auto. apply (Plus_Leq x 0 (-x)) in H1;
  auto with real. apply (Plus_Leq y 0 (-y)) in H3; auto with real.
  rewrite Minus_P1 in H1,H3; auto.
  rewrite Plus_P4,Plus_P1 in H1,H3; auto with real.
  apply (Mult_Leq (-x)) in H3; auto with real.
  rewrite PlusMult_Co3,(PlusMult_Co3 y),Mult_P3,<-(Mult_P3 (-(1))),
  (Mult_P4 x),Mult_P3,PlusMult_Co4,(Mult_P4 1),Mult_P1 in H3;
  auto with real.
Qed.

Corollary OrderPM_Co6 : ∀ x y, x ∈ R -> y ∈ R -> x < 0 -> 0 < y
  -> x · y < 0.
Proof.
  intros. apply (OrderPM_Co1 x 0 (-x)) in H1; auto with real.
  rewrite Minus_P1,Plus_P4,Plus_P1 in H1; auto with real.
  assert (0 < (-x) · y). { apply OrderPM_Co5; auto with real. }
  rewrite PlusMult_Co3,<-Mult_P3,<-PlusMult_Co3 in H3;
  auto with real. apply (OrderPM_Co1 _ _ (x · y)) in H3;
  auto with real. rewrite Plus_P4,Plus_P1,Plus_P4,Minus_P1 in H3;
  auto with real.
Qed.

Corollary OrderPM_Co7 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x < y
  -> 0 < z -> x · z < y · z.
Proof.
  intros. apply (OrderPM_Co1 x y (-x)) in H2; auto with real.
  rewrite Minus_P1 in H2; auto.
  assert (0 < (y - x) · z). { apply OrderPM_Co5; auto with real. }
  rewrite Mult_P5 in H4; auto with real.
  apply (OrderPM_Co1 _ _ (x · z)) in H4; auto with real.
  rewrite Plus_P4,Plus_P1,<-Plus_P3,PlusMult_Co3,<-Mult_P3,
  <-PlusMult_Co3,(Plus_P4 (- (x · z))),Minus_P1,Plus_P1 in H4;
  auto with real.
Qed.

Corollary OrderPM_Co7b : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y
  -> 0 ≤ z -> x · z ≤ y · z.
Proof.
  intros. pose proof H0. apply (Order_Co1 x) in H4 as [H4|[]]; auto.
  pose proof H1. apply (Order_Co1 0) in H5 as [H5|[]];
  auto with real. apply (OrderPM_Co7 _ _ z) in H4; auto.
  destruct H4; auto. destruct H5. elim H6. apply Leq_P2;
  auto with real. rewrite <-H5,PlusMult_Co1,PlusMult_Co1; auto.
  apply Leq_P1; auto with real. destruct H4. elim H5.
  apply Leq_P2; auto. rewrite H4. apply Leq_P1; auto with real.
Qed.

Corollary OrderPM_Co8 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x < y
  -> z < 0 -> y · z < x · z.
Proof.
  intros. apply (OrderPM_Co1 z 0 (-z)) in H3; auto with real.
  rewrite Minus_P1,Plus_P4,Plus_P1 in H3; auto with real.
  apply (OrderPM_Co1 x y (-x)) in H2; auto with real.
  rewrite Minus_P1 in H2; auto.
  assert (0 < (y - x) · (-z)). { apply OrderPM_Co5; auto with real. }
  rewrite (PlusMult_Co3 z),Mult_P4,<-Mult_P3,<-PlusMult_Co3 in H4;
  auto with real. apply (OrderPM_Co1 _ _ (z · (y - x))) in H4;
  auto with real. rewrite Plus_P4,Plus_P1,
  (Plus_P4 (-(z · (y - x)))),Minus_P1 in H4; auto with real.
  rewrite Mult_P4,Mult_P5 in H4; auto with real.
  apply (OrderPM_Co1 _ _ (x · z)) in H4; auto with real.
  rewrite <-Plus_P3,(Plus_P4 (- x · z)),PlusMult_Co3,
  <-Mult_P3,<-PlusMult_Co3,Minus_P1,Plus_P1,Plus_P4,Plus_P1 in H4;
  auto with real.
Qed.

Corollary OrderPM_Co8b : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y
  -> z ≤ 0 -> y · z ≤ x · z.
Proof.
  intros. assert (0 ≤ (-z)).
  { pose proof zero_in_R. apply (Order_Co1 (-z)) in H4 as [H4|[]];
    auto with real. apply (OrderPM_Co1 _ _ z) in H4; auto with real.
    rewrite Plus_P4,Minus_P1,Plus_P4,Plus_P1 in H4; auto with real.
    destruct H4. elim H5. apply Leq_P2; auto with real.
    destruct H4; auto. rewrite H4. apply Leq_P1; auto with real. }
  apply (OrderPM_Co7b _ _ (-z)) in H2; auto with real.
  apply (OrderPM_Co3 _ _ (x · z) (x · z)) in H2; auto with real;
  [ |apply Leq_P1; auto with real].
  rewrite Mult_P4,(Mult_P4 x),<-Mult_P5,Plus_P4,Minus_P1,
  Mult_P4,PlusMult_Co1 in H2; auto with real.
  apply (OrderPM_Co3 _ _ (y · z) (y · z)) in H2; auto with real;
  [ |apply Leq_P1; auto with real].
  rewrite Plus_P4,Plus_P1,Plus_P4,Plus_P3,Mult_P4,(Mult_P4 y),
  <-Mult_P5,Plus_P4,Minus_P1,(Mult_P4 0),PlusMult_Co1,Plus_P1,
  Mult_P4,(Mult_P4 z) in H2; auto with real.
Qed.

Corollary OrderPM_Co9 : 0 < 1.
Proof.
  pose proof zero_in_R. pose proof one_in_R.
  apply MKT4' in H0 as []. apply AxiomII in H1 as [].
  pose proof H. apply (Order_Co1 0 1) in H3 as [H3|[|]]; auto.
  - assert (0 < 1 · 1). { apply OrderPM_Co5; auto. }
    rewrite Mult_P1 in H4; auto.
  - elim H2. apply MKT41; eauto.
Qed.

Corollary OrderPM_Co10 : ∀ x, x ∈ R -> 0 < x -> 0 < (x⁻).
Proof.
  intros. assert (x <> 0).
  { intro. rewrite H1 in H0. destruct H0; auto. }
  assert (x ∈ (R ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H2; eauto with real. }
  assert (x · (x⁻) = 1). { apply Divide_P1; auto. }
  assert ((x⁻) ∈ R).
  { apply Mult_inv1 in H2. apply MKT4' in H2; tauto. }
  pose proof zero_in_R. apply (Order_Co1 0 (x⁻)) in H5 as [H5|[|]];
  auto. apply (OrderPM_Co6 (x⁻) x) in H5; auto.
  rewrite Mult_P4,H3 in H5; auto. destruct H5.
  destruct OrderPM_Co9. elim H8. apply Leq_P2; auto with real.
  rewrite <-H5,PlusMult_Co1 in H3; auto. pose proof one_in_R.
  apply MKT4' in H6 as []. apply AxiomII in H7 as []. elim H8.
  apply MKT41; eauto with real.
Qed.

Corollary OrderPM_Co11 : ∀ x y, x ∈ R -> y ∈ R -> 0 < x -> x < y
  -> 0 < (y⁻) /\ (y⁻) < (x⁻).
Proof.
  intros. assert (0 < y).
  { destruct H1,H2. split. apply (Leq_P3 0 x y); auto with real.
    intro. rewrite H5 in H1. elim H4. apply Leq_P2; auto. }
  split. apply OrderPM_Co10; auto.
  assert (0 < (x⁻) /\ 0 < (y⁻)) as [].
  { split; apply OrderPM_Co10; auto. }
  assert (x ∈ (R ~ [0]) /\ y ∈ (R ~ [0])) as [].
  { split; apply MKT4'; split; auto; apply AxiomII; split; eauto;
    intro; apply MKT41 in H6; eauto with real;
    [rewrite H6 in H1; destruct H1|rewrite H6 in H3; destruct H3];
    auto. }
  pose proof H6; pose proof H7. apply Mult_inv1 in H8,H9.
  apply MKT4' in H8 as [H8 _]. apply MKT4' in H9 as [H9 _].
  pose proof H2. apply (OrderPM_Co7 x y (x⁻)) in H10; auto.
  rewrite Divide_P1 in H10; auto.
  apply (OrderPM_Co7 _ _ (y⁻)) in H10; auto with real.
  rewrite Mult_P4,Mult_P1,Mult_P4,Mult_P3,(Mult_P4 _ y),
  Divide_P1,Mult_P4,Mult_P1 in H10; auto with real.
Qed.

(* 完备公理与数集确界的存在性 *)
Definition Upper X c := X ⊂ R /\ c ∈ R /\ (∀ x, x ∈ X -> x ≤ c).

Definition Lower X c := X ⊂ R /\ c ∈ R /\ (∀ x, x ∈ X -> c ≤ x).

Definition Bounded X := ∃ c1 c2, Upper X c1 /\ Lower X c2.

Definition Max X c := X ⊂ R /\ c ∈ X /\ (∀ x, x ∈ X -> x ≤ c).

Definition Min X c := X ⊂ R /\ c ∈ X /\ (∀ x, x ∈ X -> c ≤ x).

Corollary Max_Corollary : ∀ X c1 c2, Max X c1 -> Max X c2 -> c1 = c2.
Proof.
  intros. unfold Max in H,H0. destruct H as [H[]].
  destruct H0 as [H0[]]. pose proof H1. pose proof H3.
  unfold Included in H. apply H in H1. apply H in H3.
  apply H4 in H5. apply H2 in H6.
  pose proof (Leq_P2 c1 c2 H1 H3 H5 H6). auto.
Qed.

Corollary Min_Corollary : ∀ X c1 c2, Min X c1 -> Min X c2 -> c1 = c2.
Proof.
  intros. unfold Min in H,H0. destruct H as [H[]].
  destruct H0 as [H0[]]. pose proof H1. pose proof H3.
  unfold Included in H. apply H in H1. apply H in H3.
  apply H4 in H5. apply H2 in H6.
  pose proof (Leq_P2 c1 c2 H1 H3 H6 H5). auto.
Qed.

Definition Sup1 X s := Upper X s /\ (∀ s1, s1 ∈ R -> s1 < s
  -> (∃ x1, x1 ∈ X /\ s1 < x1)).

Definition Sup2 X s := Min (\{ λ u, Upper X u \}) s.

Corollary Sup_Corollary : ∀ X s, Sup1 X s <-> Sup2 X s.
Admitted.

Definition Inf1 X i := Lower X i /\ (∀ i1, i1 ∈ R -> i < i1
  -> (∃ x1, x1 ∈ X /\ x1 < i1)).

Definition Inf2 X i := Max (\{ λ u, Lower X u \}) i.

Corollary Inf_Corollary : ∀ X i, Inf1 X i <-> Inf2 X i.
Admitted.

Theorem SupT : ∀ X, X ⊂ R -> X <> Φ -> ∃ c, Upper X c
  -> exists ! s, Sup1 X s.
Admitted.

Theorem InfT : ∀ X, X ⊂ R -> X <> Φ -> ∃ c, Lower X c
  -> exists ! i, Inf1 X i.
Admitted.

(* 自然数集的定义 *)
(* 归纳集的定义 *)
Definition IndSet X := X ⊂ R /\ (∀ x, x ∈ X -> (x + 1) ∈ X).

Proposition IndSet_P1 : ∀ X, X <> Φ -> (∀ x, x ∈ X -> IndSet x)
  -> IndSet (∩X).
Admitted.

(* 自然数集 *)
Definition N := ∩(\{ λ u, IndSet u /\ 1 ∈ u \}).

Corollary N_Subset_R : N ⊂ R.
Proof.
  unfold Included; intros. apply AxiomII in H as [].
  assert (R ∈ \{ λ u, IndSet u /\ 1 ∈ u \}).
  { apply AxiomII; repeat split; auto with real. apply Ensemble_R. }
  apply H0 in H1; auto.
Qed.

Corollary one_in_N : 1 ∈ N.
Proof.
  apply AxiomII; split; eauto with real. intros.
  apply AxiomII in H as [H[]]; auto.
Qed.

Global Hint Resolve N_Subset_R one_in_N : real.

(* 数学归纳原理 *)
Theorem MathInd : ∀ E, E ⊂ N -> 1 ∈ E -> (∀ x, x ∈ E
  -> (x + 1) ∈ E) -> E = N.
Admitted.

(* 自然数的性质 *)
Proposition Nat_P1 : ∀ m n, m ∈ N -> n ∈ N
  -> (m + n) ∈ N /\ (m · n) ∈ N.
Admitted.

Proposition Nat_P2 : ∀ n, n ∈ N -> n <> 1 -> (n - 1) ∈ N.
Admitted.

(* 书打错集合里的n应该是x *)
Proposition Nat_P3 : ∀ n, n ∈ N
  -> Min (\{ λ u, u ∈ N /\ n < u \}) (n + 1).
Admitted.

Proposition Nat_P4 : ∀ m n, m ∈ N -> n ∈ N -> n < m -> (n + 1) ≤ m.
Admitted.

Proposition Nat_P5 : ∀ n, n ∈ N
  -> ~ (∃ x, x ∈ N /\ n < x /\ x < (n + 1)).
Admitted.

(* 书上和性质2有重复 *)
Proposition Nat_P6 : ∀ n, n ∈ N -> n <> 1
  -> ~ (∃ x, x ∈ N /\ (n - 1) < x /\ n < x).
Admitted.

Proposition Nat_P7 : ∀ E, E ⊂ N -> E <> Φ -> ∃ n, Min E n.
Admitted.

(* 整数的定义 *)
Definition Z := N ∪ \{ λ u, (-u) ∈ N \} ∪ [0].

(* 整数的性质 *)

Corollary Z_Corollary : N ⊂ Z /\ Z ⊂ R.
Proof.
  split.
  - unfold Included; intros. apply AxiomII; repeat split; eauto.
  - unfold Included; intros. unfold Z in H.
    apply MKT4 in H as []; auto with real. 
    apply MKT4 in H as []. apply AxiomII in H as [].
    apply N_Subset_R in H0. apply NNPP. intro.
    assert (\{ λ u, u ∈ R /\ u + z = 0 \} = Φ).
    { apply AxiomI; split; intros. apply AxiomII in H2 as [H2[]].
      assert ([z0,z] ∉ (dom( fp ))).
      { destruct PlusR as [H5[]]. unfold NotIn. intro.
        rewrite H6 in H8. apply AxiomII' in H8 as [H8[]].
        auto. } 
      apply MKT69a in H5. rewrite H4 in H5. pose proof zero_in_R.
      rewrite H5 in H6. pose proof MKT39. elim H7. eauto.
      apply MKT16 in H2. destruct H2. }
    assert (∩(\{ λ u, u ∈ R /\ u + z = 0 \}) = μ).
    { rewrite H2. apply MKT24. }
    rewrite H3 in H0. pose proof MKT39. elim H4. eauto.
    apply MKT41 in H; eauto with real. rewrite H. apply zero_in_R.
Qed.

Lemma Int_P1_Lemma : ∀ m n, m ∈ N -> n ∈ N -> m < n 
  -> (n - m) ∈ N.
Admitted.


Proposition Int_P1a : ∀ m n, m ∈ Z -> n ∈ Z
  -> (m + n) ∈ Z.
Proof.
  intros. pose proof H. pose proof H0.
  apply Z_Corollary in H1,H2.
  assert (Ensemble (m + n)).
  { pose proof (Plus_close m n H1 H2). eauto. }
  assert (∀ a b, Ensemble (a+b) -> a ∈ \{ λ u, (-u) ∈ N \} 
    -> b ∈ Z -> a + b ∈ Z).
  { intros a b H' H4 H5.
    apply AxiomII in H4 as []. apply MKT4 in H5 as [].
    assert (b < -a \/ -a < b \/ b = -a) as [H7|[]].
    { apply Order_Co1; auto with real. }
    + pose proof (Int_P1_Lemma b (-a) H5 H6 H7).
      rewrite PlusMult_Co3,(PlusMult_Co3 b),
      Mult_P4,(Mult_P4 _ b), <- Mult_P5, Mult_P4, 
      <- PlusMult_Co3 in H8; auto with real.
      apply MKT4. right. apply MKT4. left.
      apply AxiomII; auto.
    + pose proof (Int_P1_Lemma (-a) b H6 H5 H7).
      assert (a = --a). 
      { rewrite PlusMult_Co3,PlusMult_Co4; auto with real. }
      rewrite <- H9,Plus_P4 in H8; auto with real.
      apply Z_Corollary; auto.
    + rewrite H7. rewrite Minus_P1; auto with real.
      apply MKT4. right. apply MKT4. right.
      apply MKT41; eauto with real.
    + apply MKT4 in H5 as []. apply AxiomII in H5 as [].
      apply MKT4. right. apply MKT4. left. apply AxiomII.
      split; auto. rewrite PlusMult_Co3,Mult_P4,Mult_P5,
      Mult_P4,(Mult_P4 b),<- PlusMult_Co3, <- PlusMult_Co3;
      auto with real. apply Nat_P1; auto.
      apply MKT41 in H5; eauto with real. rewrite H5.
      rewrite Plus_P1; auto with real.
      apply MKT4. right. apply MKT4. left.
      apply AxiomII; auto. }
  apply MKT4 in H as []. apply MKT4 in H0 as []. 
  apply Z_Corollary. apply Nat_P1; auto with real.
  apply MKT4 in H0 as []. 
  rewrite Plus_P4; auto. apply (H4 n m); auto.
  rewrite Plus_P4; auto. apply Z_Corollary; auto.
  apply MKT41 in H0; eauto with real. rewrite H0.
  rewrite Plus_P1; auto with real. apply Z_Corollary; auto.
  apply MKT4 in H as []; auto.
  apply MKT41 in H; eauto with real. rewrite H.
  rewrite Plus_P4,Plus_P1; auto with real. 
Qed.


Proposition Int_P1b : ∀ m n, m ∈ Z -> n ∈ Z
  -> (m · n) ∈ Z.
Proof.
  intros. pose proof H. pose proof H0.
  apply Z_Corollary in H1,H2.
  assert (Ensemble (m · n)).
  { pose proof (Mult_close m n H1 H2). eauto. }
  assert (∀ a b, Ensemble (a · b) -> a ∈ [0]
    -> b ∈ Z -> a · b ∈ Z).
  { intros a b H' H4 H5. pose proof H5.
    apply Z_Corollary in H5.
    apply MKT41 in H4; eauto with real.
    rewrite H4,Mult_P4,PlusMult_Co1; auto with real.
    pose proof zero_in_R.
    apply AxiomII; split; eauto. right. apply MKT4. right.
    apply MKT41; eauto. }
  assert (∀ a b, Ensemble (a · b) -> a ∈ \{ λ u, (-u) ∈ N \} 
    -> b ∈ Z -> a · b ∈ Z).
  { intros a b H' H5 H6. apply AxiomII in H5 as [].
    pose proof H6. apply Z_Corollary in H8.
    apply MKT4 in H6 as [].
    pose proof (Nat_P1 (-a) b H7 H6) as [ ].
    rewrite PlusMult_Co3,<- Mult_P3,<- PlusMult_Co3 in H10; 
    auto with real.
    apply AxiomII. split; auto. right. apply MKT4. left.
    apply AxiomII; auto.
    apply MKT4 in H6 as []. apply AxiomII in H6 as [].
    pose proof (Nat_P1 (-a) (-b) H7 H9) as [].
    rewrite PlusMult_Co3 in H11; auto with real.
    assert (- (1) · a = a · -(1)). 
    { apply Mult_P4; auto with real. }
    rewrite H12,<- Mult_P3,(PlusMult_Co4 b) in H11; 
    auto with real. apply MKT4. left; auto.
    rewrite Mult_P4; auto with real. apply (H4 b a); auto.
    rewrite Mult_P4; auto with real.
    apply MKT4. right. apply MKT4. left. apply AxiomII; auto. }  
  apply MKT4 in H as []. apply MKT4 in H0 as [].
  apply Z_Corollary. apply Nat_P1; auto with real.
  apply MKT4 in H0 as [].
  rewrite Mult_P4; auto. apply (H5 n m); auto.
  rewrite Mult_P4; auto. apply Z_Corollary in H; auto.
  rewrite Mult_P4; auto. apply (H4 n m); auto.
  rewrite Mult_P4; auto. apply Z_Corollary in H; auto.
  apply MKT4 in H as []; auto.
Qed.

Proposition Int_P2 : ∀ n, n ∈ Z -> n + 0 = n /\ 0 + n = n.
Proof.
  intros; split.
  - apply Z_Corollary in H. apply Plus_P1; auto.
  - apply Z_Corollary in H.
    assert (0 + n = n + 0). { apply Plus_P4; auto with real. }
    rewrite H0. apply Plus_P1; auto.
Qed.

Proposition Int_P3 : ∀ n, n ∈ Z -> (-n) ∈ Z /\ n + (-n) = 0
  /\ (-n) + n = 0.
Proof.
  intros; repeat split.
  - apply AxiomII in H as [H[]]. apply AxiomII. split.
    apply N_Subset_R in H0. apply Plus_neg1a in H0; eauto.
    right. apply MKT4. left. pose proof H0. apply N_Subset_R in H0. 
    apply Plus_neg1a in H0. apply AxiomII; split; eauto.
    assert (n = --n). 
    { rewrite PlusMult_Co3,PlusMult_Co4; auto with real. }
    rewrite <- H2; auto.
    apply MKT4 in H0 as []. apply AxiomII in H0. destruct H0.
    apply Z_Corollary in H1; auto. 
    pose proof zero_in_R. apply MKT41 in H0; eauto. rewrite H0.
    pose proof one_in_R_Co.
    pose proof (Plus_neg1a 1 H2).
    pose proof (PlusMult_Co1 (-(1)) H3).
    pose proof (PlusMult_Co3 0 H1). rewrite H4 in H5.
    rewrite H5. rewrite H0 in H. apply AxiomII.
    split; auto. right. apply MKT4. right. apply MKT41; auto.
  - apply Z_Corollary in H. apply Plus_neg2; auto.
  - apply Z_Corollary in H.
    assert (- n + n = n + (-n) ). 
    { apply Plus_P4; auto with real. }
    rewrite H0. apply Plus_neg2; auto.
Qed.


Proposition Int_P4 : ∀ m n k, m ∈ Z -> n ∈ Z -> k ∈ Z
  -> m + (n + k) = (m + n) + k.
Proof.
  intros. apply Z_Corollary in H,H0,H1. 
  apply Plus_P3; auto with real.
Qed.

Proposition Int_P5 : ∀ m n, m ∈ Z -> n ∈ Z -> m + n = n + m.
Proof.
  intros. apply Z_Corollary in H,H0. 
  apply Plus_P4; auto with real.
Qed.

(* 有理数的定义 *)
Definition Q := \{ λ u, ∃ m n, m ∈ Z /\ n ∈ (Z ~ [0])
  /\ u = m / n \}.
 
Corollary Q_Corollary : Z ⊂ Q /\ Q ⊂ R.
Proof.
  split.
  - unfold Included; intros.
    apply AxiomII; split; eauto.
    exists z,1; split. auto. split.
    apply MKT4'. split. apply Z_Corollary,one_in_N.
    apply AxiomII; split. unfold Ensemble. 
    exists N. apply one_in_N.
    unfold NotIn. intro. pose proof one_in_R. 
    apply MKT4' in H1 as []. apply AxiomII in H2 as [].
    contradiction. symmetry. apply Divide_P2.
    apply Z_Corollary; auto.
  - unfold Included; intros. 
    apply AxiomII in H as [H[m[n[H0[]]]]].
    apply MKT4' in H1 as []. apply Z_Corollary in H0,H1.
    rewrite H2. apply Mult_close; auto.
    assert (n ∈ R ~ [0]). { apply MKT4'; auto. }
    apply Mult_inv1 in H4. apply MKT4' in H4; tauto.
Qed.

Proposition Frac_P1 : ∀ m n k, m ∈ R -> n ∈ (R ~ [0])
  -> k ∈ (R ~ [0]) -> m / n = (m · k) / (n · k).
Admitted.


Proposition Frac_P2 : ∀ m n k t, m ∈ R -> n ∈ (R ~ [0])
  -> k ∈ R -> t ∈ (R ~ [0])
  -> (m / n) · (k / t) = (m · k) / (n · t).
Admitted.

Proposition Rat_P1 : ∀ x y, x ∈ Q -> y ∈ Q
  -> (x + y) ∈ Q /\ (x · y) ∈ Q.
Admitted.

Proposition Rat_P2 : ∀ x, x ∈ Q -> x + 0 = x /\ 0 + x = x.
Proof.
  intros; split.
  - apply Q_Corollary in H. apply Plus_P1; auto.
  - apply Q_Corollary in H.
    assert (0 + x = x + 0). 
    { apply Plus_P4; auto with real. }
    rewrite H0. apply Plus_P1; auto.
Qed.

Proposition Rat_P3 : ∀ n, n ∈ Q -> (-n) ∈ Q /\ n + (-n) = 0
  /\ (-n) + n = 0.
Admitted.

Proposition Rat_P4 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> x + (y + z) = (x + y) + z.
Proof.
  intros. apply Q_Corollary in H,H0,H1.
  apply Plus_P3; auto with real.
Qed.

Proposition Rat_P5 : ∀ x y, x ∈ Q -> y ∈ Q -> x + y = y + x.
Proof.
  intros. apply Q_Corollary in H,H0.
  apply Plus_P4; auto with real.
Qed.

Proposition Rat_P6 : ∀ x, x ∈ Q -> x · 1 = x /\ 1 · x = x.
Proof.
  intros. apply Q_Corollary in H.
  split. apply Mult_P1; auto with real.
  rewrite Mult_P4; auto with real.
  apply Mult_P1; auto with real.
Qed.

Proposition Rat_P7 : ∀ x, x ∈ (Q ~ [0])
  -> (x⁻) ∈ Q /\ x · (x⁻) = 1.
Admitted.

Proposition Rat_P8 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> x · (y · z) = (x · y) · z.
Proof.
  intros. apply Q_Corollary in H,H0,H1.
  apply Mult_P3; auto with real.
Qed.

Proposition Rat_P9 : ∀ x y, x ∈ Q -> y ∈ Q -> x · y = y · x.
Proof.
  intros. apply Q_Corollary in H,H0.
  apply Mult_P4; auto with real.
Qed.

Proposition Rat_P10 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> (x + y) · z = (x · z) + (y · z).
Proof.
  intros. apply Q_Corollary in H,H0,H1.
  apply Mult_P5; auto with real.
Qed.

Theorem Existence_of_irRational_Number : (R ~ Q) <> Φ.
Admitted.
  

(* 阿基米德原理 *)
Proposition Arch_P1 : ∀ E, E ⊂ N -> E <> Φ -> Bounded E
  -> ∃ n, Max E n.
Admitted.

Proposition Arch_P2 : ~ ∃ n, Upper N n.
Admitted.

Proposition Arch_P3 : ∀ E, E ⊂ Z -> E <> Φ -> (∃ x, Upper E x)
  -> ∃ n, Max E n.
Admitted.

Proposition Arch_P4 : ∀ E, E ⊂ N -> E <> Φ -> Bounded E
  -> ∃ n, Min E n.
Admitted.

Proposition Arch_P5 : ~ (∃ n, Lower Z n) /\ ~ (∃ n, Upper Z n).
Admitted.

Proposition Arch_P6 : ∀ h x, h ∈ R -> 0 < h -> x ∈ R
  -> (exists ! k, (k - 1) · h ≤ x /\ x < k · h).
Admitted.

Proposition Arch_P7 : ∀ x, x ∈ R -> 0 < x
  -> (∃ n, n ∈ N /\ 0 < 1 / n /\ 1 / n < x).
Admitted.

Proposition Arch_P8 : ∀ x, x ∈ R -> 0 ≤ x
  -> (∀ n, n ∈ N -> x < 1 / n) -> x = 0.
Admitted.

Proposition Arch_P9 : ∀ a b, a ∈ R -> b ∈ R -> a < b
  -> (∃ r, r ∈ Q /\ a < r /\ r < b).
Admitted.

Proposition Arch_P10 : ∀ x, x ∈ R
  -> (exists ! k, k ∈ Z /\ k ≤ x /\ x < k + 1).
Admitted.

(* 实数的几何解释 *)
(* 有界区间 *)
(* 开区间 *)
Notation "］ a , b ［" := (\{ λ x, x ∈ R /\ a < x /\ x < b \})
  (at level 5, a at level 0, b at level 0) : R_scope.

(* 闭区间 *)
Notation "［ a , b ］" := (\{ λ x, x ∈ R /\ a ≤ x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0) : R_scope.

(* 左开右闭 *)
Notation "］ a , b ］" := (\{ λ x, x ∈ R /\ a < x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0) : R_scope.

(* 左闭右开 *)
Notation "［ a , b ［" := (\{ λ x, x ∈ R /\ a ≤ x /\ x < b \})
  (at level 5, a at level 0, b at level 0) : R_scope.

(* 无界区间 *)
Notation "］ a , +∞［" := (\{ λ x, x ∈ R /\ a < x \})
  (at level 5, a at level 0) : R_scope.

Notation "［ a , +∞［" := (\{ λ x, x ∈ R /\ a ≤ x \})
  (at level 5, a at level 0) : R_scope.

Notation "］-∞ , b ］" := (\{ λ x, x ∈ R /\ x ≤ b \})
  (at level 5, b at level 0) : R_scope.

Notation "］-∞ , b ［" := (\{ λ x, x ∈ R /\ x < b \})
  (at level 5, b at level 0) : R_scope.

Notation "]-∞ , +∞[" := (R)(at level 0) : R_scope.

(* 邻域 *)
Definition Neighbourhood x δ := x ∈ R /\ δ ∈ R
  /\ x ∈ ］(x - δ),(x + δ)［.

(* 绝对值函数 *)
Definition Abs := \{\ λ u v, u ∈ R
  /\ ((0 ≤ u /\ v = u) \/ (u < 0 /\ v = (-u))) \}\.

Corollary Abs_Corollary : Function Abs /\ dom(Abs) = R
  /\ ran(Abs) = \{ λ x, x ∈ R /\ 0 ≤ x \}.
Proof.
  repeat split.
  - unfold Function. unfold Relation. intros. 
    apply AxiomII in H as [H[x[y[]]]]. exists x,y; auto.
  - intros. appoA2H H. appoA2H H0.
    destruct H1 as [H1[]]; destruct H2 as [H2[]].
    destruct H3,H4. rewrite <- H6 in H5; auto.
    destruct H3,H4. unfold lt in H4. destruct H4.
    pose proof zero_in_R.
    pose proof (Leq_P2 0 x H8 H1 H3 H4); destruct H7; auto.
    destruct H3,H4. unfold lt in H3. destruct H3.
    pose proof zero_in_R.
    pose proof (Leq_P2 0 x H8 H1 H4 H3); destruct H7; auto.
    destruct H3,H4. rewrite <- H6 in H5; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H. destruct H as [H[]].
      apply AxiomII' in H0; tauto. 
    + apply AxiomII; split; eauto. pose proof zero_in_R.
      pose proof (Order_Co1 0 z H0 H). destruct H1.
      exists z. apply AxiomII'; repeat split; eauto.
      apply MKT49a; eauto.
      left; split; auto. unfold lt in H1. tauto.
      destruct H1. exists (-z).
      apply AxiomII'; repeat split; eauto.
      pose proof (Plus_neg1a z H). apply MKT49a; eauto.
      exists 0. apply AxiomII'; split; auto.
      apply MKT49a; eauto. split; auto.
      left; split. rewrite <- H1. apply Leq_P1; auto. auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H. destruct H as [H[]].
      apply AxiomII' in H0 as [H0[]]. 
      destruct H2,H2. rewrite H3. apply AxiomII; eauto.
      apply AxiomII; split; auto. split.
      rewrite H3. apply Plus_neg1a; auto.
      pose proof (Plus_neg1a x H1).
      assert (x = --x). 
      { rewrite PlusMult_Co3,PlusMult_Co4; auto with real. }
      rewrite H5 in H2. rewrite <- H3 in H2. rewrite <- H3 in H4.
      pose proof H4. apply Plus_neg1a in H6.
      pose proof zero_in_R.
      assert (- z + z < 0 + z ).
      { apply OrderPM_Co1; auto with real.  }
      pose proof (Plus_neg2 z H4). 
      rewrite Plus_P4 in H8; auto with real. rewrite H9 in H8.
      pose proof (Plus_P1 z H4). 
      rewrite Plus_P4 in H10; auto with real.
      rewrite H10 in H8. unfold lt in H8. tauto.
    + apply AxiomII; split; eauto.
      exists z. apply AxiomII'; split.
      apply MKT49a; eauto. split.
      apply AxiomII in H. tauto.
      left. split; auto. apply AxiomII in H as [H[]]; auto.
Qed.

Notation "｜ x ｜" := (Abs[x])(at level 5, x at level 0) : R_scope.

Definition Distance x y := ｜(x - y)｜.

(* 绝对值的性质 *)
Proposition Abs_P1 : ∀ x, x ∈ R -> 0 ≤ ｜x｜ /\ (｜x｜ = 0 <-> x = 0).
Admitted.

Proposition Abs_P2 : ∀ x, x ∈ R -> ｜x｜ = ｜(-x)｜ /\ -｜x｜ ≤ x
  /\ x ≤ ｜x｜.
Admitted.

Proposition Abs_P3 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x · y)｜ = ｜x｜ · ｜y｜.
Admitted.

Proposition Abs_P4 : ∀ x y, x ∈ R -> y ∈ R -> 0 < y
  -> ｜x｜ ≤ y <-> -y ≤ x /\ x ≤ y.
Admitted.

Proposition Abs_P5 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x + y)｜ ≤ ｜x｜ + ｜y｜
  /\ ｜(x - y)｜ ≤ ｜x｜ + ｜y｜ /\ ｜(｜x｜ - ｜y｜)｜ ≤ ｜(x - y)｜.
Admitted.

Proposition Abs_P6 : ∀ x y, x ∈ R -> y ∈ R
  -> ｜(x - y)｜ = 0 <-> x = y.
Admitted.

Proposition Abs_P7 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x - y)｜ = ｜(y - x)｜.
Admitted.

Proposition Abs_P8 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> ｜(x - y)｜ ≤ ｜(x - z)｜ + ｜(z - y)｜.
Admitted.

























