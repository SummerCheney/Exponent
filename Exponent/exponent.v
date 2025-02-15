Require Export R_Axioms.


(*数学归纳法*)
Theorem Mathematical_Induction : ∀ (P :Class -> Prop), P 1
  -> (∀ k, k ∈ N -> P k -> P (k+1)) -> (∀ n, n ∈ N -> P n).
Proof.
  intros. assert (\{λ x, x ∈ N /\ P x \} = N).
  { apply MathInd. unfold Included. intros.
    - apply AxiomII in H2; tauto.
    - apply AxiomII; split; eauto. pose proof one_in_N; eauto. 
      pose proof one_in_N; eauto.
    - intros. apply AxiomII in H2. destruct H2 as [H3[]].
      pose proof one_in_N. apply AxiomII.
      assert (x + 1 ∈ N).
      { pose proof (Nat_P1 x 1 H2 H5). tauto. }
      repeat split; eauto. }
  rewrite <-H2 in H1. apply AxiomII in H1; tauto.
Qed.

Corollary zero_not_in_N : 0 ∉ N.
Proof.
  intro. apply AxiomII in H as [].
  assert (\{ λ u, u ∈ R /\ 0 < u \} ⊂ R).
  { unfold Included; intros. apply AxiomII in H1 as []. 
    tauto. }
  assert (\{ λ u, u ∈ R /\ 0 < u \}
    ∈ \{ λ u, IndSet u /\ 1 ∈ u \}).
  { apply AxiomII; repeat split; auto. apply (MKT33 R); auto.
    apply Ensemble_R.
    intros. apply AxiomII in H2 as [H2[]].
    apply AxiomII; split; eauto with real. 
    split; auto with real. destruct H4.
    apply (OrderPM_Co4 0 x 0 1) in H4; auto with real.
    rewrite Plus_P1 in H4; auto with real. apply OrderPM_Co9.
    apply AxiomII; split; [ |split]; eauto with real. 
    apply OrderPM_Co9. }
  apply H0 in H2. apply AxiomII in H2 as [_[_[]]].
  auto.
Qed.

Theorem FAA3 : ∀ x, x ∈ N -> x + 1 <> 1.
Proof.
  intros. intro. pose proof H. apply N_Subset_R in H.
  assert((x + 1) - 1 = 1 - 1).
  { rewrite H0. auto. }
  rewrite <- Plus_P3 in H2; auto with real.
  pose proof one_in_R. apply AxiomII in H3 as [[]].
  destruct H4. assert (1 - 1 = 0).
  { apply Plus_neg2. auto. }
  rewrite H6 in H2. rewrite Plus_P1 in H2; auto with real.
  rewrite H2 in H1. pose proof zero_not_in_N. destruct H7.
  auto.
Qed.

Theorem FAA4 : ∀ x y, x ∈ N -> y ∈ N ->  x + 1 = y + 1
  -> x = y.
Proof.
  intros. pose proof H. pose proof H0.
  apply N_Subset_R in H,H0.
  assert ((x + 1) - 1 = (y + 1) - 1).
  { rewrite H1. auto. }
  rewrite <- Plus_P3 in H4; auto with real.
  assert (y + 1 - 1 = y + (1 - 1)).
  { rewrite <- Plus_P3; auto with real. }
  rewrite H5 in H4. pose proof one_in_R. 
  apply AxiomII in H6 as [[]].
  destruct H7. assert (1 - 1 = 0).
  { apply Plus_neg2. auto. }
  rewrite H9 in H4. rewrite Plus_P1 in H4; auto with real.
  assert (y + 0 = y). { rewrite Plus_P1; auto with real. }
  rewrite H10 in H4. auto.
Qed.
  

(*递归定理*)
Theorem Recursion : ∀ h x, Function h -> dom(h) = R 
  -> ran(h) ⊂ R -> x ∈ R 
  -> (exists ! f, Function f /\ dom(f) = N /\ ran(f) ⊂ R 
  /\ f[1] = x /\ (∀ n, n ∈ N -> f[n+1] = h[(f[n])])).
Proof.
(* 定义N到R的归纳关系 *)
  intros. set (Ind r := r ⊂ (N × R) /\ [1,x] ∈ r
    /\ (∀ n x, n ∈ N -> x ∈ R -> [n,x] ∈ r
      -> [n+1,h[x]] ∈ r)).
(* 定义f是N到R的最小归纳关系 *)
  set (f := \{\ λ u v, [u,v] ∈ (N × R)
    /\ (∀ r, Ind r -> [u,v] ∈ r) \}\).
  assert (Ensemble x). eauto. pose proof FAA3.
  assert (Ensemble 1). { pose proof one_in_R; eauto. }
  assert (∀ r, Ind r -> f ⊂ r).
  { unfold Included; intros.
    apply AxiomII in H7 as [_[x1[y1[H8[]]]]]. 
    rewrite H8; auto. }
  assert ([1,x] ∈ f).
  { apply AxiomII'.
    assert (Ensemble ([1,x])); auto.
    repeat split; auto. apply AxiomII'; repeat split; eauto.
    apply one_in_N. intros. unfold Ind in H8; tauto. }
  assert (Ind f).
  { repeat split; auto. unfold Included. intros. 
    - apply AxiomII in H8 as [_[x1[y1[H8[]]]]]. 
      rewrite H8; auto.
    - intros. pose proof H8. 
      assert (n + 1 ∈ N). 
      { pose proof one_in_N. pose proof (Nat_P1 n 1 H11 H12).
        tauto. }
      pose proof H9. rewrite <-H0 in H13.
      apply Property_Value in H13; auto. 
      apply Property_ran in H13. 
      assert (Ensemble ([n + 1,(h[x0])])).
      { apply MKT49a; eauto. }
      apply AxiomII'. repeat split. auto.
      apply AxiomII'; repeat split; auto.
      intros. pose proof H15. apply H6 in H15.
      apply H15 in H10. destruct H16 as [_[]].
      apply H17; auto. }
(*用归纳 证明矛盾 从而证明f的单值性*)
  assert (∀ m, m ∈ N -> exists ! x, x ∈ R /\ [m,x] ∈ f).
  { apply Mathematical_Induction.
    - exists x. split; auto.
      intros x1 []. apply NNPP; intro.
      set(f' := f ~ [[1,x1]]).
      assert (Ind f').
      { repeat split; unfold Included; intros.
        - destruct H8. apply H8. apply MKT4' in H12 as [].
          auto.           
        - apply MKT4'. split; auto.
          apply AxiomII; split; auto.
          intro. apply MKT41 in H12; eauto.
          apply MKT55 in H12 as []; auto.
        - apply MKT4' in H14 as []. destruct H8 as [H8[]].
          apply H17 in H14; auto. apply MKT4'; split; auto.
          apply AxiomII; split; eauto.
          intro. apply MKT41 in H18; eauto.
          assert (Ensemble ([(n+1),(h[x0])])); eauto.
          apply MKT49b in H19 as [].
          apply MKT55 in H18 as []; auto.
          elim (H4 n); auto. }
      apply H6 in H12. apply H12 in H10.
      apply MKT4' in H10 as [_]. apply AxiomII in H10 as []. 
      elim H13. apply MKT41; eauto.
    - intros m H9. intros [x0[[]]].
       assert (h[x0] ∈ R).
      { apply H1. apply (@ Property_ran x0).
        apply Property_Value; auto.
        rewrite H0; auto. }
      pose proof H9. assert (m + 1 ∈ N). 
      { pose proof one_in_N.
        pose proof (Nat_P1 m 1 H9 H15). tauto. }
      exists (h[x0]). 
      assert ([(m+1),(h[x0])] ∈ f).
      { destruct H8 as [H8[]]. apply H17; auto. }
      repeat split; auto.
      intros x1 []. apply NNPP; intro.
      set(f' := f ~ [[(m+1),x1]]).
      assert (Ind f').
      { repeat split; unfold Included; intros.
        - apply MKT4' in H20 as []. destruct H8. auto.
        - apply MKT4'; split; auto.
          apply AxiomII. split; eauto. 
          intro. apply MKT41 in H20; eauto.
          apply MKT55 in H20 as []; auto.
          elim (H4 m); auto.
        - apply MKT4' in H22 as []. destruct H8 as [H8[]].
          pose proof H22. apply H25 in H22; auto.
          apply MKT4'; split; auto.
          apply AxiomII; split; eauto.
          intro. apply MKT41 in H27; eauto.
          assert (Ensemble ([(n+1),(h[x2])])); eauto.
          apply MKT49b in H28 as [].
          apply MKT55 in H27 as []; auto.
          apply FAA4 in H27; auto. rewrite H27 in H26.
          assert (x0 = x2). { apply H12; auto. }
          elim H19. rewrite H31; auto. }
      apply H6 in H20. apply H20 in H18.
      apply MKT4' in H18 as []. apply AxiomII in H21 as []. 
      elim H22. apply MKT41; eauto. }
(*f是函数*)
  assert (Function f).
  { split; unfold Relation; intros.
    apply AxiomII in H10 as [_[x1[y1[]]]]. exists x1,y1. auto.
    assert (x0 ∈ N /\ y ∈ R /\ z ∈ R).
    { apply AxiomII' in H10 as [_[]].
      apply AxiomII' in H10 as [_[]]. 
      apply AxiomII' in H11 as [_[]].
      apply AxiomII' in H11 as [_[]]. auto. }
    pose proof H12. destruct H13. apply H9 in H13 as [x1[_]].
    assert (x1 = y /\ x1 = z). { split; apply H13; tauto. }
    destruct H15. rewrite <-H15,<-H16; auto. }
  assert (∀ m, m ∈ N -> ∃ y, [m,y] ∈ f).
  { apply Mathematical_Induction; eauto. intros m H12 [].
    destruct H8 as [H8[]]. apply H14 in H11; eauto.
    apply H8 in H11. apply AxiomII' in H11. tauto. }
  assert (dom(f) = N).
  { apply AxiomI; split; intros.
    - apply AxiomII in H12 as [_[]].
      apply AxiomII' in H12 as [_[]].
      apply AxiomII' in H12; tauto.
    - apply AxiomII. split; eauto. }
  assert (ran(f) ⊂ R).
  { unfold Included; intros. apply AxiomII in H13 as [_[]].
    apply AxiomII' in H13 as [_[]].
    apply AxiomII' in H13; tauto. }
  assert (∀ n, n ∈ N -> f[n + 1] = h[f[n]]).
  { intros. destruct H8 as [H8[]].
    pose proof H14. rewrite <-H12 in H14.
    apply Property_Value in H14; auto.
    pose proof H14. apply Property_ran in H14.
    apply (H16 n) in H18; auto.
    pose proof H18. 
    apply Property_dom,Property_Value in H19; auto. 
    destruct H10. eapply H20; eauto. }
  assert (f[1] = x).
  { pose proof H7.
    apply Property_dom,Property_Value in H15; auto.
    destruct H10. apply (H16 1); auto. }
  exists f. split; auto.
  intros f1. intros. destruct H16,H17,H18,H19.
  apply MKT71; auto. 
  intros. destruct (classic (x0 ∈ N)).
  - generalize dependent x0. apply Mathematical_Induction.
    rewrite H15,H19; auto.
    intros. pose proof H21.
    apply H20 in H21. apply H14 in H23. 
    rewrite H21,H23,H22; auto.
  - pose proof H21. rewrite <-H12 in H21. 
    rewrite <-H17 in H22. 
    apply MKT69a in H21. apply MKT69a in H22. 
    rewrite H21,H22; auto.
Qed. 


(*应用递归定理去规定指数*)
Theorem construction_Exponent : ∀ m, m ∈ R
  -> (exists ! f, Function f /\ dom(f) = N /\ ran(f) ⊂ R
  /\ f[1] = m /\ (∀ n, n ∈ N -> f[n+1] = f[n]·m)).
Proof.
(*定义h[n] = m·n m为R n为N*)
 intros. assert (Function (\{\ λ u v, u ∈ R /\ v = u · m \}\)).
  { split; intros. unfold Relation. intros.
    apply AxiomII in H0 as [H0[u[v[H1[]]]]]; eauto. 
    apply AxiomII' in H0 as [H0[]].
    apply AxiomII' in H1 as [H1[]]. rewrite H3,H5; auto. }
(*应用递归定理*)
  apply (Recursion _ m) in H0 as [f[[H0[H1[H2[]]]]]]; auto.
  - exists f. split; auto. split; auto. repeat split; auto.
    + intros. pose proof H6 as H6'. apply H4 in H6.
      rewrite H6. apply AxiomI; split; intros.
      * apply AxiomII in H7 as []. apply H8.
        assert (Ensemble ((f[n])·m)).
        { assert (((f[n])· m) ∈ R). 
          { assert (f[n] ∈ R).
            { apply H2. apply (@ Property_ran n).
              apply Property_Value. auto.
              rewrite H1; auto. } 
            pose proof (Mult_close f[n] m H9 H); auto. } 
           eauto. }
        apply AxiomII; split; auto. apply AxiomII'.
        assert (f[n] ∈ R).
        { apply H2. apply (@ Property_ran n). 
          apply Property_Value; auto.
          rewrite H1; auto. } 
        split; auto. apply MKT49a; eauto.
      * apply AxiomII; split; eauto.
        intros. apply AxiomII in H8 as [].
        apply AxiomII' in H9. destruct H9 as [H10[]].
        rewrite H11; auto.
    + intros g [H6[H7[H8[]]]]. apply H5. split; auto.
      repeat split; auto.
      intros. pose proof H11 as H11'.
      apply H10 in H11. rewrite H11.
      apply AxiomI; split; intros.
      * apply AxiomII; split; eauto.
        intros. apply AxiomII in H13 as []. 
        apply AxiomII' in H14 as [H14[]]. 
        rewrite H16; auto.
      * apply AxiomII in H12 as []. apply H13. apply AxiomII.
        assert (Ensemble (g[n]· m)).
        { assert ((g[n]·m) ∈ R).
          { assert (g[n] ∈ R).
            { apply H8. apply (@ Property_ran n).
              apply Property_Value; auto. rewrite H7; auto. } 
            pose proof (Mult_close g[n] m H14 H); auto. } 
           eauto. }
        split; auto. apply AxiomII'.
        assert (g[n] ∈ R).
        { rewrite <-H7 in H11'. 
          apply Property_Value in H11'; auto.
          apply Property_ran in H11'. apply H8 in H11'; auto. }
        split; auto. apply MKT49a; eauto.
  - apply AxiomI; split; intros.
    apply AxiomII in H1 as [H1[y]].
    apply AxiomII' in H2 as [H2[]]; auto.
    apply AxiomII; split; eauto.
    exists (z·m). apply AxiomII'. split; auto.
    apply MKT49a; eauto.
    assert ((z·m) ∈ R). { apply Mult_close; auto. } eauto.
  - unfold Included; intros. apply AxiomII in H1 as [H1[]].
    apply AxiomII' in H2 as [H2[]]. rewrite H4.
    apply Mult_close; auto.
Qed. 

(*以下推论为指数函数具有唯一性的集合论语言表达*)
Corollary ExpFunction_uni: ∀ m, m ∈ R
  -> exists f, Ensemble f /\ \{ λ f,Function f /\ dom(f) = N 
  /\ ran(f) ⊂ R /\ f[1] = m /\ 
  (∀ n, n ∈ N -> f[n+1] = f[n]·m) \} = [f].
Proof.
  intros. pose proof H as H'. 
  apply construction_Exponent in H as [f[]].
  exists f. split. destruct H as [H1[H2[H3[]]]].
  apply MKT75; auto. rewrite H2. pose proof Ensemble_R.
  pose proof N_Subset_R. apply MKT33 with R; auto.
  apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H2[H3[H4[H5[]]]]].
    apply MKT41; auto. apply MKT75. destruct H; auto.
    destruct H as [H7[]]. rewrite H. pose proof Ensemble_R.
    pose proof N_Subset_R. apply MKT33 with R; auto. 
    symmetry. apply H0; split; auto.
  - apply AxiomII; split; auto. apply MKT41 in H1.
    rewrite H1. apply MKT75. destruct H; auto.
    destruct H as [H2[]]. rewrite H.
    pose proof Ensemble_R. pose proof N_Subset_R. 
    apply MKT33 with R; auto.
    destruct H as [H3[]]. apply MKT75; auto.
    rewrite H. pose proof Ensemble_R. pose proof N_Subset_R. 
    apply MKT33 with R; auto. apply MKT41 in H1. 
    rewrite H1; auto. destruct H as [H3[]]. 
    apply MKT75; auto. rewrite H. pose proof Ensemble_R. 
    pose proof N_Subset_R. apply MKT33 with R; auto.
Qed.
    

Definition ExpFunction a := ∩\{ λ h, Function h /\ 
  dom(h) = N /\ ran(h) ⊂ R /\ h[1] = a /\ 
  ∀ n, n ∈ N -> h[n+1] = h[n]·a \}.

Definition Exp a b := (ExpFunction a)[b].

Notation "x ^ y" :=(Exp x y): R_scope.

Corollary Exp_close : ∀ x y, x ∈ R -> y ∈ N -> (x ^ y) ∈ R.
Proof.
  intros. unfold Exp. pose proof H as H'.
  apply ExpFunction_uni in H as [f[]].
  assert (f ∈ [f]). { apply MKT41; auto. }
  assert ((ExpFunction x) = f).
  { unfold ExpFunction. rewrite H1. apply MKT44; auto. }
  rewrite H3. rewrite <- H1 in H2.
  apply AxiomII in H2 as [H2[H5[H6[H7[]]]]].
  assert (f[y] ∈ ran(f)).
  { apply (@Property_ran y),Property_Value; auto.
    rewrite H6; auto. }
  apply H7; auto.
Qed.


Theorem P_Ex1: ∀ x, x ∈ R -> Function (ExpFunction x).
Proof.
  intros. apply ExpFunction_uni in H as [f[]].
  assert (f ∈ [f]). { apply MKT41; auto. }
  assert ((ExpFunction x) = f).
  { unfold ExpFunction. rewrite H0. apply MKT44; auto. }
  rewrite H2. rewrite <- H0 in H1. apply AxiomII in H1.
  destruct H1 as [H3[]]; auto.
Qed.


Theorem P_Ex2: ∀ x, x ∈ R -> x ^ 1 = x.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H0 as [].
    apply H1. apply AxiomII; split; eauto.
    apply AxiomII; split. pose proof one_in_R.
    apply AxiomII in H2 as [H3[]]. apply MKT49a; eauto.
    intros. apply AxiomII in H2 as [H3[H4[H5[H6[]]]]].
    rewrite <- H2. apply Property_Value; auto. rewrite H5. 
    apply one_in_N.
  - apply AxiomII; split; eauto. intros.
    assert (x ∈ \{ λ y, [1, y] ∈ ExpFunction x \}).
    { apply AxiomII; split; eauto. apply AxiomII; split.
      pose proof one_in_R. apply MKT4' in H2 as [].
      apply MKT49a; eauto. intros.
      apply AxiomII in H2 as [H3[H4[H5[H6[]]]]].
      rewrite <- H2. apply Property_Value; auto. rewrite H5. 
      apply one_in_N. }
    assert (y = x).
    { apply AxiomII in H1,H2. destruct H1,H2.
      apply Property_Fun in H3,H4. rewrite H3; auto. 
      apply P_Ex1; auto. apply P_Ex1; auto. }
    rewrite H3; auto.
Qed.


Lemma one_is_min_in_N : Min N 1.
Proof.
  repeat split. apply N_Subset_R. apply one_in_N.
  intros. set (E := \{ λ u, u ∈ N /\ 1 ≤ u \}).
  assert (1 ∈ E).
  { apply AxiomII; repeat split; eauto with real.
    apply Leq_P1; auto with real. }
  assert (E = N).
  { apply MathInd; unfold Included; intros; auto.
    apply AxiomII in H1; tauto. apply AxiomII in H1 as [H1[]].
    apply AxiomII; repeat split; eauto with real.
    pose proof one_in_N. pose proof (Nat_P1 x0 1 H2 H4); tauto.
    apply (OrderPM_Co3 1 x0 0 1) in H3; auto with real.
    rewrite Plus_P1 in H3; auto with real.
    destruct OrderPM_Co9; auto. }
  rewrite <-H1 in H. apply AxiomII in H; tauto.
Qed.


Corollary P_Ex3: ∀ x, x ∈ N -> 0 < x.
Proof.
  intros. pose proof one_is_min_in_N.
  unfold Min in H0. destruct H0,H1.
  pose proof H as H'. apply H2 in H. pose proof OrderPM_Co9.
  pose proof zero_in_R. pose proof one_in_R. 
  apply MKT4' in H5 as []. apply N_Subset_R in H'.
  apply (Order_Co2 0 1 x H4 H5 H'). left; tauto.
Qed.


Corollary P_Ex4: ∀ x n, x ∈ (R ~ [0]) -> n ∈ N 
  -> x ^ (n + 1) = (x ^ n) · x. 
Proof.
  intros. pose proof H as H'.
  apply MKT4' in H' as []. pose proof one_in_R_Co.
  assert (∀ n, n ∈ N -> x ^ (n + 1) = (x ^ n) · x).
  { apply Mathematical_Induction.
    - apply AxiomI; split; intros. 
      + apply AxiomII in H4 as []. apply H5.
        apply AxiomII; split. pose proof (P_Ex2 x H1). 
        rewrite H6. pose proof (Mult_close x x H1 H1); eauto.
        apply AxiomII; split. apply MKT49a.
        pose proof (Plus_close 1 1 H3 H3); eauto.
        rewrite P_Ex2; eauto.
        pose proof (Mult_close x x H1 H1); eauto.
        intros. apply AxiomII in H6 as [H7[H8[H9[H10[]]]]].
        pose proof one_in_N. apply H11 in H12.
        rewrite P_Ex2; auto. rewrite H6 in H12.
        rewrite <-H12. apply Property_Value; auto.
        rewrite H9. pose proof one_in_N. apply Nat_P1; auto.
      + apply AxiomII; split; eauto.
        intros. apply AxiomII in H5 as [].
        assert ([1 + 1, x ^ 1 · x] ∈ ExpFunction x).
        { apply AxiomII; split. apply MKT49a.
          pose proof (Plus_close 1 1 H3 H3); eauto.
          rewrite P_Ex2; eauto.
          pose proof (Mult_close x x H1 H1); eauto.
          intros. apply AxiomII in H7 as [H8[H9[H10[H11[]]]]].
          pose proof one_in_N. apply H12 in H13.
          rewrite P_Ex2; eauto. rewrite H7 in H13.
          rewrite <-H13. apply Property_Value; auto.
          rewrite H10. pose proof one_in_N. 
          pose proof (Nat_P1 1 1 H14 H14); tauto. }
        assert (y = x ^ 1 · x).
        { pose proof H1 as H1'. apply P_Ex1 in H1'.
          unfold Function in H1'. destruct H1'.
          apply H9 with (1+1); auto. }
        rewrite H8; auto.
    - intros. pose proof one_in_N. 
      pose proof (Nat_P1 k 1 H4 H6).
      destruct H7. pose proof (Exp_close x (k+1) H1 H7).
      pose proof (Mult_close (x^(k+1)) x H9 H1).
      apply AxiomI; split; intros.
      + apply AxiomII in H11 as []. apply H12.
        apply AxiomII; split; eauto.
        apply AxiomII; split. apply MKT49a; eauto.
        pose proof (Nat_P1 (k+1) 1 H7 H6).
        destruct H13; eauto. intros.
        assert ((ExpFunction x) = y).
        { pose proof H1.
          apply ExpFunction_uni in H14 as [f[]].
          rewrite H15 in H13. unfold ExpFunction.
          rewrite H15. apply MKT41 in H13; auto.
          rewrite H13. apply MKT44; auto. }
        rewrite <-H14.
        assert (y[k + 1] = x ^(k + 1)).
        { rewrite <-H14. auto. }
        apply AxiomII in H13 as [H16[H17[H18[H19[]]]]].
        apply H20 in H7. rewrite H15 in H7.
        rewrite <-H7. rewrite H14. 
        apply Property_Value; auto. rewrite H18.
        pose proof (Nat_P1 k 1 H4 H6). destruct H21.
        pose proof (Nat_P1 (k + 1) 1 H21 H6).
        destruct H23; auto.
      + apply AxiomII; split; eauto.
        intros. apply AxiomII in H12 as [].
        assert ([k + 1 + 1, x ^ (k + 1) · x] 
          ∈ ExpFunction x).
        { apply AxiomII; split. apply MKT49a; eauto.
          pose proof (Nat_P1 (k+1) 1 H7 H6).
          destruct H14; eauto. intros.
        assert ((ExpFunction x) = y0).
        { pose proof H1.
          apply ExpFunction_uni in H15 as [f[]].
          rewrite H16 in H14. unfold ExpFunction.
          rewrite H16. apply MKT41 in H14; auto.
          rewrite H14. apply MKT44; auto. }
        rewrite <-H15.
        assert (y0[k + 1] = x ^(k + 1)).
        { rewrite <-H15. auto. } 
        apply AxiomII in H14 as [H17[H18[H19[H20[]]]]].
        apply H21 in H7. rewrite H16 in H7.
        rewrite <- H7. rewrite H15.
        apply Property_Value; auto. rewrite H19.
        pose proof (Nat_P1 k 1 H4 H6). destruct H22.
        pose proof (Nat_P1 (k + 1) 1 H22 H6).
        destruct H24; auto. }
      assert (y = x ^ (k + 1) · x).
      { apply P_Ex1 in H1. unfold Function in H1.
        destruct H1. apply H15 with (k + 1 + 1); auto. }
      rewrite H15; auto. }
  apply H4 in H0; auto.
Qed.


Corollary Exp_ran0: ∀ n x, n ∈ N -> x ∈ (R ~ [0]) -> x ^ n ≠ 0.
Proof.
  intros. assert (∀ n, n ∈ N -> x ^ n ≠ 0).  
  { apply Mathematical_Induction.
    - intro. pose proof H0 as H0'. apply MKT4' in H0 as [].
      pose proof (P_Ex2 x H0). rewrite H1 in H3.
      rewrite <-H3 in H2. apply AxiomII in H2 as [].
      elim H4. apply MKT41. pose proof zero_in_R; eauto.
      auto.
    - intros. pose proof H0 as H0'.
      apply MKT4' in H0' as []. pose proof one_in_R. 
      apply MKT4' in H5 as []. pose proof (Exp_close x k H3 H1).
      pose proof (Mult_close (x^k) x H7 H3).
      pose proof one_in_N. pose proof (Nat_P1 k 1 H1 H9).
      destruct H10.
      pose proof (P_Ex4 x k H0 H1). rewrite H12.
      intro. pose proof (Exp_close x k H3 H1).
      apply PlusMult_Co2 in H13; eauto. destruct H13.
      contradiction. rewrite H13 in H4.
      apply AxiomII in H4 as []. elim H15.
      apply MKT41. pose proof zero_in_R; eauto. auto. }
  apply H1 in H. auto.
Qed.


Corollary Exp_ran1: ∀ x z, x ∈ (R ~ [0]) 
  -> z ∈ \{ λ u, (-u) ∈ N \} -> x ^ (-z) ∈ (R ~ [0]).
Proof.
  intros. apply AxiomII in H0 as []. 
  pose proof H as H'. apply MKT4' in H as [].
  assert (x ^ (-z) ∈ R).
  { apply (Exp_close x (-z)) in H; auto. }
  apply MKT4'; split; auto.
  apply AxiomII; split; eauto.
  intro. pose proof zero_in_R. apply MKT41 in H4; eauto.
  pose proof H2. pose proof (Exp_ran0 (-z) x  H1 H').
  destruct H7; auto.
Qed.


Corollary Exp_mult1 : ∀ x a, x ∈ (R ~ [0]) -> a ∈ N
  -> x ^ (a + 1) = x ^ a · x.
Proof.
  intros. pose proof H as H'. apply MKT4' in H' as [].
  pose proof one_in_N. pose proof (Nat_P1 a 1 H0 H3).
  destruct H4. 
  assert (∀ a, a ∈ N -> x ^ (a + 1) = (x ^ a) · x).
  { apply Mathematical_Induction.
    - apply AxiomI; split; intros. 
      + apply AxiomII in H6 as []. apply H7.
        apply AxiomII; split. pose proof (P_Ex2 x H1). 
        rewrite H8. pose proof (Mult_close x x H1 H1); eauto.
        apply AxiomII; split. apply MKT49a.
        pose proof (Nat_P1 1 1 H3 H3). destruct H8. eauto.
        rewrite P_Ex2; eauto.
        pose proof (Mult_close x x H1 H1); eauto.
        intros. apply AxiomII in H8 as [H8[H9[H10[H11[]]]]].
        pose proof H3. apply H13 in H14.
        rewrite P_Ex2; auto. rewrite H12 in H14.
        rewrite <-H14. apply Property_Value; auto.
        rewrite H10. apply Nat_P1; auto.
      + apply AxiomII; split; eauto.
        intros. apply AxiomII in H7. destruct H7.
        assert ([1 + 1, x ^ 1 · x] ∈ ExpFunction x).
        { apply AxiomII; split. apply MKT49a.
          pose proof (Nat_P1 1 1 H3 H3). destruct H9. eauto.
          rewrite P_Ex2; eauto.
          pose proof (Mult_close x x H1 H1); eauto.
          intros. apply AxiomII in H9 as [H9[H10[H11[H12[]]]]].
          pose proof H3. apply H14 in H15. rewrite P_Ex2; eauto.
          rewrite H13 in H15. rewrite <-H15. 
          apply Property_Value; auto. rewrite H11.
          pose proof (Nat_P1 1 1 H3 H3); tauto. }
        assert (y = x ^ 1 · x).
        { apply P_Ex1 in H1. unfold Function in H1.
          destruct H1. apply H10 with (1+1); auto. }
        rewrite H10; auto.
     - intros. pose proof (Nat_P1 k 1 H6 H3).
        destruct H8. pose proof (Exp_close x (k+1) H1 H8).
        pose proof (Mult_close (x^(k+1)) x H10 H1).
        apply AxiomI; split; intros.
        + apply AxiomII in H12 as []. apply H13.
          apply AxiomII; split; eauto.
          apply AxiomII; split. apply MKT49a; eauto.
          pose proof (Nat_P1 (k+1) 1 H8 H3).
          destruct H14; eauto. intros.
          assert ((ExpFunction x) = y).
          { apply ExpFunction_uni in H1 as [f[]].
            rewrite H15 in H14. unfold ExpFunction.
            rewrite H15. apply MKT41 in H14; auto.
            rewrite H14. apply MKT44; auto. }
          rewrite <-H15.
          assert (y[k + 1] = x ^(k + 1)).
          { rewrite <-H15. auto. }
          apply AxiomII in H14 as [H17[H18[H19[H20[]]]]].
          pose proof H8 as H8'. apply H21 in H8.
          rewrite H16 in H8. rewrite <-H8. rewrite H15. 
          apply Property_Value; auto. rewrite H19.
          pose proof (Nat_P1 (k+1) 1 H8' H3).
          destruct H22; auto.
        + apply AxiomII; split; eauto.
          intros. apply AxiomII in H13 as [].
          assert ([k + 1 + 1, x ^ (k + 1) · x] 
            ∈ ExpFunction x).
          { apply AxiomII; split. apply MKT49a; eauto.
            pose proof (Nat_P1 (k+1) 1 H8 H3).
            destruct H15; eauto. intros.
          assert ((ExpFunction x) = y0).
          { apply ExpFunction_uni in H1 as [f[]].
            rewrite H16 in H15. unfold ExpFunction.
            rewrite H16. apply MKT41 in H15; auto.
            rewrite H15. apply MKT44; auto. }
          rewrite <-H16.
          assert (y0[k + 1] = x ^(k + 1)).
          { rewrite <-H16. auto. } 
          apply AxiomII in H15 as [H18[H19[H20[H21[]]]]].
          apply H22 in H8. rewrite H17 in H8.
          rewrite <- H8. rewrite H16.
          apply Property_Value; auto. rewrite H20.
          pose proof (Nat_P1 k 1 H6 H3). destruct H23.
          pose proof (Nat_P1 (k+1) 1 H23 H3).
          destruct H25; auto. }
        assert (y = x ^ (k + 1) · x).
        { apply P_Ex1 in H1. unfold Function in H1.
          destruct H1. apply H16 with (k+1+1); auto. }
        rewrite H16; auto. }
    apply H6 in H0; auto.
Qed.


Corollary Exp_mult2 : ∀ x a b, x ∈ (R ~ [0]) -> a ∈ N 
  -> b ∈ N -> x ^ a · x ^ b = x ^ (a + b).
Proof.
  intros. pose proof H. apply MKT4' in H as [].
  pose proof one_in_N.
  assert (∀ a, a ∈ N -> x ^ a · x ^ b = x ^ (a + b)).
  { apply Mathematical_Induction.
    - pose proof (P_Ex2 x H). rewrite H5.
      pose proof (Exp_close x b H H1).
      pose proof one_in_R_Co. pose proof H1 as H1'.
      apply N_Subset_R in H1'. rewrite (Plus_P4 1 b); auto.
      pose proof (Exp_close x b H H1).
      rewrite Mult_P4; auto.
      pose proof (Nat_P1 b 1 H1 H4). destruct H9.
      rewrite P_Ex4; auto.
    - intros. pose proof (P_Ex4 x k H2 H5).
      pose proof (Nat_P1 k 1 H5 H4). destruct H8.
      pose proof one_in_R_Co.
      pose proof H1 as H1'. apply N_Subset_R in H1'.
      pose proof (Plus_P4 b 1 H1' H10). 
      pose proof H5 as H5'. apply N_Subset_R in H5'.
      rewrite <-Plus_P3; auto. rewrite <-H11.
      rewrite Plus_P3; auto. pose proof (Nat_P1 k b H5 H1).
      destruct H12. pose proof (P_Ex4 x (k + b) H2 H12).
      pose proof (Nat_P1 (k + b) 1 H12 H4).
      destruct H15. pose proof (Exp_close x k H H5). 
      rewrite H14,<-H6,H7.
      pose proof (Exp_close x b H H1).
      pose proof (Mult_P4 (x ^ k) (x ^ b) H17 H18).
      rewrite Mult_P4,Mult_P3,H19; auto.
      pose proof (Mult_close (x ^ k) x H17 H). auto. } 
   apply H5 in H0. auto.
Qed.


Definition ExpFunction_Zt u := (\{\ λ z v, z ∈ Z /\
    ((z ∈ N /\ v = u ^ z) \/ (z ∈ \{ λ u, (-u) ∈ N \} 
    /\ v = (u ^ (-z))⁻) \/ (z = 0 /\ v = 1)) \}\).


Notation "x \^ y" := ((ExpFunction_Zt x)[y])(at level 10): R_scope.


Corollary ExpZ_equ: ∀ x z, x ∈ (R ~ [0]) -> z ∈ N 
  -> x \^ z = x ^ z.
Proof.
  intros. pose proof H. apply MKT4' in H1 as [].
  pose proof (Exp_close x z H1 H0).
  apply AxiomI; split; intros.
  - apply AxiomII in H4 as []. apply H5.
    apply AxiomII; repeat split; eauto.
    apply AxiomII'; split; eauto. apply MKT49a; eauto.
    repeat split. apply Z_Corollary in H0; auto.
    left; auto.
  - apply AxiomII; repeat split; eauto. intros.
    apply AxiomII in H5 as []. apply AxiomII' in H6 as [H7[]].
    destruct H8,H8. rewrite H9; auto.
    destruct H8. apply AxiomII in H8 as [].
    pose proof (Nat_P1 z (-z) H0 H10). destruct H11.
    apply N_Subset_R in H0. pose proof (Minus_P1 z H0).
    rewrite H13 in H11. pose proof zero_not_in_N.
    destruct H14; auto. destruct H8. rewrite H8 in H0.
    pose proof zero_not_in_N. destruct H10; auto.
Qed.


Theorem Zt_Ex1: ∀ x, x ∈ R -> Function (ExpFunction_Zt x).
Proof.
  intros. pose proof H. unfold Function. split. 
  - unfold Relation. intros. 
    apply AxiomII in H1 as [H1[x0[y0[]]]].
    exists x0,y0; auto.
  - intros.
    apply AxiomII in H1 as [H1[x1[y1[H4[H5[]]]]]].
    apply AxiomII in H2 as [H2[x2[y2[H7[H8[]]]]]].
    + apply MKT49b in H1 as []. 
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4,H3.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H7; auto. destruct H7,H6.
      rewrite H14,<-H7 in H13. rewrite H11,<-H4 in H10.
      rewrite H10,H13; auto.
    + destruct H6,H6. apply MKT49b in H1 as [].
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4,H3.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H7; auto. destruct H7.
      apply AxiomII in H6 as []. rewrite <- H4 in H3.
      rewrite <- H7 in H15. pose proof (Nat_P1 x0 (-x0) H3 H15).
      destruct H16. pose proof H3. apply N_Subset_R in H18.
      pose proof (Minus_P1 x0 H18). rewrite H19 in H16.
      pose proof zero_not_in_N. destruct H20; auto.
      apply MKT49b in H1 as [].
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4,H3.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H7; auto. destruct H7.
      rewrite H6 in H7. 
      assert (x1 = 0). { rewrite <- H4; auto. }
      rewrite H15 in H3. pose proof zero_not_in_N. 
      destruct H16; auto.
    + destruct H3,H3. apply AxiomII in H2 as [H2[x2[y2[H8[]]]]].
      destruct H9,H9. apply AxiomII in H3 as [].
      apply MKT49b in H1 as [].
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H8; auto. destruct H8.
      rewrite H4 in H8. rewrite <-H8 in H9. 
      pose proof (Nat_P1 x1 (-x1) H9 H11). destruct H16.
      pose proof H9. apply N_Subset_R in H9.
      pose proof (Minus_P1 x1 H9). rewrite H19 in H16.
      pose proof zero_not_in_N. destruct H20; auto.
      destruct H9. apply MKT49b in H1 as [].
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H8; auto. destruct H8.
      assert (x1 = x2). { rewrite <-H4. rewrite <-H8. auto. }
      rewrite <-H15 in H10. rewrite <-H10 in H6. 
      rewrite <-H12 in H6. rewrite <-H14 in H6. auto.
      destruct H9. apply AxiomII in H3 as [].
      apply MKT49b in H1 as [].
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4,H3.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H8; auto. destruct H8.
      rewrite H9 in H8. rewrite H8 in H4. rewrite <- H4 in H11.
      pose proof zero_not_in_N. destruct H16; auto.
      assert (-0 = 0). 
      { apply AxiomI; split; intros.
        apply AxiomII in H16 as []. apply H17.
        pose proof zero_in_R. apply AxiomII; repeat split; eauto.
        apply Plus_P1; auto. apply AxiomII; split; eauto.
        intros. apply AxiomII in H17 as [H18[]].
        pose proof zero_in_R. rewrite Plus_P4 in H19; auto.
        apply Plus_Co3 in H19; eauto. pose proof (Minus_P1 0 H20).
        rewrite H21 in H19. rewrite H19. auto. }
      rewrite H16 in H11. pose proof zero_not_in_N.
      destruct H17; auto.
      apply AxiomII in H2 as [H2[x2[y2[H8[]]]]].
      destruct H9,H9. apply MKT49b in H1 as []. 
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H8; auto. destruct H8.
      rewrite H3 in H4. rewrite H4 in H8. rewrite <-H8 in H9.
      pose proof zero_not_in_N. destruct H15; auto.
      destruct H9. apply AxiomII in H9 as []. 
      apply MKT49b in H1 as []. 
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H8; auto. destruct H8.
      rewrite H3 in H4. rewrite H4 in H8. rewrite <-H8 in H11.
      assert (-0 = 0). 
      { apply AxiomI; split; intros.
        apply AxiomII in H16 as []. apply H17.
        pose proof zero_in_R. apply AxiomII; repeat split; eauto.
        apply Plus_P1; auto. apply AxiomII; split; eauto.
        intros. apply AxiomII in H17 as [H18[]].
        pose proof zero_in_R. rewrite Plus_P4 in H19; auto.
        apply Plus_Co3 in H19; eauto. pose proof (Minus_P1 0 H20).
        rewrite H21 in H19. rewrite H19. auto. }
      rewrite H16 in H11. pose proof zero_not_in_N. 
      destruct H17; auto.
      apply MKT49b in H1 as []. 
      apply (MKT55 x0 y x1 y1) in H4; auto. destruct H4.
      apply MKT49b in H2 as [].
      apply (MKT55 x0 z x2 y2) in H8; auto. destruct H8,H9.
      rewrite H6 in H11. rewrite H14 in H13.
      rewrite H11,H13. auto.
Qed.


Theorem Zt_Ex2: ∀ x, x ∈ (R ~ [0]) 
  -> dom(ExpFunction_Zt x) = Z.
Proof. 
  intros. pose proof H as H'. apply AxiomI; split; intros. 
  - apply AxiomII in H0 as [H1[]]. 
    apply AxiomII' in H0 as [H0[]]; tauto.
  - apply AxiomII in H0 as [H1[]].
    + apply AxiomII; split; eauto. (*对z∈N进行讨论*)
      exists (x ^ z). apply AxiomII'; split. 
      apply MKT4' in H as [].
      assert (Ensemble (x ^ z)).
      { apply (Exp_close x z) in H; auto; eauto. }
      apply MKT49a; auto.
      repeat split; auto. apply Z_Corollary; auto.
    + apply AxiomII in H0 as [H2[]]. 
      * apply AxiomII; split; eauto. (*对-z∈N进行讨论*)
        exists ((x ^ (-z))⁻). apply AxiomII'; split.
        assert (Ensemble ((x ^ (-z))⁻) ).
        { pose proof H0.  pose proof H.
          apply AxiomII in H0 as []. apply MKT4' in H as [].
          apply (Exp_close x (-z)) in H; auto.
          unfold Ensemble. exists R.
          pose proof (Exp_ran1 x z H4 H3).
          apply Mult_inv1 in H7. 
          apply MKT4' in H7 as []. auto. }
        apply MKT49a; auto. split; auto.
        apply AxiomII; split; auto. right.
        apply AxiomII; split; auto.
      * apply AxiomII; split; auto. exists 1. (*对z=0讨论*)
        pose proof zero_in_R. assert (Ensemble 0); eauto.
        apply MKT41 in H0; auto. rewrite H0.
        apply AxiomII'; repeat split; auto.
        pose proof one_in_R. apply MKT4' in H5 as [].
        apply MKT49a; eauto. apply AxiomII; split; auto.
        right. apply AxiomII;split; auto.
Qed.


Theorem Z_Ex3: ∀ x, x ∈ (R ~ [0]) 
  -> ran(ExpFunction_Zt x) ⊂ (R ~ [0]).
Proof. 
  intros. unfold Included. intros. 
  pose proof H as H'. apply MKT4' in H' as [].
  apply AxiomII in H0 as []. destruct H3.
  apply AxiomII' in H3 as [H3[H4[]]]. destruct H5.
  - apply MKT4'; split. 
    apply (Exp_close x x0) in H1; auto. rewrite H6; auto.
    apply AxiomII; split; auto. 
    intro. pose proof zero_in_R.
    apply MKT41 in H7; eauto.
    rewrite H7 in H6. symmetry in H6.
    pose proof (Exp_ran0 x0 x H5 H). contradiction.  (*对z∈N讨论*)
  - destruct H5,H5. 
    assert (((x ^ (-x0))⁻) ∈ (R ~ [0])).
    { pose proof (Exp_ran1 x x0 H H5).  
      apply PlusMult_Co6 in H7. auto. }
    rewrite <-H6 in H7; auto. (*对-z∈N讨论*)
    rewrite H6. pose proof one_in_R; auto. (*对z=0讨论*)
Qed.


Corollary ExpZ_one: ∀ x, x ∈ (R ~ [0]) 
    -> (ExpFunction_Zt x)[0] = 1.
Proof. 
  intros. pose proof H as H'. 
  apply AxiomI; split; intros. apply AxiomII in H0 as [].
  apply H1. pose proof one_in_R. apply AxiomII in H2 as [H3[]].
  apply AxiomII; split; eauto. 
  pose proof zero_in_R. apply AxiomII'; repeat split; eauto.
  apply AxiomII; split; eauto. right. apply AxiomII; split; eauto.
  apply AxiomII; split; eauto. intros. 
  apply AxiomII in H1 as []. apply AxiomII' in H2 as [H3[H4[]]].
  destruct H2. pose proof zero_not_in_N. destruct H6; auto.
  destruct H2,H2. apply AxiomII in H2 as [].
  assert (-0 = 0). 
  { apply AxiomI; split; intros.
    apply AxiomII in H7 as []. apply H8.
    pose proof zero_in_R. apply AxiomII; repeat split; eauto.
    apply Plus_P1; auto. apply AxiomII; split; eauto.
    intros. apply AxiomII in H8 as [H9[]].
    pose proof zero_in_R. rewrite Plus_P4 in H10; auto.
    apply Plus_Co3 in H10; eauto. pose proof (Minus_P1 0 H11).
    rewrite H12 in H10. rewrite H10. auto. } 
  rewrite H7 in H6. pose proof zero_not_in_N. destruct H8; auto.
  rewrite H5; auto.
Qed.


Corollary ExpZ_ran1 : ∀ x y, x ∈ (R ~ [0]) 
  -> y ∈ Z -> (ExpFunction_Zt x)[y] ∈ (R ~ [0]).
Proof.
  intros. pose proof H as H'. apply MKT4' in H' as [].
  pose proof (Zt_Ex2 x H). pose proof (Z_Ex3 x H).
  pose proof (Zt_Ex1 x H1).
  apply H4,(@ Property_ran y),Property_Value; auto.
  rewrite H3. auto. 
Qed.


Theorem Z_Ex: ∀ x n, x ∈ (R ~ [0]) -> n ∈ \{ λ u, (-u) ∈ N \}
   -> (ExpFunction_Zt x)[n]  = ((ExpFunction_Zt x)[(-n)])⁻.
Proof. 
  intros. apply AxiomI; split; intros.
  - unfold ExpFunction_Zt in H1. apply AxiomII in H1 as [].
    apply H2.
    assert ((-n) ∈ Z).
    { apply AxiomII in H0 as [].
      apply AxiomII; split; eauto. }
    pose proof (ExpZ_ran1 x (-n) H H3).
    pose proof (Mult_inv1 (x \^ (- n)) H4). 
    apply AxiomII; split; eauto.
    apply AxiomII; split. apply MKT49a; eauto.
    exists n. exists ((x \^ (- n)) ⁻). repeat split.
    apply AxiomII; repeat split; eauto. right.
    apply MKT4. left; auto. right. left.
    split; auto. apply AxiomII in H0 as [].
    pose proof (ExpZ_equ x (-n) H H6).
    rewrite <-H7; auto.
  - unfold ExpFunction_Zt. apply AxiomII; split; eauto.
    intros. apply AxiomII in H2 as [].
    apply AxiomII in H3 as [H4[x0[y0[H5[H6[]]]]]].
    + destruct H3. apply MKT49b in H4 as [].
      apply MKT55 in H5 as []; auto. rewrite <-H5 in H3.
      apply AxiomII in H0 as [].
      pose proof (Nat_P1 n (-n) H3 H10). destruct H11.
      pose proof H3. apply N_Subset_R in H3.
      rewrite Minus_P1 in H11; auto.
      pose proof zero_not_in_N. contradiction.
    + destruct H3,H3.
      * apply MKT49b in H4 as []. 
        apply MKT55 in H5 as []; eauto.
        rewrite <-H5,<-H9 in H7. rewrite H7.
        assert (-n ∈ N). 
        { apply AxiomII in H0 as []; eauto. }
        pose proof (ExpZ_equ x (-n) H H10).
        rewrite <-H11; auto.
      * apply MKT49b in H4 as []. 
        apply MKT55 in H5 as []; auto. rewrite H3 in H5.
        rewrite H5 in H0. apply AxiomII in H0 as [].
        assert (0 = - 0).
        { symmetry. pose proof zero_in_R.
          apply N_Subset_R in H10.
          pose proof (Plus_neg2 0 H11).
          apply Plus_Co1; auto. intros.
          pose proof (Minus_P2 y1 H13). auto. }
        rewrite <-H11 in H10. pose proof zero_not_in_N.
        contradiction.        
Qed.


Corollary ExpZ_mult1 : ∀ x a, x ∈ (R ~ [0]) -> a ∈ Z
  -> (ExpFunction_Zt x)[a + 1] = ((ExpFunction_Zt x)[a]) · x.
Proof.
  intros. pose proof H as H'. apply MKT4' in H' as [].
  apply AxiomII in H0 as []. destruct H3.
  - pose proof (ExpZ_equ x a H H3).
    pose proof one_in_N. pose proof (Nat_P1 a 1 H3 H5).
    destruct H6. pose proof (ExpZ_equ x (a + 1) H H6).
    rewrite H4,H8.
    assert (∀ a, a ∈ N -> x ^ (a + 1) = (x ^ a) · x).
    { apply Mathematical_Induction.
      - apply AxiomI; split; intros. 
        + apply AxiomII in H9 as []. apply H10.
          apply AxiomII; split. pose proof (P_Ex2 x H1). 
          rewrite H11. pose proof (Mult_close x x H1 H1); eauto.
          apply AxiomII; split. apply MKT49a.
          pose proof (Nat_P1 1 1 H5 H5). destruct H11. eauto.
          rewrite P_Ex2; eauto.
          pose proof (Mult_close x x H1 H1); eauto.
          intros. apply AxiomII in H11 as [H12[H13[H14[H15[]]]]].
          pose proof H5. apply H16 in H17.
          rewrite P_Ex2; auto. rewrite H11 in H17.
          rewrite <-H17. apply Property_Value; auto.
          rewrite H14. apply Nat_P1; auto.
        + apply AxiomII; split; eauto.
          intros. apply AxiomII in H10. destruct H10.
          assert ([1 + 1, x ^ 1 · x] ∈ ExpFunction x).
          { apply AxiomII; split. apply MKT49a.
            pose proof (Nat_P1 1 1 H5 H5). destruct H12. eauto.
            rewrite P_Ex2; eauto.
            pose proof (Mult_close x x H1 H1); eauto.
            intros. apply AxiomII in H12 as [H13[H14[H15[H16[]]]]].
            pose proof H5. apply H17 in H18. rewrite P_Ex2; eauto.
            rewrite H12 in H18. rewrite <-H18. 
            apply Property_Value; auto. rewrite H15.
            pose proof (Nat_P1 1 1 H5 H5); tauto. }
          assert (y = x ^ 1 · x).
          { apply P_Ex1 in H1. unfold Function in H1.
            destruct H1. apply H13 with (1+1); auto. }
          rewrite H13; auto.
      - intros. pose proof (Nat_P1 k 1 H9 H5).
        destruct H11. pose proof (Exp_close x (k+1) H1 H11).
        pose proof (Mult_close (x^(k+1)) x H13 H1).
        apply AxiomI; split; intros.
        + apply AxiomII in H15 as []. apply H16.
          apply AxiomII; split; eauto.
          apply AxiomII; split. apply MKT49a; eauto.
          pose proof (Nat_P1 (k+1) 1 H11 H5).
          destruct H17; eauto. intros.
          assert ((ExpFunction x) = y).
          { apply ExpFunction_uni in H1 as [f[]].
            rewrite H18 in H17. unfold ExpFunction.
            rewrite H18. apply MKT41 in H17; auto.
            rewrite H17. apply MKT44; auto. }
          rewrite <-H18.
          assert (y[k + 1] = x ^(k + 1)).
          { rewrite <-H18. auto. }
          apply AxiomII in H17 as [H20[H21[H22[H23[]]]]].
          pose proof H11 as H11'. apply H24 in H11.
          rewrite H19 in H11. rewrite <-H11. rewrite H18. 
          apply Property_Value; auto. rewrite H22.
          pose proof (Nat_P1 (k+1) 1 H11' H5).
          destruct H25; auto.
        + apply AxiomII; split; eauto.
          intros. apply AxiomII in H16 as [].
          assert ([k + 1 + 1, x ^ (k + 1) · x] 
            ∈ ExpFunction x).
          { apply AxiomII; split. apply MKT49a; eauto.
            pose proof (Nat_P1 (k+1) 1 H11 H5).
            destruct H18; eauto. intros.
          assert ((ExpFunction x) = y0).
          { apply ExpFunction_uni in H1 as [f[]].
            rewrite H19 in H18. unfold ExpFunction.
            rewrite H19. apply MKT41 in H18; auto.
            rewrite H18. apply MKT44; auto. }
          rewrite <-H19.
          assert (y0[k + 1] = x ^(k + 1)).
          { rewrite <-H19. auto. } 
          apply AxiomII in H18 as [H21[H22[H23[H24[]]]]].
          apply H25 in H11. rewrite H20 in H11.
          rewrite <- H11. rewrite H19.
          apply Property_Value; auto. rewrite H23.
          pose proof (Nat_P1 k 1 H9 H5). destruct H26.
          pose proof (Nat_P1 (k+1) 1 H26 H5).
          destruct H28; auto. }
        assert (y = x ^ (k + 1) · x).
        { apply P_Ex1 in H1. unfold Function in H1.
          destruct H1. apply H19 with (k+1+1); auto. }
        rewrite H19; auto. }
    apply H9 in H3; auto. (*N*)
  - apply MKT4 in H3 as [].
    + pose proof (Z_Ex x a H H3).
      pose proof H3. apply AxiomII in H5 as [].
      pose proof H6. apply N_Subset_R in H6.
      apply P_Ex3 in H7. apply OrderPM_Co2 in H7; auto.
      assert (a ∈ Z).
      { apply AxiomII; split; auto. right.
        apply MKT4. left. auto. }
      pose proof H8 as H8'. apply Z_Corollary in H8.
      pose proof zero_in_R.
      assert (a < 0).
      { pose proof (Order_Co1 a 0 H8 H9).
        destruct H10; auto. destruct H10.
        apply AxiomII in H3 as []. apply P_Ex3 in H11.
        pose proof (OrderPM_Co1 0 (-a) a H9 H6 H8 H11).
        rewrite Plus_P4,Plus_P1 in H12; auto.
        pose proof (Plus_P4 a (-a) H8 H6).
        rewrite <-H13,Minus_P1 in H12; auto.
        rewrite H10 in H3. apply AxiomII in H3 as [].
        assert (0 = - 0).
        { symmetry. pose proof zero_in_R.
          apply N_Subset_R in H11.
          pose proof (Plus_neg2 0 H12).
          apply Plus_Co1; auto. intros.
          pose proof (Minus_P2 y H14). auto. }
        rewrite <-H12 in H11. pose proof zero_not_in_N.
        contradiction. }
      pose proof one_in_R_Co.
      pose proof (Plus_close a 1 H8 H11).
      pose proof (Order_Co1 (a + 1) 0 H12 H9).
      destruct H13.
      * assert (a + 1 ∈ (\{ λ u,- u ∈ N \})).
        { apply AxiomII; split; eauto. pose proof H13.
          pose proof OrderPM_Co9. pose proof one_in_R_Co.
          apply OrderPM_Co2 in H15; auto.
          apply Plus_neg1a in H16.
          assert ((- (1)) < 0 /\ a + 1 < 0). { tauto. }
          pose proof (OrderPM_Co5 (-(1)) (a + 1) H16 H12).
          destruct H18. right; auto.
          assert (0 < - (1) · (a + 1)). { unfold lt; auto. }
          assert ( - (1) · (a + 1) = - (a + 1)).
          { rewrite <-PlusMult_Co3; auto. }
          pose proof (Mult_P5 a 1 (-(1)) H8 H11 H16).
          rewrite Mult_P4 in H22; auto. rewrite <-H21,H22.
          rewrite Mult_P4; auto. rewrite <-PlusMult_Co3; auto.
          rewrite Mult_P4; auto. rewrite <-PlusMult_Co3; auto.
          apply Nat_P2. apply AxiomII in H3 as []; eauto.
          intro. assert ( -a = (-(1)) · a). 
          { apply PlusMult_Co3; auto. }
          rewrite H24 in H23.
          assert((-(1)) ∈ (R ~ [0])).
          { apply MKT4'; split; auto. 
            apply AxiomII; split; eauto.
            intro. apply MKT41 in H25; eauto.
            rewrite H25 in H15. unfold lt in H15.
            destruct H15. contradiction. }
          pose proof (PlusMult_Co5 1 H11).
          apply Mult_Co3 in H23; auto.
          rewrite Mult_P1 in H26; auto.
          apply Mult_Co3 in H26; auto.
          assert (a = (-(1))).
          { rewrite H26. rewrite H23. auto. }
          rewrite H27 in H13. rewrite Plus_P4 in H13; auto.
          rewrite Minus_P1 in H13; auto. unfold lt in H13.
          destruct H13. contradiction. }
        pose proof (Z_Ex x (a + 1) H H14).
        pose proof (ExpZ_ran1 x a H H8').
        pose proof H16 as H16'. apply MKT4' in H16 as [].
        pose proof (Mult_close (x \^ a) x  H16 H1).
        pose proof (Mult_P4 x (x \^ a) H1 H16).
        rewrite <-H19,H4,H15. pose proof H.
        apply Mult_inv1 in H20.
        assert (- a ∈ Z).
        { apply AxiomII; split; eauto. left.
          apply AxiomII in H3 as []; auto.  }
        pose proof (ExpZ_ran1 x (-a) H H21).
        pose proof (Frac_P1 x (x \^ (- a)) x⁻ H1 H22 H20).
        rewrite Mult_inv2 in H23; auto.
        rewrite H23. pose proof (Plus_neg1a 1 H11).
        rewrite PlusMult_Co3,Mult_P4; eauto.
        rewrite Mult_P5,Mult_P4; auto.
        pose proof (PlusMult_Co3 a H8). rewrite <-H25.
        rewrite Mult_P4,<-PlusMult_Co3; auto.
        apply MKT4' in H22 as []; auto.
        apply MKT4' in H20 as []; auto.
        pose proof (Mult_close (x \^ (- a)) (x⁻) H22 H20).
        assert (x \^ (- a) / x ∈ (R ~ [0])).
        { apply MKT4'; split. apply Mult_close; auto.
          apply AxiomII; split; eauto.
          intro. apply MKT41 in H29; eauto.
          apply PlusMult_Co2 in H29; auto.
          destruct H29. apply AxiomII in H26 as [].
          elim H30. apply MKT41; eauto.
          apply AxiomII in H27 as []. elim H30.
          apply MKT41; eauto. }
        assert ( 1 / (x \^ (- a) / x) = ((x \^ (- a) / x)⁻)· 1).
        { rewrite Mult_P4; auto.          
          pose proof (Mult_inv1 (x \^ (- a) / x ) H29).
          apply MKT4' in H30 as []; auto. }
        pose proof (Mult_inv1 (x \^ (- a) / x ) H29).
        apply MKT4' in H31 as [].
        rewrite H30,Mult_P1; eauto.
        assert (x \^ (- a - 1) = x \^ (- a) / x).
        { assert (∀ a, a ∈ N -> x \^ (a - 1) = x \^ (a) · x⁻).
          { apply Mathematical_Induction.           
            rewrite Minus_P1; auto. rewrite ExpZ_one; auto.
            pose proof one_in_N.
            pose proof (ExpZ_equ x 1 H H33). rewrite H34.
            rewrite P_Ex2; auto. rewrite Mult_inv2; auto.
            intros. pose proof H33 as H33'.
            apply N_Subset_R in H33'.
            pose proof (Order_Co1 k 1 H33' H11). destruct H35.
            pose proof H33. pose proof one_is_min_in_N.
            unfold Min in H37. destruct H37,H38.
            apply H39 in H36.
            pose proof (Order_Co2 k 1 k H33' H11 H33').
            destruct H40. left; tauto. contradiction.
            destruct H35. 
            pose proof (OrderPM_Co1 1 k (-(1)) H11 H33' H24).
            pose proof H35 as H35'. apply H36 in H35.
            rewrite Minus_P1 in H35; auto.
            pose proof (Plus_close k 1 H33' H11).
            assert (1 - 1 = (-(1)) + 1). 
            { rewrite Plus_P4; auto. }
            rewrite <-Plus_P3,Minus_P1,Plus_P1; auto.
            pose proof one_in_N.
            pose proof (Nat_P1 k 1 H33 H39). destruct H40.
            pose proof (ExpZ_equ x (k + 1) H H40).
            rewrite H42. pose proof (Exp_mult1 x k H H33).
            rewrite H43. pose proof (Exp_close x k H1 H33).
            rewrite <-Mult_P3; auto.
            pose proof (ExpZ_equ x k H H33). rewrite H45.
            rewrite Divide_P1,Mult_P1; auto.
            rewrite <-Plus_P3; auto. 
            rewrite Minus_P1,Plus_P1; auto.
            pose proof (Exp_mult1 x k H H33).
            pose proof one_in_N.
            pose proof (Nat_P1 k 1 H33 H37).
            destruct H38. 
            pose proof (ExpZ_equ x (k + 1) H H38).
            rewrite H40,H36,<-Mult_P3,Divide_P1,H35; auto.
            rewrite Mult_P1; auto.
            pose proof (ExpZ_equ x 1 H H37); auto.
            rewrite P_Ex2; auto. rewrite H35,P_Ex2; auto. }
          apply AxiomII in H3 as []. pose proof H34 as H34'.
          apply H33 in H34. auto. }
        rewrite H33; auto.        
        * destruct H13. pose proof one_in_R_Co.
          pose proof (Plus_neg1a 1 H14).
          pose proof (Order_Co1 a (-(1)) H8 H15).
          destruct H16.
          pose proof (OrderPM_Co1 a (-(1)) 1 H8 H15 H11 H16); auto.
          assert ( (-(1)) + 1 = 1 - 1).
          { apply Plus_P4; auto. }
          rewrite H18,Plus_neg2 in H17; auto.
          unfold lt in H17. destruct H17.
          assert ( 0 < a + 1 /\ a + 1 ≤ 0). { auto. }
          pose proof (Order_Co2 0 (a + 1) 0 H9 H12 H9).
          destruct H21. left. auto. contradiction.
          destruct H16. 
          assert (a ≤ (-(1))).
          { pose proof (Order_Co2 (-(1)) a 0 H15 H8 H9).
            destruct H17. left. split; auto. 
            unfold lt in H10. tauto.
            assert ((-(1)) < 0). { unfold lt; tauto. }
            pose proof H3 as H3'. apply AxiomII in H3' as [].
            pose proof one_is_min_in_N. unfold Min in H22.
            destruct H22,H23. apply H24 in H21.
            pose proof (OrderPM_Co8b 1 (-a) (-(1)) H14 H6 H15).
            apply H25 in H21; auto. 
            rewrite Mult_P4,PlusMult_Co4 in H21; auto.
            rewrite Mult_P4,<-PlusMult_Co3 in H21; auto. }
          apply Z_Corollary in H8'.
          pose proof (OrderPM_Co4 a (-(1)) (-(1)) a H8 H15).
          apply H18 in H15; auto.
          pose proof (Plus_neg1a 1 H14).
          rewrite Plus_P4 in H15; auto.
          unfold lt in H15; auto. destruct H15.
          contradiction.
          rewrite Plus_P4,H16,Minus_P1,ExpZ_one; auto. 
          pose proof (Mult_inv1 x H). 
          apply MKT4' in H17 as [].
          assert ((-(-(1))) = 1).
          { rewrite PlusMult_Co3,PlusMult_Co5,Mult_P1; auto. }
          assert (x \^ (- (1)) = x⁻).
          { apply AxiomI; split; intros.
            apply AxiomII in H20 as []. apply H21.
            apply AxiomII; split; eauto.
            apply AxiomII'; split. apply MKT49a; eauto.
            split. rewrite H16 in H8'; auto.
            right. left. split.
            apply AxiomII; split; eauto. rewrite H19.
            pose proof one_in_N; auto.
            rewrite H19,P_Ex2; auto.
            apply AxiomII; split; eauto. intros.
            apply AxiomII in H21 as [].
            assert ( [(-(1)), x ⁻] ∈ ExpFunction_Zt x).
            { apply AxiomII; split; eauto.
              apply MKT49a; eauto. exists (-(1)). exists x⁻.
              repeat split; auto. rewrite H16 in H8'; auto.
              right. left. split.
              apply AxiomII; split; eauto. rewrite H19.
              pose proof one_in_N; auto.
              rewrite H19,P_Ex2; auto. }   
            assert (y = x ⁻).
            { pose proof (Zt_Ex1 x H1). 
              unfold Function in H24. destruct H24.
              apply H25 with (-(1)); auto. }
            rewrite H24; auto. }
          rewrite H20,Mult_P4,Divide_P1; auto.
          rewrite H13. rewrite ExpZ_one; auto.
          pose proof (Plus_neg1a 1 H11).
          assert (a = -(1)).
          { pose proof (Minus_P1 1 H11). 
            rewrite Plus_P4 in H13; auto.
            apply Plus_Co3 in H13; auto.
            apply Plus_Co3 in H15; auto.
            rewrite H15,H13; auto. }
          rewrite H15. pose proof (Mult_inv1 x H).
          pose proof H16 as H16'. apply MKT4' in H16' as [].
          assert (x \^ (- (1)) = x⁻).
          { apply AxiomI; split; intros. 
            apply AxiomII in H19 as []. apply H20.
            assert ( 1 = (-(-(1)))).
            { rewrite PlusMult_Co3; auto.
              rewrite PlusMult_Co5,Mult_P1; auto.  }
            apply AxiomII; split; eauto.
            apply AxiomII'; split.
            apply MKT49a; eauto. repeat split.
            apply AxiomII; split; eauto.
            right. apply MKT4. left.
            apply AxiomII; split; eauto.
            pose proof one_in_N. rewrite <-H21; auto.
            right. left. split. apply AxiomII; split; eauto.
            rewrite <-H21. pose proof one_in_N; auto.
            rewrite <-H21. rewrite P_Ex2; auto.
            apply AxiomII; split; eauto. intros.
            apply AxiomII in H20 as [].
            apply AxiomII' in H21 as [H22[]].
            destruct H23,H23. pose proof one_in_N.
            pose proof (Nat_P1 1 (-(1)) H25 H23).
            destruct H26. rewrite Minus_P1 in H26; auto.
            pose proof zero_not_in_N. contradiction.
            destruct H23. assert ( 1 = (-(-(1)))).
            { rewrite PlusMult_Co3; auto.
              rewrite PlusMult_Co5,Mult_P1; auto. }
            rewrite <-H25 in H24. rewrite P_Ex2 in H24; auto.
            rewrite H24; auto.
            assert ( 1 = (-(-(1)))).
            { rewrite PlusMult_Co3; auto.
              rewrite PlusMult_Co5,Mult_P1; auto. }
            assert ((-(1)) ∈ \{ λ u,- u ∈ N \}).
            { apply AxiomII; split; eauto.
              rewrite <-H24. pose proof one_in_N.
              auto. } 
            destruct H23. rewrite H23 in H25.
            apply AxiomII in H25 as [].
            rewrite PlusMult_Co3,PlusMult_Co1 in H27; auto.
            pose proof zero_not_in_N. contradiction. }
          rewrite H19,Mult_P4,Divide_P1; auto. (*-n*)
    + pose proof one_in_R_Co. pose proof zero_in_R.
      apply MKT41 in H3; eauto. rewrite H3,ExpZ_one; auto.
      rewrite Plus_P4,Plus_P1; auto. 
      pose proof (Mult_P4 x 1 H1 H4). rewrite <-H6,Mult_P1; auto.
      pose proof one_in_N. rewrite ExpZ_equ; auto.
      rewrite P_Ex2; auto. (*n*)
Qed.
      

Corollary ExpZ_mult2 : ∀ x a b, x ∈ (R ~ [0]) -> a ∈ Z 
  -> b ∈ Z -> ((ExpFunction_Zt x)[a])·((ExpFunction_Zt x)[b]) 
  = (ExpFunction_Zt x)[a + b]. 
Proof.
  intros. apply AxiomII in H0 as [].
  apply AxiomII in H1 as []. pose proof H.
  apply MKT4' in H as []. pose proof one_in_N.
  destruct H2. destruct H3.
  - assert (∀ a, a ∈ N -> x \^ a · x \^ b = x \^ (a + b)).
    { apply Mathematical_Induction.
      - pose proof (ExpZ_equ x 1 H4 H6).
        rewrite H7. pose proof (P_Ex2 x H).
        rewrite H8. pose proof (Exp_close x b H H3).
        pose proof one_in_R_Co. pose proof H3 as H3'.
        apply N_Subset_R in H3'. rewrite (Plus_P4 1 b); auto.
        pose proof (Exp_close x b H H3).
        rewrite <-ExpZ_equ in H11; auto.
        rewrite Mult_P4; auto. pose proof one_in_N.
        pose proof (Nat_P1 b 1 H3 H12). destruct H13.
        pose proof (ExpZ_equ x (b + 1) H4 H13). rewrite H15.
        pose proof (ExpZ_equ x b H4 H3).
        rewrite P_Ex4,<-H16; auto.
      - intros. pose proof (P_Ex4 x k H4 H7).
        pose proof (ExpZ_equ x k H4 H7). 
        pose proof (Nat_P1 k 1 H7 H6). destruct H11.
        pose proof (ExpZ_equ x (k + 1) H4 H11).
        rewrite <-H13,<-H10 in H9. pose proof one_in_R_Co.
        pose proof H3 as H3'. apply N_Subset_R in H3'.
        pose proof (Plus_P4 b 1 H3' H14). 
        pose proof H7 as H7'. apply N_Subset_R in H7'.
        rewrite <-Plus_P3; auto. rewrite <-H15.
        rewrite Plus_P3; auto. pose proof (Nat_P1 k b H7 H3).
        destruct H16. pose proof (P_Ex4 x (k + b) H4 H16).
        pose proof (Nat_P1 (k + b) 1 H16 H6).
        destruct H19. pose proof (ExpZ_equ x (k + b) H4 H16).
        pose proof (ExpZ_equ x (k + b +1) H4 H19).
        rewrite <-H22,<-H21 in H18. rewrite H18,H9.
        pose proof (Exp_close x k H H7). 
        rewrite <-H10 in H23. pose proof (ExpZ_equ x b H4 H3).
        pose proof (Exp_close x b H H3). rewrite <-H24 in H25.
        pose proof (Mult_close (x \^ k) x H23 H).
        rewrite Mult_P4,Mult_P3; auto.
        pose proof (Mult_P4 (x \^ b) (x \^ k) H25 H23).
        rewrite H27,H8. auto. } apply H7 in H2. auto. (*nn*)   
  - apply AxiomII in H3 as []. destruct H7.
    + assert (∀ a, a ∈ N -> x \^ a · x \^ b = x \^ (a + b)).
      { assert (b ∈ Z). 
        { apply AxiomII; split; auto. right.
          apply MKT4. left. auto. }   
         apply Mathematical_Induction.
        - pose proof (ExpZ_equ x 1 H4 H6).
          rewrite H9. pose proof (P_Ex2 x H).
          rewrite H10. pose proof (ExpZ_ran1 x b H4 H8).
          pose proof one_in_R_Co. pose proof H8 as H8'.
          apply Z_Corollary in H8'.
          rewrite (Plus_P4 1 b); auto.
          pose proof (ExpZ_ran1 x b H4 H8).
          apply MKT4' in H13 as []. rewrite Mult_P4; auto.
          pose proof (ExpZ_mult1 x b H4 H8).
          symmetry; auto.
        - intros. pose proof (P_Ex4 x k H4 H9).
          pose proof (ExpZ_equ x k H4 H9). 
          pose proof (Nat_P1 k 1 H9 H6). destruct H13.
          pose proof (ExpZ_equ x (k + 1) H4 H13).
          rewrite <-H15,<-H12 in H11. pose proof one_in_R_Co.
          pose proof H8 as H8'. apply Z_Corollary in H8'.
          pose proof (Plus_P4 b 1 H8' H16). 
          pose proof H9 as H9'. apply N_Subset_R in H9'.
          rewrite <-Plus_P3; auto. rewrite <-H17,Plus_P3; auto.
          pose proof H9. apply Z_Corollary in H18.
          pose proof (Int_P1a k b H18 H8).
          pose proof (ExpZ_mult1 x (k + b) H4 H19).
          pose proof (ExpZ_ran1 x k H4 H18).
          pose proof (ExpZ_ran1 x b H4 H8).
          apply MKT4' in H21 as []. apply MKT4' in H22 as [].
          rewrite H11,H20,<-Mult_P3; auto.
          pose proof (Mult_close x (x \^ b) H H22).
          pose proof (Mult_P4 x (x \^ b) H H22). 
          rewrite H26,Mult_P3,H10; auto. }
        apply H8 in H2; auto. (*n,-n*)
      + pose proof zero_in_R. apply MKT41 in H7; eauto.
        rewrite H7,ExpZ_one; auto.
        pose proof H2 as H2'. apply N_Subset_R in H2'.
        rewrite Plus_P1; auto.
        pose proof (ExpZ_equ x a H4 H2). 
        pose proof (Exp_close x a H H2). rewrite H9.
        rewrite <- H9 in H10. pose proof one_in_R_Co.
        rewrite Mult_P1; auto. rewrite <-H9; auto. (*n,0*)
    - apply MKT4 in H2. destruct H2.
    + destruct H3.
      * assert (∀ b, b ∈ N -> x \^ a · x \^ b = x \^ (a + b)).
        { assert (a ∈ Z). 
          { apply AxiomII; split; auto. right.
            apply MKT4. left. auto. }   
           apply Mathematical_Induction.
          - pose proof (ExpZ_equ x 1 H4 H6).
            rewrite H8. pose proof (P_Ex2 x H).
            rewrite H9. pose proof (ExpZ_ran1 x a H4 H7).
            pose proof one_in_R_Co. pose proof H7 as H7'.
            apply Z_Corollary in H7'.
            pose proof (ExpZ_ran1 x a H4 H7).
            apply MKT4' in H12 as []. rewrite Mult_P4; auto.
            pose proof (ExpZ_mult1 x a H4 H7).
            rewrite H14; auto. rewrite Mult_P4; auto.
          - intros. pose proof (P_Ex4 x k H4 H8).
            pose proof (ExpZ_equ x k H4 H8). 
            pose proof (Nat_P1 k 1 H8 H6). destruct H12.
            pose proof (ExpZ_equ x (k + 1) H4 H12).
            rewrite <-H14,<-H11 in H10. pose proof one_in_R_Co.
            pose proof H7 as H7'. apply Z_Corollary in H7'.
            pose proof (Plus_P4 a 1 H7' H15). 
            pose proof H8 as H8'. apply N_Subset_R in H8'.
            rewrite Plus_P3; auto. pose proof H8.
            apply Z_Corollary in H17.
            pose proof (Int_P1a a k H7 H17).
            pose proof (ExpZ_mult1 x (a + k) H4 H18).
            pose proof (ExpZ_ran1 x k H4 H17).
            pose proof (ExpZ_ran1 x a H4 H7).
            apply MKT4' in H20 as []. apply MKT4' in H21 as [].
            rewrite H10,H19,<-H9,<-Mult_P3; auto. }
        apply H7 in H3; auto. (*-n,n*)
      * apply MKT4 in H3. destruct H3.
        -- assert (a ∈ Z).
           { apply AxiomII; split; auto.
             right. apply MKT4. left; auto. }
           assert (b ∈ Z).
           { apply AxiomII; split; auto.
             right. apply MKT4. left; auto. }
           pose proof (Z_Ex x a H4 H2).
           pose proof (Z_Ex x b H4 H3).
           pose proof (Int_P1a a b H7 H8). 
           pose proof one_in_R_Co.
           pose proof (Plus_neg1a 1 H12).
           assert (a + b ∈ \{ λ u,- u ∈ N \}).
           { apply AxiomII; split; eauto.
             apply AxiomII in H2 as [].
             apply AxiomII in H3 as [].
             pose proof (Nat_P1 (-a) (-b) H14 H15).
             destruct H16. apply Z_Corollary in H11.
             rewrite PlusMult_Co3,Mult_P4,Mult_P5; eauto.
             apply Z_Corollary in H7.
             apply Z_Corollary in H8.
             rewrite Mult_P4,<-PlusMult_Co3; auto.
             rewrite Mult_P4,<-PlusMult_Co3; auto.
             apply Z_Corollary in H7; auto.
             apply Z_Corollary in H8; auto. }
           pose proof (Z_Ex x (a + b) H4 H14).
           rewrite H9,H10,H15.
           pose proof H2 as H2'. apply AxiomII in H2' as [].
           pose proof H3 as H3'. apply AxiomII in H3' as [].
           assert (-a ∈ Z). { apply AxiomII; split; eauto. }
           assert (-b ∈ Z). { apply AxiomII; split; eauto. }
           pose proof (ExpZ_ran1 x (-a) H4 H20).
           pose proof (ExpZ_ran1 x (-b) H4 H21).
           pose proof (Mult_inv1 (x \^ (- a)) H22).
           pose proof (Mult_inv1 (x \^ (- b)) H23).
           apply MKT4' in H24 as []. apply MKT4' in H25 as [].
           pose proof (Mult_P1 (x \^ (- a))⁻ H24).
           pose proof (Mult_P1 (x \^ (- b))⁻ H25).
           rewrite Mult_P4 in H28; auto.
           rewrite Mult_P4 in H29; auto.
           rewrite <-H28,<-H29; auto.
           pose proof (Frac_P2 1 (x \^ (- a)) 1 (x \^ (- b)) H12 H22 H12 H23).
           pose proof H22 as H22'. pose proof H23 as H23'.
           apply MKT4' in H22 as [].
           apply MKT4' in H23 as []. 
           pose proof (Mult_close (x \^ (-a)) (x \^ (-b)) H22 H23).
           assert ((x \^ (- a) · x \^ (- b)) ⁻ ∈ (R ~ [0])).
           { apply Mult_inv1. apply MKT4'; split; eauto.
             pose proof zero_in_R.
             apply AxiomII; split; eauto. intro.
             apply MKT41 in H35; eauto.
             apply PlusMult_Co2 in H35; eauto.
             destruct H35. apply AxiomII in H31 as [].
             elim H36. apply MKT41; eauto.
             apply AxiomII in H32 as []. elim H36.
             apply MKT41; eauto. }
           apply MKT4' in H34 as [].
           rewrite H30,Mult_P1,Mult_P4,Mult_P1; eauto.
           apply Z_Corollary in H7. apply Z_Corollary in H8.
           pose proof (Plus_close a b H7 H8) as HM.
           assert(x \^ (- a) · x \^ (- b) = x \^ (- (a + b))).
           { pose proof (ExpZ_equ x (-a) H4 H17).
             pose proof (ExpZ_equ x (-b) H4 H19).
             apply AxiomII in H14 as [].
             pose proof (ExpZ_equ x (-(a + b)) H4 H38).
             rewrite H36,H37,H39. 
             assert (-(a + b) = -a -b). 
             { rewrite PlusMult_Co3,Mult_P4,Mult_P5; eauto.
               rewrite Mult_P4,<-PlusMult_Co3; eauto.
               rewrite Mult_P4,<-PlusMult_Co3; eauto. }
           rewrite H40. 
           pose proof (Exp_mult2 x (-a) (-b) H4 H17 H19).
           auto. }
           rewrite H36; auto.(*-n,-n*)
        -- pose proof zero_in_R. apply MKT41 in H3; eauto.
           rewrite H3,ExpZ_one; auto.
           assert (a ∈ Z). 
           { apply AxiomII; split; auto. right.
             apply MKT4. left. auto. }
           pose proof H8 as H8'. apply Z_Corollary in H8.
           rewrite Plus_P1; auto.
           pose proof (ExpZ_ran1 x a H4 H8').
           apply MKT4' in H9 as []. pose proof one_in_R_Co.
           rewrite Mult_P1; auto. (*-n,0*)
    + pose proof zero_in_R. apply MKT41 in H2; eauto.
      pose proof one_in_R_Co.
      assert (b ∈ Z). { apply AxiomII; auto. }
      pose proof (ExpZ_ran1 x b H4 H9).
      apply MKT4' in H10 as [].
      rewrite H2,ExpZ_one,Mult_P4,Mult_P1; auto.
      pose proof H9 as H9'. apply Z_Corollary  in H9'.
      pose proof (Plus_P4 0 b H7 H9'). 
      rewrite H12,Plus_P1; auto. (*0,z*)
Qed.


Corollary ExpZ_mult3: ∀ x m, x ∈ (R ~ [0]) -> m ∈ Z 
    -> ((ExpFunction_Zt x)[m])·((ExpFunction_Zt x)[(-m)]) = 1.
Proof.
  intros. apply AxiomI; split; intros.
  pose proof H0. apply Int_P3 in H2 as [H2[]].
  - pose proof H. apply (ExpZ_mult2 x m (-m)) in H; eauto.
    rewrite H3 in H. rewrite  ExpZ_one in H; auto.
    rewrite H in H1; auto.
  - pose proof H. pose proof H0.
    apply Int_P3 in H0 as [H0[]].
    pose proof (ExpZ_mult2 x m (-m) H2 H3 H0) ; eauto.
    rewrite H4 in H6. rewrite ExpZ_one in H6; auto.
    rewrite H6; auto.
Qed. 

    
(* 作用在有理数上的指数运算(1/n) *)
Theorem Q_Ex1: ∀ n x, n ∈ N -> x ∈ R /\ 0 < x
  -> exists r, 0 < r /\ r ^ n = x.
Proof.
Admitted.


(* 最后再定义1/n *)