Require Export R_Axioms.


Definition twoR := 1 + 1.

Notation "2" := twoR : R_scope.

Corollary OrderPM_Co12 : 1 < 2.
Proof.
  pose proof OrderPM_Co9. pose proof zero_in_R.
  pose proof one_in_R_Co. pose proof H1.
  pose proof (OrderPM_Co1 0 1 1 H0 H1 H2 H).
  pose proof (Plus_P1 1 H1). pose proof (Plus_P4 1 0 H1 H0).
  rewrite H5 in H4. rewrite H4 in H3. auto.
Qed.

Corollary OrderPM_Co13 : 0 < 2.
Proof.
  pose proof one_in_R_Co.
  assert (2 ∈ R).
  { pose proof (Plus_close 1 1 H H); auto. }  
  pose proof OrderPM_Co9. unfold lt in H1.
  destruct H1. pose proof zero_in_R.
  pose proof (Order_Co2 0 1 2 H3 H H0). apply H4.
  pose proof OrderPM_Co12. right. eauto.
Qed. 

Corollary two_in_R_Co : 2 ∈ (R ~ [0]).
Proof.
  apply MKT4'. repeat split.
  pose proof one_in_R_Co. apply (Plus_close 1 1 H H).
  apply AxiomII. split.
  pose proof (Plus_close 1 1). pose proof one_in_R_Co.
  pose proof H0. apply H in H0. unfold twoR. eauto. auto.
  intro. apply AxiomII in H as [].
  assert (Ensemble 0). { pose proof zero_in_R; eauto. } 
  apply MKT19 in H1. apply H0 in H1. 
  pose proof OrderPM_Co13. rewrite <- H1 in H2. destruct H2. auto.
Qed.

Global Hint Resolve OrderPM_Co12 OrderPM_Co13 two_in_R_Co : real.

Definition Dedekind1 := ∀ A B, A ⊂ R -> B ⊂ R -> A <> Φ -> B <> Φ
  -> (∀ a b, a ∈ A -> b ∈ B -> a ≤ b) -> ∃ c, c ∈ R
  /\ (∀ a b, a ∈ A -> b ∈ B -> (a ≤ c /\ c ≤ b)).

Definition Dedekind2 := ∀ A B, A ⊂ R -> B ⊂ R 
  -> A <> Φ -> B <> Φ -> A ∪ B = R 
  -> (∀ a b, a ∈ A -> b ∈ B -> a < b) 
  -> ∃ c, c ∈ R /\ (∀ a b, a ∈ A -> b ∈ B -> (a ≤ c /\ c ≤ b)).

Proposition Dedekind1_equ_Dedekind2 : Dedekind1 <-> Dedekind2.
Proof.
  split; intros.
  - unfold Dedekind2. intros. unfold Dedekind1 in H.
    apply H; eauto. intros. pose proof (H5 a b H6 H7).
    unfold lt in H8; tauto.
  - unfold Dedekind1. intros. unfold Dedekind2 in H.
    set (M := \{ λ u, u ∈ R /\ (∀ b, b ∈ B -> u < b) \}).
    set (N := \{ λ u, u ∈ R /\(((∃c, Max M c) /\ ∀ m, m ∈ M -> m < u) 
         \/((~(∃c, Max M c)) /\ ∀ m, m ∈ M -> m ≤ u))\}).
    assert (M ⊂ ]-∞ , +∞[).
    { unfold Included. intros. apply AxiomII in H5 as []. tauto. }
    assert (M <> Φ).
    { apply NEexE in H2. destruct H2.
      apply NEexE in H3. destruct H3.
      assert (x - 1 ∈ M).
      { apply AxiomII. split; auto.
        assert (x - 1 ∈ R); auto with real. eauto.
        split. assert (x - 1 ∈ R); auto with real. 
        intros.
        assert (x ≤ b). apply H4; auto.
        assert (x - 1 < x).
        { pose proof one_in_R_Co. pose proof OrderPM_Co9.
          pose proof (OrderPM_Co2 1 H8 H9).
          assert (-(1) ∈ R); auto with real. 
          assert (x ∈ R); auto with real. pose proof zero_in_R.
          pose proof (OrderPM_Co1 (-(1)) 0 x H11 H13 H12 H10).
          rewrite Plus_P4 in H14; auto with real. 
          assert (0 + x = x + 0). { apply Plus_P4; auto with real. }
          rewrite H15 in H14. rewrite Plus_P1 in H14; auto. }
        assert (x - 1 < b).
        { assert (x - 1 ∈ R); auto with real.
          assert (x ∈ R); auto with real. assert (b ∈ R); auto with real.
          assert (x - 1 < x /\ x ≤ b); auto with real.
          pose proof (Order_Co2 (x - 1) x b H9 H10 H11). destruct H13.
          left; auto. unfold lt; eauto. } auto. }
        apply NEexE; eauto. } 
    assert (N ⊂ ]-∞ , +∞[).
    { unfold Included. intros. apply AxiomII in H7 as [H7[]]. tauto. }
    assert (N <> Φ).
    { apply NEexE in H3. destruct H3. apply NEexE. exists x.
      apply AxiomII. repeat split; eauto.
      destruct (classic (∃ c, Max M c)).
      - left. destruct H8 as []. split; eauto.
        intros. apply AxiomII in H9 as [H9[]]. apply H11 in H3; auto.
      - assert (∀ x, x ∈ M -> ∃ c, c ∈ M /\ x < c).
        { intros. apply NNPP; intro. apply H8.
          exists x0. repeat split; unfold Included; intros; auto.
          destruct (Leq_P4 x1 x0); auto. TF (x0 = x1).
          rewrite H13. apply Leq_P1; auto. elim H10.
          exists x1. repeat split; auto. }
        right. split; auto. intros. New H10.
        apply H9 in H11 as [x0[]]. apply AxiomII in H10 as [H10[]].
        apply H14 in H3. destruct H3; auto.  }
    assert (∀ a b, a ∈ M -> b ∈ N -> a < b).
    { intros. pose proof H10. apply AxiomII in H10 as [H10[]].
      destruct H13. destruct H13. apply H14 in H9. auto.
      destruct H13.
      assert (∀ x, x ∈ M -> ∃ c, c ∈ M /\ x < c).
        { intros. apply NNPP; intro. apply H13.
          exists x. repeat split; unfold Included; intros; auto.
          destruct (Leq_P4 x x0); auto. TF (x = x0).
          rewrite H19. apply Leq_P1; auto. elim H16.
          exists x0. repeat split; auto. }
      pose proof H9. apply H15 in H9. apply H14 in H16.
      unfold lt. split; auto. TF(a = b).
      rewrite H17 in H9. destruct H9. destruct H9.
      apply AxiomII in H9 as [H9[]].
         }
    assert (M ∪ N = R). admit.
    New H10. apply H in H11 as [x[]]; auto. exists x.
    split; intros; auto. rewrite <-H10 in H11.
    apply MKT4 in H11 as [].
    + TF (a = x).
      * admit.
      * assert (a ∈ M).
        { apply AxiomII; split; eauto. split; auto. intros.
           }
      
        exists R. apply Plus_close; auto.
        apply Plus_neg1a; auto with real. split.
         intro.
        rewrite <-H16 in H15. }
      { intro. apply (H9 x x) in H15; auto. destruct H15; auto. }
      
    


             elim H8. } exists x.


        apply NEexE in H6. destruct H6.
        (* right. split. intro. destruct H8. unfold Max in H8.
        destruct H8 as [H8[]]. apply H10 in H6.  *)


        left. split. apply NEexE in H2. destruct H2.
        pose proof (H4 x1 x H2 H3). exists x0.
        unfold Max. repeat split; auto.
        



        unfold Max. exists (x0-1). repeat split. unfold Included. auto.
        apply AxiomII. split.
        assert (x0 - 1 ∈ R); auto with real. eauto. split.
        assert (x0 -1 ∈ R); auto with real. intros.
        pose proof (H4 x b H2 H9).
        assert (x0 - 1 < x0).
        { pose proof one_in_R_Co. pose proof OrderPM_Co9.
          pose proof (OrderPM_Co2 1 H11 H12).
          assert (-(1) ∈ R); auto with real. 
          assert (x0 ∈ R); auto with real. pose proof zero_in_R.
          pose proof (OrderPM_Co1 (-(1)) 0 x0 H14 H16 H15 H13).
          rewrite Plus_P4 in H17; auto with real. 
          assert (0 + x0 = x0 + 0). { apply Plus_P4; auto with real. }
          rewrite H18 in H17. rewrite Plus_P1 in H17; auto. }
        assert (x0 - 1 < b).
        { assert (x0 - 1 ∈ R); auto with real.
          assert (x0 ∈ R); auto with real. assert (b ∈ R); auto with real.
          assert (x0- 1 < x0 /\ x0 ≤ b); auto with real.
          pose proof (Order_Co2 (x0 - 1) x0 b H12 H13 H14). destruct H16.
          left; auto. unfold lt; eauto. } auto.
        intros. apply AxiomII in H9 as [H9[]]. apply H11 in H3. }
        apply NEexE; eauto. } 

            } }
    assert (∀m n, m ∈ M -> n ∈ N -> m < n).
    { intros. apply AxiomII in H6 as [H6[]]. apply AxiomII in H7 as [H7[]].
      apply NEexE in H2. destruct H2. apply NEexE in H3. destruct H3.
      apply H9 in H3. apply NEexE in H5. destruct H5. }

    apply NEexE in H5. destruct H5.

    
  
      


Definition Supremum_existence := ∀S , S ⊂ R -> S <> Φ 
  -> (∃ c, Upper S c )-> ∃ s, Sup1 S s.
(* 注意括号问题 箭头优先级高于存在*)

Proposition Dedekind_equ_mumtexist: 
  Dedekind2 <-> Supremum_existence.
Proof.
  split; intros. 
  - unfold Dedekind2 in H.
    unfold Supremum_existence. intros.
    set (B := \{ λ a, a ∈ R /\ ∀ x, x ∈ S -> x < a \}).
    set (A := R ~ B).
(*     destruct H2 as [x].  *)
    unfold Upper in H2. destruct H2,H2,H3. 
    (*前提的存在命题可以destruct*)
    set (a := x + 1).
    assert( ∀x0, x0 ∈ S -> x0 < a).
    { intros. unfold a. pose proof OrderPM_Co9.
      pose proof zero_in_R. pose proof one_in_R_Co.
      pose proof (OrderPM_Co1 0 1 x H7 H8 H3 H6).
      rewrite <- Plus_P4 in H9; auto. 
      rewrite Plus_P1 in H9; auto.
      assert (1 + x = x + 1).
      { pose proof (Plus_P4 1 x H8 H3); auto. }
        rewrite H10 in H9. 
        assert (x0 ∈ R).
        { unfold Included in H2. apply H2 in H5; auto. }
        assert (x + 1 ∈ R); auto with real.         
        pose proof (Order_Co2 x0 x (x+1) H11 H3 H12).
        apply H13. right. split; eauto. }
    assert (a ∈ B).
    { apply AxiomII; split. unfold a. 
      assert (x + 1 ∈ R); auto with real; eauto.
      split; auto. unfold a; auto with real. }
    assert (B <> Φ).
    { apply NEexE. eauto. }
    assert (∀x0, x0 ∈ S -> x0 ∉ B).
    { intros. intro. apply AxiomII in H9.
      destruct H9 as [H10[]]. apply H11 in H8.
      destruct H8. contradiction H12. auto. }
    assert (A <> Φ).
    { apply NEexE.
      assert (∀x0, x0 ∈ S -> x0 ∈ A).
      { intros. apply AxiomII. repeat split; eauto.
        apply AxiomII. split; eauto. }
      apply NEexE in H1. destruct H1.
       (*前提的存在命题可以destruct*)
      exists x0. apply H9 in H1; auto. }
    assert (A ∪ B = R).
    { apply AxiomI; split; intros.
      apply AxiomII in H10. destruct H10,H11.
      apply AxiomII in H11; tauto.
      apply AxiomII in H11; tauto.
      apply AxiomII; split; eauto.
      unfold A.
      destruct (classic (z ∈ B)). right. auto.
      left. apply AxiomII; repeat split; eauto.
      intros. apply AxiomII. split. eauto.
      intro. contradiction. }
    assert (A ⊂ R).
    {  unfold Included. intros. apply AxiomII in H11; tauto. }
    assert (B ⊂ R).
    { unfold Included. intros. apply AxiomII in H12; tauto. }
    assert (∃ c, c ∈ R /\ (∀ a b, a ∈ A -> b ∈ B 
    -> (a ≤ c /\ c ≤ b))).
    { apply (H A B); auto. intros.
        assert (a0 ∈ R); auto with real.
        assert (b ∈ R); auto with real.
        assert (∀z, z ∈ S -> z < b).
        { apply AxiomII in H14. destruct H14 as [_[]]. auto. }
        pose proof (Order_Co1 a0 b H15 H16). destruct H18; auto.
        destruct H18.
        assert (a0 ∈ B). 
        { apply AxiomII. split. eauto. split; auto.
          intros. assert (x0 ∈ R); auto with real. 
          apply H17 in H19. unfold lt in H19. destruct H19.
          assert (x0 ≤ b /\ b < a0); eauto.
          pose proof (Order_Co2 x0 b a0 H20 H16 H15).
          destruct H23. right. auto. unfold lt; eauto. }
        apply AxiomII in H13. destruct H13 as [_[]].
        apply AxiomII in H20 as []. contradiction.
        rewrite <- H18 in H14. apply AxiomII in H13.
        destruct H13 as [_[]]. apply AxiomII in H19 as [].
        contradiction. }
    destruct H13 as [c]. destruct H13.
    exists c. unfold Sup1. split.
    unfold Upper. repeat split; auto. intros.
    assert (∀x0, x0 ∈ S -> x0 ∈ A).
    { intros. apply AxiomII. repeat split; eauto.
      apply AxiomII. split; eauto. }
    apply H16 in H15. pose proof (H14 x0 a H15 H6); tauto.
    assert (∀m, m ∈ R /\ 0 < m -> c - m/2 < c).
    { intros. destruct H15.
      pose proof two_in_R_Co. pose proof (Mult_inv1 2 H17).
      pose proof OrderPM_Co13. apply MKT4' in H17 as [].
      pose proof (OrderPM_Co10 2 H17 H19).
      apply MKT4' in H18 as [].
      pose proof (OrderPM_Co5 m  2 ⁻ H15 H18). destruct H23.
      left. split; auto.
      assert (0 < m/2);unfold lt; auto. pose proof zero_in_R.
      pose proof (Mult_close m 2 ⁻ H15 H18).
      assert (c + 0 < c + m/2).
      { pose proof (OrderPM_Co1 0 (m/2) c H26 H27 H13 H25); auto.
        rewrite Plus_P4; auto. 
        assert ((m / 2 + c) = (c + m / 2)).
        { pose proof (Plus_P4 (m/2) c H27 H13). auto. }
        rewrite <- H29. auto. }
      rewrite Plus_P1 in H28; auto.
      assert (c - m/2  < (c + m/2)- m/2 ).
      { pose proof (Plus_neg1a (m/2) H27).
        assert (c + m/2 ∈ R).
        { pose proof (Plus_close c (m/2) H13 H27); auto. }
        pose proof (OrderPM_Co1 c (c + m/2) (-(m/2)) H13 H30 H29 H28).
        auto. }
      pose proof (Plus_neg1a (m/2) H27).
      pose proof (Plus_P3 c (m/2) (-(m/2)) H13 H27 H30). 
      rewrite <- H31 in H29.
      pose proof (Minus_P1 (m/2) H27). rewrite H32 in H29.
      pose proof (Plus_P1 c H13). rewrite H33 in H29. eauto. }
    pose proof one_in_R_Co. pose proof OrderPM_Co9.
    assert (1 ∈ R /\ 0 < 1); auto. apply H15 in H18. 
    assert ((c - 1 / 2) ∉ B).
    { intro. apply NEexE in H9.
      destruct H9. pose proof (H14 x0 (c - 1/2) H9 H19).
      destruct H20. 
      assert (c - c ≤ c - c - 1/2).
      { pose proof H13. apply Plus_neg1a in H13.
        assert (c - 1/2 ∈ R).
        { pose proof one_in_R_Co. pose proof two_in_R_Co.
          apply Mult_inv1 in H24. apply MKT4' in H24 as [].
          pose proof (Mult_close 1 2 ⁻ H23  H24).
          pose proof H26. apply Plus_neg1a in H26.
          pose proof (Plus_close c (-(1/2)) H22 H26). auto. }
          pose proof (Plus_Leq c (c - 1/2) (-c) H22 H23 H13 H21).
          assert (c - 1 / 2 - c = c - c - 1 / 2).
          { pose proof one_in_R_Co. pose proof two_in_R_Co.
            apply Mult_inv1 in H26. apply MKT4' in H26 as [].
            pose proof (Mult_close 1 2 ⁻ H25 H26).
            pose proof (Plus_neg1a (1/2) H28).
            pose proof (Plus_P4 (- (1/2)) (-c) H29 H13).
            pose proof (Plus_P3 c (-(1/2)) (-c) H22 H29 H13).
            rewrite H30 in H31. rewrite <- H31.
            rewrite (Plus_P3 c (-c) (- (1/2)) H22 H13 H29). auto. }
         rewrite H25 in H24. auto. }
      pose proof (Plus_neg2 c H13). rewrite H23 in H22.
      assert ((- (1/2)) ∈ R).
      { pose proof one_in_R_Co. pose proof two_in_R_Co.
        apply Mult_inv1 in H25. apply MKT4' in H25 as [].
        pose proof (Mult_close 1 2 ⁻ H24 H25).
        pose proof H27. apply Plus_neg1a in H27. auto. }
      pose proof zero_in_R. pose proof (Plus_P4 0 (- (1/2)) H25 H24).
      rewrite H26 in H22. rewrite Plus_P1 in H22; auto.
      pose proof two_in_R_Co. apply MKT4' in H27 as [].
      assert (0 <> (- (1/2))).
      { intro. rewrite <- H29 in H18. rewrite Plus_P1 in H18; auto.
        destruct H18. contradiction. }
      assert (0 < - (1 / 2)). { unfold lt. tauto. }
      pose proof OrderPM_Co13.
      pose proof (OrderPM_Co7 0  (- (1/2)) 2 H25 H24 H27 H30 H31).
      rewrite Mult_P4,PlusMult_Co1 in H32; auto. pose proof two_in_R_Co.
      pose proof (Mult_inv1 2 H33). pose proof one_in_R_Co.
      apply MKT4' in H34 as [].
      Check Mult_P3.
      rewrite <- (Mult_P3 1 2 ⁻ 2 H35 H34 H27) in H32.
      
     

         }   } 


    
    
    
  assert (c ∈ Y)
  { apply AxiomII; split; eauto repeat split; auto. intros.
    apply NEexE in H2 as [y]. apply (H5 x0 y) in H6; tauto. }
  assert (Sup2 X c).
  { repeat split; auto. intros. apply NEexE in H0 as [x1].
    apply (H5 x1 x0) in H7; tauto. }
  exists c. split. apply Sup_Corollary; auto. intros.
  apply Sup_Corollary in H8. apply (Min_Corollary Y); auto.



























