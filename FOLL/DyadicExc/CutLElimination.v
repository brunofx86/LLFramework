Require Export LL.FOLL.DyadicExc.Tactics.

Set Implicit Arguments.

Section CutLElimination.

Context `{OLS: OLSig}.
 
 Theorem CutL  a b C M N O B : CutH (complexity C) (a+b) -> CutW (complexity C) -> 
 LL3 a |-- B; C::M ->
 LL3 b |-- B; N++(dual C)::O ->
 LL3 |-- B; M ++ N ++ O.
Proof with sauto; try dualSimpl.   
 intros CH CW Ha Hb.
 destruct N.
 -
 inversion Ha;subst.
 * solvell3.
 * inversion Hb... 
   solvell3.
   putFirst H0.
   cutLH Ha H0.
   LL3copy F. 
   apply Permutation_vs_cons_inv' in H...
   cutLH Ha H0.
   exact Bot.
   rewrite H2...  
 * inversion Hb... 
    putFirst H0.
    cutLH Ha H0.
    LL3copy F. 
    rewrite Permutation_middle...   
    apply Permutation_vs_cons_inv' in H...
    cutLH Ha H0.
    exact Bot.
    rewrite H2...
 * inversion Hb...
    putFirst H4.
    cutLW H2 H4.
    simpl...
    LL3copy F0.
    putFirst H0.   
    cutLH Ha H0.
    rewrite Permutation_middle...
    apply Permutation_vs_cons_inv' in H...
    rewrite H3.
    cutLH Ha H0.
 * inversion Hb...
    putFirst H6.
    cutLW H2 H6.
    simpl...
    LL3copy F0.
    putFirst H0.   
    cutLH Ha H0.
    rewrite Permutation_middle...
    apply Permutation_vs_cons_inv' in H...
    rewrite H3.
    cutLH Ha H0.
 * inversion Hb...
    putFirst H2.
    cutLW H3 H2.
    simpl...
    putFirst H2.
    cutLW H4 H2.
    simpl...
    LL3copy F0.
    putFirst H0.   
    cutLH Ha H0.
    rewrite Permutation_middle...
    apply Permutation_vs_cons_inv' in H...
    rewrite H2.
    cutLH Ha H0.
 * inversion Hb...
    solvell3.
    LL3copy F.
    putFirst H0.   
    cutLH Ha H0.
    rewrite Permutation_middle...
    apply Permutation_vs_cons_inv' in H...
    rewrite H3.
    cutLH Ha H0.
    exact Bot.
 * inversion Hb...
    putFirst H4.
    cutLW H2 H4. 
    simpl...
    assert(LL3 |-- B; G:: (M ++ M0))...
    apply LL3StoLL3N in H...
    putFirst H6.
    cutLW H H6.
    simpl...
    rewrite app_assoc...
    putFirst H0.   
    cutLH Ha H0.
    LL3copy F0.
    rewrite Permutation_middle...
    apply Permutation_vs_cons_inv' in H...
    cutLH Ha H0. 
    rewrite H3...
 * inversion Hb...
    putFirst H2.
    cutLW H4 H2. 
    simpl...
    assert(LL3 |-- B; N ++ [F ^] ++ O)...
    apply LL3StoLL3N in H...
    simpl in H.
    cutLW H3 H.
    simpl...
    rewrite app_assoc_reverse...
    putFirst H0.   
    cutLH Ha H0.
    LL3copy F0.
    rewrite Permutation_middle...
    apply Permutation_vs_cons_inv' in H...
    cutLH Ha H0. 
    rewrite H2...
 * cutCH H2 Hb.    
 * inversion Hb...
    rewrite (ng_involutive F) in Ha.
    putFirst Ha.
    cutCH H3 Ha...
    simpl...
    putFirst H0.   
    cutLH Ha H0.
    LL3copy F0.
    apply Permutation_vs_cons_inv' in H...
    cutLH Ha H0. 
    rewrite H3...
 * inversion Hb...
   assert(proper t) by auto.
   apply H7 in H4.
   putFirst H4.
   cutLW H5 H4.
   simpl...
   assert(proper (VAR con 0%nat)) by constructor.
   specialize (ComplexityUniformEq H1 H H0);intros...
   putFirst H0.   
   cutLH Ha H0.
   LL3copy F.
   rewrite Permutation_middle...
   apply Permutation_vs_cons_inv' in H...
   cutLH Ha H0. 
   rewrite H3...
 * inversion Hb...
   assert(proper t) by auto.
   apply H4 in H6.
   putFirst H7.
   cutLW H6 H7.
   simpl...
   assert(proper (VAR con 0%nat)) by constructor.
   specialize (ComplexityUniformEq H3 H H0);intros...
   putFirst H0.   
   cutLH Ha H0.
   LL3copy F.
   rewrite Permutation_middle...
   apply Permutation_vs_cons_inv' in H...
   cutLH Ha H0.
   exact Bot. 
   rewrite H2...
 * putFirst H0.
   simpl in Hb.
   rewrite (ng_involutive C) in H0.
   cutLH Hb H0...
   simpl in HCUT...
   rewrite Permutation_app_comm...
   LL3copy F. 
   rewrite Permutation_middle...
 * apply Permutation_vs_cons_inv' in H...
   rewrite (ng_involutive C) in H0.
   cutLH Hb H0...
   simpl in HCUT...
   rewrite Permutation_app_comm...
   rewrite H2...
 -
   LL3exchangeL (o::M++N++O).
   rewrite <- app_comm_cons in Hb.
   inversion Hb...
    * inversion H1...
      solvell3.
   *  rewrite app_comm_cons in H2.
      cutLH Ha H2.
      LL3plus1.  
      rewrite Permutation_middle...
   *  rewrite app_comm_cons in H2.
      cutLH Ha H2.
      LL3plus2.  
      rewrite Permutation_middle...
   * rewrite app_comm_cons in H3.
     rewrite app_comm_cons in H4.
     cutLH Ha H3.
     cutLH Ha H4.
     LL3with. 
     LL3exchangeL (M ++ (F :: N) ++ O).
     LL3exchangeL (M ++ (G :: N) ++ O).
   * cutLH Ha H2.
   * rewrite app_comm_cons in H2.
     rewrite app_comm_cons in H2.
     cutLH Ha H2.
     LL3par. 
     LL3exchangeL (M ++ (F :: G :: N) ++ O).      
    * apply eq_then_Permutation in H0.
      rewrite Permutation_midle in H0.
      checkPermutationCases H0.
      rewrite <- H1.
      rewrite app_assoc.
      apply Permutation_vs_cons_inv' in H0...
      rewrite app_comm_cons in H3.
      cutLH Ha H3.
      LL3tensor ;try solvell3. 
      rewrite H2.
      rewrite Permutation_middle...
      rewrite <- H1.
      rewrite Permutation_app_rot.
      apply Permutation_vs_cons_inv' in H0...
      rewrite app_comm_cons in H4.
      cutLH Ha H4.
      LL3tensor;try solvell3. 
      rewrite H2.
      LL3exchangeL (M ++ (G :: x0) ++ x1).
   * apply @LL3weakeningN with (F:=F) in Ha.
     cutLH Ha H2.
   * rewrite app_comm_cons in H5.
     cutLH Ha H5.
     LL3exist t.
     LL3exchangeL (M ++ (FX t :: N) ++ O).
   * LL3forall.
     apply H4 in H.
     rewrite app_comm_cons in H.
     cutLH Ha H.
     LL3exchangeL (M ++ (FX x :: N) ++ O).
   * do 2 rewrite app_comm_cons in H0.
     cutLH Ha H0.
     LL3copy F.
     LL3exchangeL (M ++ (F :: o :: N) ++ O).
   * assert(Permutation  (o :: N ++ C ^ :: O)  (C ^ :: o :: N ++ O)) by perm.
     rewrite H1 in H. clear H1.
     apply Permutation_vs_cons_inv' in H...
     cutLH Ha H0. 
     LL3exchangeL (M++ (o :: N ++ O)).
     rewrite H2...
Qed.     
         
  End CutLElimination.