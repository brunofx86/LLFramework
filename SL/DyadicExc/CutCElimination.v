Require Export LL.SL.DyadicExc.DYTactics.

Set Implicit Arguments.

Section CutCElimination.

Context `{OLS: OLSig}.

   Theorem CutC  a b P Q M N O B : CutH (complexity P) (a+b) -> CutW (complexity P) -> S (complexity Q) = complexity P ->
      LL3 a |-- Q::B; M -> 
      LL3 b |-- B; N++[! Q ^]++O ->  
      LL3 |-- B; M++N++O.
    Proof with sauto;try dualSimpl.
    intros HC WC Hc Ha Hb.
    destruct N.
    * inversion Hb...
    2:{ apply Permutation_vs_cons_inv' in H...
        cutCH Ha H0.
       rewrite H2...  }
    2:{ simpl in H0. putFirst H0. 
        cutCH Ha H0.
        LL3copy F. 
        LL3exchangeL (M ++ [F] ++ O). }
      inversion Ha...
        + LL3tensor.
          putFirst Hb. 
          cutCH H Hb.
          putFirst Hb. 
          cutCH H0 Hb.
        + LL3plus1.
          putFirst Hb. 
          cutCH H Hb.
        + LL3plus2.
          putFirst Hb. 
          cutCH H Hb.
        + LL3bang.
          putFirst Hb. 
          cutCH H Hb.
        + rewrite <- H.
          putFirst Hb. 
          cutCH H0 Hb.
        + LL3bot.
          putFirst Hb. 
          cutCH H Hb.
        + LL3par.
          putFirst Hb. 
          cutCH H Hb.
        + LL3with.
          putFirst Hb. 
          cutCH H Hb.
          putFirst Hb. 
          cutCH H0 Hb.
        + LL3store.
          rewrite perm_swap in H...
          eapply @LL3weakeningN with (F:=F) in Hb...
          putFirst Hb. 
          cutCH H Hb.
        + inversion H... 
          - putFirst Hb. cutCH H0 Hb.
            assert(LL3 |-- B; F :: M)...
            apply LL3StoLL3N in H... 
            putFirst H2.
            cutLW H H2.
         - LL3copy F.
           putFirst Hb. 
           cutCH H0 Hb.
        + LL3exist t.
          putFirst Hb. 
          cutCH H1 Hb.
        + LL3forall.
          apply H0 in H1.
          putFirst Hb. 
          cutCH H1 Hb.
   * LL3exchangeL ( o:: M ++ N ++ O).
      rewrite <- app_comm_cons in Hb.
      inversion Hb...
    + apply eq_then_Permutation in H0.
      rewrite Permutation_midle in H0.
      checkPermutationCases H0.
      rewrite <- H1.
      rewrite app_assoc.
      apply Permutation_vs_cons_inv' in H0...
      rewrite app_comm_cons in H3.
      cutCH Ha H3.
      LL3tensor ;try solvell3. 
      rewrite H2.
      rewrite Permutation_middle...
      rewrite <- H1.
      rewrite Permutation_app_rot.
      apply Permutation_vs_cons_inv' in H0...
      rewrite app_comm_cons in H4.
      cutCH Ha H4.
      LL3tensor;try solvell3. 
      rewrite H2.
      LL3exchangeL (M ++ (G :: x0) ++ x1).
   +  rewrite app_comm_cons in H2.
      cutCH Ha H2.
      LL3plus1.  
      rewrite Permutation_middle...
   +  rewrite app_comm_cons in H2.
      cutCH Ha H2.
      LL3plus2.  
      rewrite Permutation_middle...
   + assert(Permutation  (o :: N ++ ! Q ^ :: O)  (! Q ^ :: o :: N ++ O)) by perm.
     rewrite H1 in H. clear H1.
     apply Permutation_vs_cons_inv' in H...
     cutCH Ha H0. 
     LL3exchangeL (M++ (o :: N ++ O)).
     rewrite H2...
   + cutCH Ha H2.
   + rewrite app_comm_cons in H2.
     rewrite app_comm_cons in H2.
     cutCH Ha H2.
     LL3par. 
     LL3exchangeL (M ++ (F :: G :: N) ++ O).
   + rewrite app_comm_cons in H3.
     rewrite app_comm_cons in H4.
     cutCH Ha H3.
     cutCH Ha H4.
     LL3with. 
     LL3exchangeL (M ++ (F :: N) ++ O).
     LL3exchangeL (M ++ (G :: N) ++ O).
   + apply @LL3weakeningN with (F:=F) in Ha.
     rewrite perm_swap in Ha. cutCH Ha H2.
   + simpl in H0.
     do 2 rewrite app_comm_cons in H0...
     cutCH Ha H0.
     LL3copy F.
     LL3exchangeL (M ++ (F :: o :: N) ++ O).
   + rewrite app_comm_cons in H5.
     cutCH Ha H5.
     LL3exist t.
     LL3exchangeL (M ++ (FX t :: N) ++ O).
   + LL3forall.
     apply H4 in H.
     rewrite app_comm_cons in H.
     cutCH Ha H.
     LL3exchangeL (M ++ (FX x :: N) ++ O).
Qed.     

   End CutCElimination.
