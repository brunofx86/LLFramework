Require Export LL.FOLL.DyadicExc.Tactics.

Import DyadicExcTactics.
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
    3:{ apply Permutation_vs_cons_inv' in H...
        cutCH Ha H0.
       rewrite H2...  }
    2:{ simpl in H0. putFirst H0. 
        cutCH Ha H0.
        LLcopy F. 
        LL3exchangeL (M ++ [F] ++ O). }
      inversion Ha...
        + LLleft.
          putFirst Hb. 
          cutCH H Hb.
        + LLright.
          putFirst Hb. 
          cutCH H Hb.
        + LLwith.
          putFirst Hb. 
          cutCH H Hb.
          putFirst Hb. 
          cutCH H0 Hb.
        + LLbot.
          putFirst Hb. 
          cutCH H Hb.
        + LLpar.
          putFirst Hb. 
          cutCH H Hb.      
        + LLtensor.
          putFirst Hb. 
          cutCH H Hb.
          putFirst Hb. 
          cutCH H0 Hb.
        + LLstore.
          rewrite perm_swap in H...
          eapply @LL3weakeningN with (F:=F) in Hb...
          putFirst Hb. 
          cutCH H Hb.
        + LLbang.
          putFirst Hb. 
          cutCH H Hb.
        + LLexists t.
          putFirst Hb. 
          cutCH H1 Hb.
        + LLforall.
          apply H0 in H1.
          putFirst Hb. 
          cutCH H1 Hb.
        + inversion H... 
          - putFirst Hb. cutCH H0 Hb.
            assert(LL3 |-- B; F :: M)...
            apply LL3StoLL3N in H... 
            putFirst H2.
            cutLW H H2.
         - LLcopy F.
           putFirst Hb. 
           cutCH H0 Hb.
        + rewrite <- H.
           putFirst Hb. 
           cutCH H0 Hb.             
   * LL3exchangeL ( o:: M ++ N ++ O).
      rewrite <- app_comm_cons in Hb.
      inversion Hb...
   +  rewrite app_comm_cons in H2.
      cutCH Ha H2.
      LLleft.  
      rewrite Permutation_middle...
   +  rewrite app_comm_cons in H2.
      cutCH Ha H2.
      LLright.  
      rewrite Permutation_middle...
   + rewrite app_comm_cons in H3.
     rewrite app_comm_cons in H4.
     cutCH Ha H3.
     cutCH Ha H4.
     LLwith. 
     LL3exchangeL (M ++ (F :: N) ++ O).
     LL3exchangeL (M ++ (G :: N) ++ O).
   + cutCH Ha H2.
   + rewrite app_comm_cons in H2.
     rewrite app_comm_cons in H2.
     cutCH Ha H2.
     LLpar. 
     LL3exchangeL (M ++ (F :: G :: N) ++ O).
    + apply eq_then_Permutation in H0.
      rewrite Permutation_midle in H0.
      checkPermutationCases H0.
      rewrite <- H1.
      rewrite app_assoc.
      apply Permutation_vs_cons_inv' in H0...
      rewrite app_comm_cons in H3.
      cutCH Ha H3.
      LLtensor ;try solvell3. 
      rewrite H2.
      rewrite Permutation_middle...
      rewrite <- H1.
      rewrite Permutation_app_rot.
      apply Permutation_vs_cons_inv' in H0...
      rewrite app_comm_cons in H4.
      cutCH Ha H4.
      LLtensor;try solvell3. 
      rewrite H2.
      LL3exchangeL (M ++ (G :: x0) ++ x1).
   + apply @LL3weakeningN with (F:=F) in Ha.
     rewrite perm_swap in Ha. cutCH Ha H2.
   + rewrite app_comm_cons in H5.
     cutCH Ha H5.
     LLexists t.
     LL3exchangeL (M ++ (FX t :: N) ++ O).
   + LLforall.
     apply H4 in H.
     rewrite app_comm_cons in H.
     cutCH Ha H.
     LL3exchangeL (M ++ (FX x :: N) ++ O).
   + simpl in H0.
     do 2 rewrite app_comm_cons in H0...
     cutCH Ha H0.
     LLcopy F.
     LL3exchangeL (M ++ (F :: o :: N) ++ O).
   + assert(Permutation  (o :: N ++ ! Q ^ :: O)  (! Q ^ :: o :: N ++ O)) by perm.
     rewrite H1 in H. clear H1.
     apply Permutation_vs_cons_inv' in H...
     cutCH Ha H0. 
     LL3exchangeL (M++ (o :: N ++ O)).
     rewrite H2...     
Qed.     

   End CutCElimination.
