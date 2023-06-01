Require Export LL.FOLL.Dyadic.Tactics.
Set Implicit Arguments.

Import DyadicTactics.
Section CutCElimination.
  Context `{OLS: OLSig}.

Theorem CutC i j P Q M N B : CutH (complexity P) (i + j) -> CutW (complexity P) -> S (complexity Q) = complexity P ->
 LL2 i |-- Q::B; M ->
 LL2 j |-- B; (! dual Q)::N ->
 LL2 |-- B; M ++ N.
Proof with sauto; try dualSimpl.   
 intros CH CW Hc Hi Hj.
 inversion Hj...
 * checkPermutationCases H...
 * checkPermutationCases H...
   rewrite H1.
   LLtop (M++x). 
 * checkPermutationCases H...
   rewrite H2.
   LLleft F G (M++x);try solvell2.
   rewrite H in H0.
   putFirst H0 (! Q ^).
   cutH' Hi H0.
   rewrite Permutation_middle...
 * checkPermutationCases H...
   rewrite H2.
   LLright F G (M++x);try solvell2.
   rewrite H in H0.
   putFirst H0 (! Q ^).
   cutH' Hi H0.
   rewrite Permutation_middle...
 * checkPermutationCases H...
   rewrite H3.
   LLwith F G (M++x);try solvell2.
   rewrite H in H0.
   putFirst H0 (! Q ^).
   cutH' Hi H0.
   rewrite Permutation_middle...
   rewrite H in H1.
   putFirst H1 (! Q ^).
   cutH' Hi H1.
   rewrite Permutation_middle...
 * checkPermutationCases H...
   rewrite H2.
   LLbot (M++x);try solvell2.
   rewrite H in H0.
   cutH' Hi H0...
 * checkPermutationCases H...
   rewrite H2.
   LLpar F G (M++x);try solvell2.
   rewrite H in H0.
   putFirst H0 (! Q ^).
   cutH' Hi H0.
   rewrite Permutation_middle...   
   rewrite Permutation_middle...    
 * checkPermutationCases H...
   checkPermutationCases H...
   rewrite H3.
   rewrite <- H4.
   LLtensor F G (M++x0) N0;try solvell2.
   rewrite H in H0.
   putFirst H0 (! Q ^).
   cutH' Hi H0.
   rewrite Permutation_middle...
   rewrite H3.
   rewrite <- H4.
   LLtensor F G M0 (M++x0);try solvell2.
   rewrite H in H1.
   putFirst H1 (! Q ^).
   cutH' Hi H1.
   rewrite Permutation_middle...
 * checkPermutationCases H...
   rewrite H2.
   LLstore F (M++x);try solvell2.
   rewrite H in H0.
   apply @weakeningLL2N with (F:=F) in Hi.
   rewrite perm_swap in Hi.
   cutH' Hi H0...   
 * inversion Hi...
   - LLinit A.
   - rewrite H.
     LLtop M0.
   - rewrite H.
     LLleft F G M0;try solvell2.
     cutH' H0 Hj...
   - rewrite H.
     LLright F G M0;try solvell2.
     cutH' H0 Hj...
   - rewrite H.
     LLwith F G M0;try solvell2.
     cutH' H0 Hj...
     cutH' H1 Hj...
   - rewrite H.
     LLbot M0;try solvell2.
     cutH' H0 Hj...
   - rewrite H.
     LLpar F G M0;try solvell2.
     cutH' H0 Hj...
   - rewrite H.
     LLtensor F G M0 N;try solvell2.
     cutH' H0 Hj...
     cutH' H1 Hj...
   - rewrite H.
     LLstore F M0;try solvell2.
     rewrite perm_swap in H0.
     apply @weakeningLL2N with (F:=F) in Hj.
     cutH' H0 Hj...
   - eapply ll2_bang'. 
     cutH' H Hj...
   - rewrite H.
     LLexists t FX M0;try solvell2.
     cutH' H3 Hj...
   - rewrite H.
     LLforall FX M0;try solvell2.
     apply H1 in H3.
     cutH' H3 Hj...
   - inversion H...
     + cutH' H0 Hj...
       assert(LL2 |-- B; F :: M)...
       apply LL2StoLL2N in H...
       cutW H H2...
     + LLcopy F.
       cutH' H0 Hj...
 * checkPermutationCases H...
   rewrite H4.
   LLexists t FX (M++x);try solvell2.
   rewrite H in H2.
   putFirst H2 (! Q ^).
   cutH' Hi H2.
   rewrite Permutation_middle...
 * checkPermutationCases H...
   rewrite H3.
   LLforall FX (M++x);try solvell2.
   specialize (H1 _ H2). 
   rewrite H in H1.
   putFirst H1 (! Q ^).
   cutH' Hi H1.
   rewrite Permutation_middle...
 * LLcopy F. 
   putFirst H0 (! Q ^).
   cutH' Hi H0.
   rewrite Permutation_middle...  
Qed.   

End CutCElimination.
