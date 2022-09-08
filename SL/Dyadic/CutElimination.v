(* Require Import FLL.SL.Dyadic.CutLElimination.
Require Import FLL.SL.Dyadic.CutCElimination. *)
Require Import LL.SL.Dyadic.OSTactics.
Set Implicit Arguments.

Section CutElimination.
  Context `{OLS: OLSig}.
   
Theorem CutElimBase C A B M N: 
      (LL2N 0 B (C::M) -> LL2N 0 B (dual C::N) -> LL2S B (M ++ N)) /\
      (S (complexity A) = complexity C -> LL2N 0 (A::B) M -> LL2N 0 B ((! dual A)::N) -> LL2S B (M ++ N)). 
  Proof with sauto; try dualSimpl.
    split;intros.
      - inversion H...
        + checkPermutationCases H1.
          solvell2.
          inversion H1...
          solvell2.
        + inversion H0...
          checkPermutationCases H1.
          checkPermutationCases H1.
          rewrite H3.
          LL2top x.
        + checkPermutationCases H1.
          inversion H0...
          checkPermutationCases H1.
          checkPermutationCases H1.
          rewrite H3.
          LL2top (M++x).
          rewrite H3.
          rewrite <- app_comm_cons.
          LL2top (x++N).
      - inversion H1...
        + checkPermutationCases H2.
        + checkPermutationCases H2.
          rewrite H4.
          LL2top (M++x). 
  Qed.
      
 Theorem CutElimination i j C A B M N:  
      (LL2 i |-- B; C::M -> LL2 j |-- B; (dual C)::N -> LL2 |-- B; M ++ N) /\
      (S (complexity A) = complexity C -> 
      LL2 i |-- A::B ; M -> LL2 j |-- B;(! (dual A))::N -> LL2 |-- B; M ++ N).
  Proof with sauto. 
    assert(exists w, complexity C = w).
    eexists; auto.
    destruct H as [w H].
    revert H.
    revert i j C A B M N.
   induction w using lt_wf_ind; intros. 
   remember (plus i j) as h.
      revert dependent B.
      revert dependent M.
      revert dependent N.
      
      revert dependent A.
      revert dependent C.
      
      revert dependent i.
      revert j.
      induction h using lt_wf_ind; intros.
      rename H into CutW.
        rename H0 into CutH.
        rename H1 into compC.
        
        move B at top.
        move M at top.
        move N at top.
        move C at top.
        move A at top.
        subst.
        rename C into P. 
         rename A into Q. 
        rename i into a. 
        rename j into b. 
        assert(CutH' : forall i j : nat,
       i + j < a + b ->
       forall C : oo,
       complexity C = complexity P ->
       forall (A : oo) (N M : list oo) (B : multiset oo),
       (LL2 i |-- B; C :: M -> LL2 j |-- B; C ^ :: N -> LL2 |-- B; M ++ N) /\
       (S (complexity A) = complexity C ->
        LL2 i |-- A :: B; M -> LL2 j |-- B; ! A ^ :: N -> LL2 |-- B; M ++ N)).
        
        intros.
        eapply CutH with (m:=i+j)...
        clear CutH.
        assert(CutW' :    forall (i j : nat) (C A : oo)
         (B : multiset oo) (M N : list oo),
       complexity C < complexity P ->
    
       (LL2 i |-- B; C :: M ->
        LL2 j |-- B; C ^ :: N ->
        LL2 |-- B; M ++ N) /\
       (S (complexity A) = complexity C ->
        LL2 i |-- A :: B; M ->
        LL2 j |-- B; ! A ^ :: N ->
        LL2 |-- B; M ++ N)).
         intros.
         
        eapply CutW with (m:=complexity C)...
        clear CutW.
        
         in CutW.
        split;intros.
       *  eapply (@CutL _ i j w h C M N)...
          unfold OSTactics.CutH; intros.
          eapply CutH with (m:=m)...
          unfold OSTactics.CutW; intros.
          eapply CutW with (m:=m)...
        * eapply (@CutC _ i j w h A M N)...
          unfold OSTactics.CutH; intros.
          eapply CutH with (m:=m)...
          unfold OSTactics.CutW; intros.
          eapply CutW with (m:=m)...
          rewrite compC in H...
Qed.

 Theorem CutLL2 i j C B M N:  
     LL2 i |-- B; C::M -> 
     LL2 j |-- B; (dual C)::N -> 
     LL2 |-- B; M ++ N.
 Proof.
    eapply CutElimination;auto.
 Qed.
 
End CutElimination.
