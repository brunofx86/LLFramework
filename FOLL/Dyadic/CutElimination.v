Require Import LL.FOLL.Dyadic.CutLElimination.
Require Import LL.FOLL.Dyadic.CutCElimination. 
Require Import LL.FOLL.Dyadic.Tactics.
Set Implicit Arguments.

Section CutElimination.
  Context `{OLS: OLSig}.
   
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
     
        split;intros.
       *  eapply (@CutL _ a b P M N)...
          unfold Tactics.CutH; intros.
          eapply CutH with (m:=i+j)...
          unfold Tactics.CutW; intros.
          eapply CutW with (m:=complexity C)...
        * eapply (@CutC _ a b P Q M N)...
          unfold Tactics.CutH; intros.
          eapply CutH with (m:=i+j)...
          unfold Tactics.CutW; intros.
          eapply CutW with (m:=complexity C)...
Qed.

 Theorem CutLL2 i j C B M N:  
     LL2 i |-- B; C::M -> 
     LL2 j |-- B; (dual C)::N -> 
     LL2 |-- B; M ++ N.
 Proof.
    eapply CutElimination;auto.
 Qed.
 
End CutElimination.
