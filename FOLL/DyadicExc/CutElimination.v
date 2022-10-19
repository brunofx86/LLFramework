Require Import LL.FOLL.DyadicExc.CutLElimination.
Require Import LL.FOLL.DyadicExc.CutCElimination.

Set Implicit Arguments.

Section CutElimination.

Context `{OLS: OLSig}.
      
 Theorem CutElimination i j C A B M N O :  
      (LL3 i |-- B; C::M -> LL3 j |-- B; N++ (dual C)::O-> LL3 |-- B; M ++ N ++ O) /\
      (S (complexity A) = complexity C -> LL3 i |-- A::B ; M -> LL3 j |-- B;N ++ (! (dual A))::O -> LL3 |-- B; M ++ N ++O).
  Proof with sauto.
  assert(exists w, complexity C = w).
    eexists; auto.
    destruct H as [w H].
    revert H.
    revert i j C A B O M N.
    
   induction w using lt_wf_ind; intros. 

   remember (plus i j) as h.
      revert dependent B.
      revert dependent M.
      revert dependent N.
      revert dependent O.
      
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
         move O at top.
        move C at top.
        move A at top.
        subst.
        rename C into P. 
         rename A into Q. 
        rename i into a. 
        rename j into b.
         split;intros.
         *  eapply (@CutL _ a b P M N O)...
          unfold Tactics.CutH; intros.
          eapply CutH with (m:=i + j)...
           unfold Tactics.CutW; intros.
           eapply CutW with (m:=complexity C)...
        * eapply (@CutC _ a b P Q M N O)...   
           unfold Tactics.CutH; intros.
          eapply CutH with (m:=i + j)...
           unfold Tactics.CutW; intros.
          eapply CutW with (m:=complexity C)...
          Qed.
    
     Theorem CutLL3 i j C B M N O:  
     LL3 i |-- B; C::M -> 
     LL3 j |-- B; N++(dual C)::O -> 
     LL3 |-- B; M ++ N ++ O.
 Proof.
    eapply CutElimination;auto.
 Qed.
   
 End CutElimination.
