Require Import LL.PLL.CutLElimination.
Require Import LL.PLL.CutCElimination. 
Require Import LL.PLL.Tactics.
Set Implicit Arguments.

Section CutElimination.
   
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
       *  eapply (@CutL a b P M N)...
          unfold Tactics.CutH; intros.
          eapply CutH with (m:=i+j)...
          unfold Tactics.CutW; intros.
          eapply CutW with (m:=complexity C)...
        * eapply (@CutC a b P Q M N)...
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
 

 Theorem CutLL2' C B M N:  
     LL2  |-- B; C::M -> 
     LL2 |-- B; (dual C)::N -> 
     LL2 |-- B; M ++ N.
 Proof with sauto.
   intros.
   apply LL2StoLL2N in H, H0...
   refine (CutLL2 H H0). 
 Qed.

Section Application.

(******************************************************)
(*                    INVERTIBILITY: RULE BOT                     *)
(******************************************************)

Lemma invertibility_bot : forall B M, LL2S B  (Bot::M) -> LL2S B  M.
Proof with simpl;auto.
  intros.
  eapply CutLL2' with (C:=One) (M:=[]) (N:=M)...
Qed.

(*******************************************************)
(*                    INVERTIBILITY: RULE PAR                      *)
(*******************************************************)

Lemma invertibility_par : forall B M F G, 
                            LL2S B  (F ⅋ G::M) -> LL2S B  (F::G::M).
Proof with simpl;auto.
  intros.
  assert(LL2 |-- B; M ++ [F; G]).
  eapply CutLL2' with (C:=F ⅋ G) (M:=M) (N:=[F;G])...
  LLtensor (dual F) (dual G) [F] [G].
  1-2: rewrite perm_takeit_8.
  1-2: apply LLinitGen...
rewrite Permutation_app_comm in H0...
Qed.

(********************************************************)
(*                    INVERTIBILITY: RULE QUEST                    *)
(********************************************************)

Lemma invertibility_store : forall B M F,
                            LL2S B  (? F::M) -> LL2S (F::B)  M.
Proof with simpl;auto.
  intros. 
  eapply CutLL2' with (C:=! (dual F)) (M:=[]) (N:=M)...
  constructor.
  LLcopy F...
  apply LLinitGen...
  rewrite <- dualInvolutive.
  apply LL2weakening... 
Qed.
  
(********************************************************)
(*                    INVERTIBILITY: RULE WITH                     *)
(********************************************************)

Lemma invertibility_with : forall B M F G, 
     LL2S B (F & G::M) -> LL2S B (F::M) /\ LL2S B (G::M).
Proof with simpl;sauto.
  intros...
  - assert(LL2 |-- B; M ++ [F]).
    eapply CutLL2' with (C:=F & G) (M:=M) (N:=[F])...
   LLleft (dual F) (dual G) [F].
   rewrite perm_takeit_8.
   apply LLinitGen...
   rewrite Permutation_app_comm in H0...
  - assert(LL2 |-- B; M ++ [G]).
    eapply CutLL2' with (C:=F & G) (M:=M) (N:=[G])...
   LLright (dual F) (dual G) [G].
   rewrite perm_takeit_8.
   apply LLinitGen...
   rewrite Permutation_app_comm in H0...
Qed.

(********************************************************)
(*                    INVERTIBILITY: RULE BANG                     *)
(********************************************************)

Lemma invertibility_bang : forall B F, 
     LL2S B [! F] -> LL2S B [F].
Proof with simpl;sauto.
  intros...
  - assert(LL2 |-- B; [] ++ [F]).
    eapply CutLL2' with (C:= ! F) (M:=[]) (N:=[F])...
    LLstore (dual F) [F].
    LLcopy (dual F)...
   rewrite perm_takeit_8.
   apply LLinitGen...
   rewrite Permutation_app_comm in H0...
Qed.

End Application.
End CutElimination.
