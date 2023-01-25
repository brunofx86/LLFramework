(** * System MALL for propositional multiplicative and additive linear logic

This file encodes the inference rules of the system MALL (two sided)
of propositional multiplicative additive linear logic.
 *)

Require Import LL.SL.FLL.Reasoning.
Require Import LL.SL.FLL.Specifications.Classical.OLCut.
Require Import LL.SL.FLL.Specifications.Classical.LK.Bipoles.
Set Implicit Arguments.

(** ** Well-formedness conditions *)

(** *** Constants *)
Lemma wellBipoleLKC : wellFormedC.
Proof with sauto.
  unfold wellFormedC;intros.
  destruct lab;destruct s.
 * exists BCFail.  
    do 2 intro.
    apply FocusingClause in H...
   - inversion H3... 
     solvePolarity.
   - inversion H3... 
     solvePolarity.
 * exists BCAxiom.  
    do 3 intro.
    apply FocusingClause in H...
   - left. exists x0... simpl. solveLL.
     intros.
      TFocus ((makeRRuleC TT )).
     inversion H1.
     FLLsplit [⌈ t_ccon TT ⌉] Delta1.
    simpl. solveLL.
   - right. split... simpl. solveLL.
     intros.
      TFocus ((makeRRuleC TT )).
     inversion H2.
     FLLsplit (@nil oo) Delta1.
    simpl. solveLL.
 * exists BCAxiom.  
    do 3 intro.
    apply FocusingClause in H...
   - left. exists x0... simpl. solveLL.
     intros.
      TFocus ((makeLRuleC FF )).
     inversion H1.
     FLLsplit [⌊ t_ccon FF ⌋] Delta1.
    simpl. solveLL.
   - right. split... simpl. solveLL.
     intros.
      TFocus ((makeLRuleC FF )).
     inversion H2.
     FLLsplit (@nil oo) Delta1.
    simpl. solveLL.
 * exists BCFail.  
    do 2 intro.
    apply FocusingClause in H...
   - inversion H3... 
     solvePolarity.
   - inversion H3... 
     solvePolarity.
Qed.


(** *** Unary connectives *)

Lemma wellBipoleLKU : wellFormedU.
Proof with sauto. 
  unfold wellFormedU;intros.
  destruct lab.
Qed.


(** *** Binary connectives *)
Lemma wellBipoleLKB : wellFormedB.
Proof with sauto.
  unfold wellFormedB;intros.
  destruct lab;destruct s.
  * exists  BOneP.  
     do 3 intro. intros.
     apply FocusingClause in H... 
     -  apply FocusingPlus in H4...
        + exists [⌊ Fo1 ⌋].
        exists x1, 4.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        left.
       exists x0...
       simpl.  
       FLLleft; solveLL.
       1-2: HProof.
       lia.
       intros.
       TFocus ((makeLRuleB AND Fo1 Go1)).
      inversion H4.
      FLLsplit [⌊ t_bcon AND Fo1 Go1 ⌋ ] Delta1.
      simpl. 
     FLLleft; solveLL.
     LLExact H1.
        + exists [⌊ Go1 ⌋].
        exists x1, 4.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        left.
       exists x0...
       simpl.  
       FLLright; solveLL.
       1-2: HProof.
       lia.
       intros.
       TFocus ((makeLRuleB AND Fo1 Go1)).
      inversion H4.
      FLLsplit [⌊ t_bcon AND Fo1 Go1 ⌋ ] Delta1.
      simpl. 
     FLLright; solveLL.
     LLExact H1.
     -  apply FocusingPlus in H4...
        + exists [⌊ Fo1 ⌋].
        exists x0, 4.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        right.
       split... 
       simpl.  
       FLLleft; solveLL.
       1-2: HProof.
       lia.
       intros.
       simpl. 
     FLLleft; solveLL.
     LLExact H.
        + exists [⌊ Go1 ⌋].
        exists x0, 4.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        right.
       split... 
       simpl.  
       FLLright; solveLL.
       1-2: HProof.
       lia.
       intros.
       simpl. 
     FLLright; solveLL.
     LLExact H.
  * exists BTwoPA.
     do 3 intro. intros.    
     - apply FocusingClause in H... 
        + apply FocusingWith in H4... 
           eexists x0,  [⌈ Fo1 ⌉ ], [⌈ Go1 ⌉ ].
           exists x1, 4.
           split...
           1-2: OLSolve.
           1-2: inversion H0...
           1-2: inversion H...
           left.
          split...
          simpl... solveLL.
           1-2:HProof.
          LLExact H2.
          LLExact H5.
          lia.
          intros.
          TFocus ((makeRRuleB AND Fo1 Go1)).
          inversion H6.
          FLLsplit [⌈ t_bcon AND Fo1 Go1 ⌉] Delta12.
         simpl... solveLL.
         LLExact H1.
         LLExact H4.
        + apply FocusingWith in H4... 
           eexists Delta,  [⌈ Fo1 ⌉ ], [⌈ Go1 ⌉ ].
           exists x0, 4.
           split...
           1-2: OLSolve.
           1-2: inversion H0...
           1-2: inversion H...
           right.
          split...
          simpl... solveLL.
           1-2:HProof.
          LLExact H2.
          LLExact H5.
          lia.
          intros.
         simpl... solveLL.
         LLExact H.
         LLExact H1.
  * exists BTwoPA.
     do 3 intro. intros.    
     - apply FocusingClause in H... 
        + apply FocusingWith in H4... 
           eexists x0,  [⌊ Fo1 ⌋], [⌊ Go1 ⌋ ].
           exists x1, 4.
           split...
           1-2: OLSolve.
           1-2: inversion H0...
           1-2: inversion H...
           left.
          split...
          simpl... solveLL.
           1-2:HProof.
          LLExact H2.
          LLExact H5.
          lia.
          intros.
          TFocus ((makeLRuleB OR Fo1 Go1)).
          inversion H6.
          FLLsplit [⌊ t_bcon OR Fo1 Go1 ⌋ ] Delta12.
         simpl... solveLL.
         LLExact H1.
         LLExact H4.
        + apply FocusingWith in H4... 
           eexists Delta, [⌊ Fo1 ⌋], [⌊ Go1 ⌋ ].
           exists x0, 4.
           split...
           1-2: OLSolve.
           1-2: inversion H0...
           1-2: inversion H...
           right.
          split...
          simpl... solveLL.
           1-2:HProof.
          LLExact H2.
          LLExact H5.
          lia.
          intros.
         simpl... solveLL.
         LLExact H.
         LLExact H1.
  * exists  BOneP.  
     do 3 intro. intros.
     apply FocusingClause in H... 
     -  apply FocusingPlus in H4...
        + exists [⌈ Fo1 ⌉ ].
        exists x1, 4.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        left.
       exists x0...
       simpl.  
       FLLleft; solveLL.
       1-2: HProof.
       lia.
       intros.
       TFocus ((makeRRuleB OR Fo1 Go1)).
      inversion H4.
      FLLsplit [⌈ t_bcon OR Fo1 Go1 ⌉ ] Delta1.
      simpl. 
     FLLleft; solveLL.
     LLExact H1.
        + exists [⌈ Go1 ⌉ ].
        exists x1, 4.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        left.
       exists x0...
       simpl.  
       FLLright; solveLL.
       1-2: HProof.
       lia.
       intros.
       TFocus ((makeRRuleB OR Fo1 Go1)).
      inversion H4.
      FLLsplit [⌈ t_bcon OR Fo1 Go1 ⌉] Delta1.
      simpl. 
     FLLright; solveLL.
     LLExact H1.
     -  apply FocusingPlus in H4...
        + exists [⌈ Fo1 ⌉ ].
        exists x0, 4.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        right.
       split... 
       simpl.  
       FLLleft; solveLL.
       1-2: HProof.
       lia.
       intros.
       simpl. 
     FLLleft; solveLL.
     LLExact H.
        + exists [⌈ Go1 ⌉ ].
        exists x0, 4.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        right.
       split... 
       simpl.  
       FLLright; solveLL.
       1-2: HProof.
       lia.
       intros.
       simpl. 
     FLLright; solveLL.
     LLExact H.
  * exists BTwoPM.
     do 3 intro. intros.    
     - apply FocusingClause in H... 
        + apply FocusingTensor in H4... 
           eexists x2, x3, [⌈ Fo1 ⌉ ], [⌊ Go1 ⌋].
           exists x1, 4.
           split...
           1-2: OLSolve.
           1-2: inversion H0...
           1-2: inversion H...
           left.
          split...
          simpl...
          FLLsplit x2 x3.
          1-2: solveLL. 1-2:HProof.
          LLExact H1.
          LLExact H6.
          lia.
          intros.
          TFocus ((makeLRuleB IMP Fo1 Go1)).
          inversion H7.
          FLLsplit [⌊ t_bcon IMP Fo1 Go1 ⌋] ( Delta1 ++ Delta2).
         simpl...
         FLLsplit Delta1 Delta2.
         1-2: solveLL.
         LLExact H4.
         LLExact H5.
        + apply FocusingTensor in H4... 
           eexists x1, x2, [⌈ Fo1 ⌉ ], [⌊ Go1 ⌋].
           exists x0, 4.
           split...
           1-2: OLSolve.
           1-2: inversion H0...
           1-2: inversion H...
           right.
          split...
          simpl...
          FLLsplit x1 x2.
          1-2: solveLL. 1-2:HProof.
          LLExact H1.
          LLExact H6.
          lia.
          intros.
          FLLsplit Delta1 Delta2.
         1-2: solveLL.
         LLExact H.
         LLExact H4.
  * exists  BOneP.  
     do 3 intro. intros.
     apply FocusingClause in H... 
     -  apply FocusingPar in H4...
        exists [⌈ Go1 ⌉;⌊ Fo1 ⌋ ].
        exists x1, 5.
        split...
        OLSolve.  
        1-2: inversion H0...
        1-2: inversion H...
        left.
       exists x0...
       simpl. solveLL. 
       1-2: HProof.
       lia.
      intros.
      TFocus ((makeRRuleB IMP Fo1 Go1)).
     inversion H4.
     FLLsplit [⌈ t_bcon IMP Fo1 Go1 ⌉] Delta1.
    simpl. solveLL. 
    LLExact H2.
  - 
    apply FocusingPar in H4... 
    exists [⌈ Go1 ⌉;⌊ Fo1 ⌋].
    exists x0, 5.
    split...
    OLSolve. 
    1-2: inversion H0...
    1-2: inversion H...
    right.
    split...
    simpl. solveLL.
    1-2: HProof.
    lia.
    intros.
    simpl. solveLL.
    LLExact H.
Qed.  

 Theorem FocusingForallUP :
    forall n th (y: expr con) FX D G, proper y ->
    flln th n G D (DW (∀{ fun x : expr con => atom (up (FX x))})) ->
      exists m , n =  S (S (S m))  /\ flln th m G (atom (up (FX y ))::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H0... 
    inversion H6...
    2:{ inversion H8. }
    specialize (H9 _ H).
    inversion H9...
    eexists n0.
    split;eauto.
  Qed.
         
   Theorem FocusingForallDW :
    forall n th (y: expr con) FX D G, proper y ->
    flln th n G D (DW (∀{ fun x : expr con => atom (down (FX x))})) ->
      exists m , n =  S (S (S m))  /\ uniform_oo (fun x  => atom (down (FX x))) /\ flln th m G (atom (down (FX y))::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H0... 
    inversion H6...
    2:{ inversion H8. }
    specialize (H9 _ H).
    inversion H9...
    eexists n0.
    split...
  Qed.

   Theorem FocusingExistsUP :
    forall n th FX D G, 
    flln th n G D (DW (∃{ fun x : expr con => atom (up (FX x))})) ->
      exists m t, n =  S (S (S m))  /\ proper t /\ flln th m G (atom (up (FX t))::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H... 
    2:{ inversion H1. }  
    inversion H6...
    inversion H8...
    eexists n0, t.
    split;eauto.
  Qed.

   Theorem FocusingExistsDW :
    forall n th FX D G, 
    flln th n G D (DW (∃{ fun x : expr con => atom (down (FX x))})) ->
      exists m t, n =  S (S (S m))  /\ proper t /\ flln th m G (atom (down (FX t))::D) (UP [ ]).
  Proof with sauto.
    intros.
    inversion H... 
    2:{ inversion H1. }  
    inversion H6...
    inversion H8...
    eexists n0, t.
    split;eauto.
  Qed.
  
(** *** Quantifiers *)
Lemma wellBipoleLKQ : wellFormedQ.
Proof with sauto.
  unfold wellFormedQ. intros.
  destruct lab.
Qed.

Lemma wellTheoryLK : wellFormedTheory.
Proof.
  split.
  apply wellBipoleLKC.
  split.
  apply wellBipoleLKU.
  split; [apply wellBipoleLKB | apply wellBipoleLKQ].
Qed.

(** ** Cut-coherency properties *)

Require Import SL.FLL.InvPositivePhase.

(** *** Binary Connectives *)
Lemma CutCoherenceAND: CutCoherenceBin cutR1  (rulesB AND).
Proof with sauto;try solveLL.
  unfold CutCoherenceBin;intros.
  simpl...
   LLPerm ((⌈ F ⌉^ ⊕ ⌈ G ⌉^):: ([⌊ F ⌋^])).
  apply InvPlus...
   LLPerm ((⌈ F ⌉^ ⊕ ⌈ G ⌉^):: ([⌊ G ⌋^])).
  apply InvPlusComm...
Qed. 

Lemma CutCoherenceOR: CutCoherenceBin cutR1  (rulesB OR).
Proof with sauto; try solveLL.
  unfold CutCoherenceBin;intros.
  simpl...
   LLPerm ((⌊ F ⌋^ ⊕ ⌊ G ⌋^):: ([⌈ F ⌉^])).
  apply InvPlus...
   LLPerm ((⌊ F ⌋^ ⊕ ⌊ G ⌋^):: ([⌈ G ⌉^])).
  apply InvPlusComm...
Qed.

Lemma CutCoherenceIMP: CutCoherenceBin cutR1 (rulesB IMP).
Proof with sauto; try solveLL.
  unfold CutCoherenceBin;intros.
  simpl...
  LLPerm ((⌊ F ⌋^ ⊗ ⌈ G ⌉^):: ([⌈ F ⌉^] ++ [⌊ G ⌋^])).
  apply InvTensor'...
Qed. 
  
Lemma CutCoherenceLK : CutCoherence cutR1.
Proof.
  split;intros. 
  destruct lab...
  split;intros; try destruct lab.
  simpl. auto. simpl. solveLL. 
  split;intros; try destruct lab.
  simpl. auto. simpl. solveLL. 
  split;intros; try destruct lab.
  split;intros; try destruct lab.
  apply CutCoherenceAND.
  apply CutCoherenceOR.
  apply CutCoherenceIMP.
Qed.
 
Check OLCutElimination wellTheoryLK CutCoherenceLK. 