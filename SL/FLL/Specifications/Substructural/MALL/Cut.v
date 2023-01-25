(** * System MALL for propositional multiplicative and additive linear logic

This file encodes the inference rules of the system MALL (two sided)
of propositional multiplicative additive linear logic.
 *)

Require Import LL.SL.FLL.Reasoning.
Require Import LL.SL.FLL.Specifications.Substructural.OLCut.
Require Import LL.SL.FLL.Specifications.Substructural.MALL.Bipoles.
Set Implicit Arguments.

(** ** Well-formedness conditions *)

(** *** Constants *)
Lemma wellBipoleMALLC : wellFormedC.
Proof with sauto.
  unfold wellFormedC;intros.
  destruct lab.
Qed.


(** *** Unary connectives *)

Lemma wellBipoleMALLU : wellFormedU.
Proof with sauto. 
  unfold wellFormedU;intros.
  destruct lab.
Qed.


(** *** Binary connectives *)
Lemma wellBipoleMALLB : wellFormedB.
Proof with sauto.
  unfold wellFormedB;intros.
  destruct lab;destruct s.
  * exists  BOneP.  
     do 3 intro. intros.
     apply FocusingClause in H... 
     -  apply FocusingPar in H4...
        exists [⌊ Go1 ⌋;⌊ Fo1 ⌋ ].
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
      TFocus ((makeLRuleB TENSOR Fo1 Go1)).
     inversion H4.
     FLLsplit [⌊ t_bcon TENSOR Fo1 Go1 ⌋] Delta1.
    simpl. solveLL. 
    LLExact H2.
  - 
    apply FocusingPar in H4... 
    exists [⌊ Go1 ⌋;⌊ Fo1 ⌋].
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
  * exists BTwoPM.
     do 3 intro. intros.    
     - apply FocusingClause in H... 
        + apply FocusingTensor in H4... 
           eexists x2, x3, [⌈ Fo1 ⌉], [⌈ Go1 ⌉].
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
          TFocus ((makeRRuleB TENSOR Fo1 Go1)).
          inversion H7.
          FLLsplit [⌈ t_bcon TENSOR Fo1 Go1 ⌉] ( Delta1 ++ Delta2).
         simpl...
         FLLsplit Delta1 Delta2.
         1-2: solveLL.
         LLExact H4.
         LLExact H5.
        + apply FocusingTensor in H4... 
           eexists x1, x2, [⌈ Fo1 ⌉], [⌈ Go1 ⌉].
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
  * exists BTwoPM.
     do 3 intro. intros.    
     - apply FocusingClause in H... 
        + apply FocusingTensor in H4... 
           eexists x2, x3, [⌊ Fo1 ⌋], [⌊ Go1 ⌋].
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
          TFocus ((makeLRuleB PAR Fo1 Go1)).
          inversion H7.
          FLLsplit [⌊ t_bcon PAR Fo1 Go1 ⌋] ( Delta1 ++ Delta2).
         simpl...
         FLLsplit Delta1 Delta2.
         1-2: solveLL.
         LLExact H4.
         LLExact H5.
        + apply FocusingTensor in H4... 
           eexists x1, x2, [⌊ Fo1 ⌋], [⌊ Go1 ⌋].
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
        exists [⌈ Go1 ⌉ ;⌈ Fo1 ⌉  ].
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
      TFocus ((makeRRuleB PAR Fo1 Go1)).
     inversion H4.
     FLLsplit [⌈ t_bcon PAR Fo1 Go1 ⌉] Delta1.
    simpl. solveLL. 
    LLExact H2.
  - 
    apply FocusingPar in H4... 
    exists [⌈ Go1 ⌉ ;⌈ Fo1 ⌉  ].
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
       TFocus ((makeLRuleB WITH Fo1 Go1)).
      inversion H4.
      FLLsplit [⌊ t_bcon WITH Fo1 Go1 ⌋ ] Delta1.
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
       TFocus ((makeLRuleB WITH Fo1 Go1)).
      inversion H4.
      FLLsplit [⌊ t_bcon WITH Fo1 Go1 ⌋ ] Delta1.
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
          TFocus ((makeRRuleB WITH Fo1 Go1)).
          inversion H6.
          FLLsplit [⌈ t_bcon WITH Fo1 Go1 ⌉] Delta12.
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
           eexists x0,  [⌊ Fo1 ⌋ ], [⌊ Go1 ⌋ ].
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
          TFocus ((makeLRuleB OPLUS Fo1 Go1)).
          inversion H6.
          FLLsplit [⌊ t_bcon OPLUS Fo1 Go1 ⌋] Delta12.
         simpl... solveLL.
         LLExact H1.
         LLExact H4.
        + apply FocusingWith in H4... 
           eexists Delta,  [⌊ Fo1 ⌋ ], [⌊ Go1 ⌋ ].
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
       TFocus ((makeRRuleB OPLUS Fo1 Go1)).
      inversion H4.
      FLLsplit [⌈ t_bcon OPLUS Fo1 Go1 ⌉ ] Delta1.
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
       TFocus ((makeRRuleB OPLUS Fo1 Go1)).
      inversion H4.
      FLLsplit [⌈ t_bcon OPLUS Fo1 Go1 ⌉] Delta1.
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
Qed.

(** *** Quantifiers *)
Lemma wellBipoleMALLQ : wellFormedQ.
Proof with sauto.
  unfold wellFormedQ. intros.
  destruct lab.
Qed.

Lemma wellTheoryMALL : wellFormedTheory.
Proof.
  split.
  apply wellBipoleMALLC.
  split.
  apply wellBipoleMALLU.
  split; [apply wellBipoleMALLB | apply wellBipoleMALLQ].
Qed.

(** ** Cut-coherency properties *)

Require Import SL.FLL.InvPositivePhase.

(** *** Binary Connectives *)
Lemma CutCoherenceTENSOR: CutCoherenceBin cutR1 (rulesB TENSOR).
Proof with sauto; try solveLL.
  unfold CutCoherenceBin;intros.
  simpl...
  LLPerm ((⌊ F ⌋^ ⊗ ⌊ G ⌋^):: ([⌈ F ⌉^] ++ [⌈ G ⌉^])).
  apply InvTensor'...
Qed. 
  
Lemma CutCoherencePAR: CutCoherenceBin cutR1 (rulesB PAR).
Proof with sauto; try solveLL.
  unfold CutCoherenceBin;intros.
  simpl...
  LLPerm ((⌈ F ⌉^ ⊗ ⌈ G ⌉^):: ([⌊ F ⌋^] ++ [⌊ G ⌋^])).
  apply InvTensor'...
Qed. 
  

Lemma CutCoherenceWITH: CutCoherenceBin cutR1  (rulesB WITH).
Proof with sauto;try solveLL.
  unfold CutCoherenceBin;intros.
  simpl...
   LLPerm ((⌈ F ⌉^ ⊕ ⌈ G ⌉^):: ([⌊ F ⌋^])).
  apply InvPlus...
   LLPerm ((⌈ F ⌉^ ⊕ ⌈ G ⌉^):: ([⌊ G ⌋^])).
  apply InvPlusComm...
Qed. 


Lemma CutCoherenceOPLUS: CutCoherenceBin cutR1  (rulesB OPLUS).
Proof with sauto; try solveLL.
  unfold CutCoherenceBin;intros.
  simpl...
   LLPerm ((⌊ F ⌋^ ⊕ ⌊ G ⌋^):: ([⌈ F ⌉^])).
  apply InvPlus...
   LLPerm ((⌊ F ⌋^ ⊕ ⌊ G ⌋^):: ([⌈ G ⌉^])).
  apply InvPlusComm...
Qed.

Lemma CutCoherenceMALL : CutCoherence cutR1.
Proof.
  split;intros. 
  destruct lab...
  split;intros; try destruct lab.
  split;intros; try destruct lab. 
  apply CutCoherenceTENSOR.
  apply CutCoherencePAR.
  apply CutCoherenceWITH.
  apply CutCoherenceOPLUS.
Qed.
 
Check OLCutElimination wellTheoryMALL CutCoherenceMALL. 