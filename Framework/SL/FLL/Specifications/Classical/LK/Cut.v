(** * System MALL for propositional multiplicative and additive linear logic

This file encodes the inference rules of the system MALL (two sided)
of propositional multiplicative additive linear logic.
 *)

Require Import LL.Framework.SL.FLL.Reasoning.
Require Export LL.Framework.SL.FLL.Specifications.Classical.OLCut.
Require Export LL.Framework.SL.FLL.Specifications.Classical.LK.Bipoles.
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
      LLtheory ((makeRRuleC TT )).
     LLtensor [⌈ t_ccon TT ⌉] Delta1.
    simpl. solveLL.
   - right. split... simpl. solveLL.
     intros.
      LLtheory ((makeRRuleC TT )).
     LLtensor (@nil oo) Delta1.
    simpl. solveLL.
 * exists BCAxiom.  
    do 3 intro.
    apply FocusingClause in H...
   - left. exists x0... simpl. solveLL.
     intros.
      LLtheory ((makeLRuleC FF )).
     LLtensor [⌊ t_ccon FF ⌋] Delta1.
    simpl. solveLL.
   - right. split... simpl. solveLL.
     intros.
      LLtheory ((makeLRuleC FF )).
     LLtensor (@nil oo) Delta1.
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
  destruct lab;destruct s.
  * do 3 intro. intros.
     apply FocusingClause in H...
     - inversion H4...
       inversion H7... 
       exists [⌈ Fo1 ⌉].
        exists n0, 3.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        left.
       exists x0...
       simpl.  solveLL.
       1-2: HProof.
       lia.
       intros.
       LLtheory ((makeLRuleU CNEG Fo1)).
      LLtensor [⌊ t_ucon CNEG Fo1⌋ ] Delta1.
      simpl.  solveLL.
     LLExact H2.
     - inversion H4...
       inversion H7... 
       exists [⌈ Fo1 ⌉].
        exists n0, 3.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        right.
       split...
       simpl.  solveLL.
       1-2: HProof.
       lia.
       intros.
      simpl.  solveLL.
     LLExact H.
  * do 3 intro. intros.
     apply FocusingClause in H...
     - inversion H4...
       inversion H7... 
       exists [⌊ Fo1 ⌋ ].
        exists n0, 3.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        left.
       exists x0...
       simpl.  solveLL.
       1-2: HProof.
       lia.
       intros.
       LLtheory ((makeRRuleU CNEG Fo1)).
      LLtensor [⌈ t_ucon CNEG Fo1 ⌉] Delta1.
      simpl.  solveLL.
     LLExact H2.
     - inversion H4...
       inversion H7... 
       exists [⌊ Fo1 ⌋ ].
        exists n0, 3.
        split...
        OLSolve.  
        inversion H0...
        inversion H...
        right.
       split...
       simpl.  solveLL.
       1-2: HProof.
       lia.
       intros.
      simpl.  solveLL.
     LLExact H.
Qed.

(** *** Binary connectives *)
Lemma wellBipoleLKB : wellFormedB.
Proof with sauto.
  unfold wellFormedB;intros.
  destruct lab;destruct s.
  * exists  BOneP.  
     do 3 intro. intros. autounfold in H.
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
       LLleft; solveLL.
       1-2: HProof.
       lia.
       intros.
       LLtheory ((makeLRuleB AND Fo1 Go1)).
      LLtensor [⌊ t_bcon AND Fo1 Go1 ⌋ ] Delta1.
      simpl. 
     LLleft; solveLL.
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
       LLright; solveLL.
       1-2: HProof.
       lia.
       intros.
       LLtheory ((makeLRuleB AND Fo1 Go1)).
      LLtensor [⌊ t_bcon AND Fo1 Go1 ⌋ ] Delta1.
      simpl. 
     LLright; solveLL.
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
       LLleft; solveLL.
       1-2: HProof.
       lia.
       intros.
       simpl. 
     LLleft; solveLL.
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
       LLright; solveLL.
       1-2: HProof.
       lia.
       intros.
       simpl. 
     LLright; solveLL.
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
          LLtheory ((makeRRuleB AND Fo1 Go1)).
          LLtensor [⌈ t_bcon AND Fo1 Go1 ⌉] Delta12.
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
          LLtheory ((makeLRuleB OR Fo1 Go1)).
          LLtensor [⌊ t_bcon OR Fo1 Go1 ⌋ ] Delta12.
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
       LLleft; solveLL.
       1-2: HProof.
       lia.
       intros.
       LLtheory ((makeRRuleB OR Fo1 Go1)).
      LLtensor [⌈ t_bcon OR Fo1 Go1 ⌉ ] Delta1.
      simpl. 
     LLleft; solveLL.
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
       LLright; solveLL.
       1-2: HProof.
       lia.
       intros.
       LLtheory ((makeRRuleB OR Fo1 Go1)).
      LLtensor [⌈ t_bcon OR Fo1 Go1 ⌉] Delta1.
      simpl. 
     LLright; solveLL.
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
       LLleft; solveLL.
       1-2: HProof.
       lia.
       intros.
       simpl. 
     LLleft; solveLL.
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
       LLright; solveLL.
       1-2: HProof.
       lia.
       intros.
       simpl. 
     LLright; solveLL.
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
          LLtensor x2 x3.
          1-2: solveLL. 1-2:HProof.
          LLExact H1.
          LLExact H6.
          lia.
          intros.
          LLtheory ((makeLRuleB IMP Fo1 Go1)).
          LLtensor [⌊ t_bcon IMP Fo1 Go1 ⌋] ( Delta1 ++ Delta2).
         simpl...
         LLtensor Delta1 Delta2.
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
          LLtensor x1 x2.
          1-2: solveLL. 1-2:HProof.
          LLExact H1.
          LLExact H6.
          lia.
          intros.
          LLtensor Delta1 Delta2.
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
      LLtheory ((makeRRuleB IMP Fo1 Go1)).
     LLtensor [⌈ t_bcon IMP Fo1 Go1 ⌉] Delta1.
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

(** *** Quantifiers *)
Lemma wellBipoleLKQ : wellFormedQ.
Proof with sauto.
  unfold wellFormedQ. intros.
  destruct lab;destruct s.
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

Lemma CutCoherenceNEG: CutCoherenceU cutR1 (rulesU CNEG).
Proof with sauto; try solveLL.
  unfold CutCoherenceU;intros.
  simpl...
Qed.

(** *** Binary Connectives *)
Lemma CutCoherenceAND: CutCoherenceB cutR1  (rulesB AND).
Proof with sauto;try solveLL.
  unfold CutCoherenceB;intros.
  simpl...
   LLPerm ((⌈ F ⌉^ ⊕ ⌈ G ⌉^):: ([⌊ F ⌋^])).
  apply InvPlus...
   LLPerm ((⌈ F ⌉^ ⊕ ⌈ G ⌉^):: ([⌊ G ⌋^])).
  apply InvPlusComm...
Qed. 

Lemma CutCoherenceOR: CutCoherenceB cutR1  (rulesB OR).
Proof with sauto; try solveLL.
  unfold CutCoherenceB;intros.
  simpl...
   LLPerm ((⌊ F ⌋^ ⊕ ⌊ G ⌋^):: ([⌈ F ⌉^])).
  apply InvPlus...
   LLPerm ((⌊ F ⌋^ ⊕ ⌊ G ⌋^):: ([⌈ G ⌉^])).
  apply InvPlusComm...
Qed.

Lemma CutCoherenceIMP: CutCoherenceB cutR1 (rulesB IMP).
Proof with sauto; try solveLL.
  unfold CutCoherenceB;intros.
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
  apply CutCoherenceNEG.
  split;intros; try destruct lab.
  apply CutCoherenceAND.
  apply CutCoherenceOR.
  apply CutCoherenceIMP.
Qed.
 
Check OLCutElimination wellTheoryLK CutCoherenceLK.  