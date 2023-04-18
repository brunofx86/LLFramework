(** * System MALL for propositional multiplicative and additive linear logic

This file encodes the inference rules of the system MALL (two sided)
of propositional multiplicative additive linear logic.
 *)

Require Import LL.Framework.SL.FLL.Reasoning.
Require Export LL.Framework.SL.FLL.Specifications.Intuitionistic.OLCut.
Require Export LL.Framework.SL.FLL.Specifications.Intuitionistic.LJ.Bipoles.
Require Import LL.Framework.SL.FLL.InvPositivePhase.
Set Implicit Arguments.


(** ** Well-formedness conditions *)

(** *** Constants *)
Lemma wellBipoleLJC : wellFormedC'.
Proof with sauto.
  unfold wellFormedC';intros.
  destruct lab;destruct s.
 * exists Requirement1.BCFail.  
    do 2 intro.
    apply FocusingClause in H...
   - inversion H3... 
     solvePolarity.
   - inversion H3... 
     solvePolarity.
 * exists Requirement1.BCAxiom.  
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
 * exists Requirement1.BCAxiom.  
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
 * exists Requirement1.BCFail.  
    do 2 intro.
    apply FocusingClause in H...
   - inversion H3... 
     solvePolarity.
   - inversion H3... 
     solvePolarity.
Qed.


(** *** Unary connectives *)

Lemma wellBipoleLJU : wellFormedU'.
Proof with sauto. 
  unfold wellFormedU';intros.
  destruct lab.
Qed.


(** *** Binary connectives *)
Lemma wellBipoleLJB : wellFormedB'.
Proof with sauto.
  unfold wellFormedB';intros.
  destruct lab;destruct s.
 + exists Requirement1.BTwoPA.
     do 3 intro. intros.  
     apply FocusingClause in H...
    - apply FocusingWith in H4...
      exists x0, [⌊ Fo1 ⌋],  [⌊ Go1 ⌋], x1, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      do 2 constructor... 
      inversion H0...  inversion H... 
      left. split... simpl. solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
      LLExact H2.
      LLExact H5.
      lia. intros.
      LLtheory (makeLRuleB OR Fo1 Go1).
       
      LLtensor [⌊ t_bcon OR Fo1 Go1 ⌋ ] Delta12. 
      simpl. solveLL. LLExact H1. LLExact H4.
    - apply FocusingWith in H4...
      exists Delta, [⌊ Fo1 ⌋],  [⌊ Go1 ⌋], x0, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      do 2 constructor... 
      inversion H0...  inversion H... 
      right. split... simpl. solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
      LLExact H2.
      LLExact H5.
      lia. intros. 
      simpl; solveLL. 
      LLExact H. LLExact H1.
  + exists Requirement1.BOneP.
     do 3 intro. intros. 
     apply FocusingClause in H...
    - apply FocusingPlusPos in H4...
      exists [!⌈ Fo1 ⌉], (S (S (S x1))), 1%nat.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      left. exists []...
      LLleft. solveLL. 
      apply seqNtoSeq in H5...
      LLfocus1. 
      lia. intros.
      LLPerm ([⌈ t_bcon OR Fo1 Go1 ⌉] ++ Delta1++[]).
      eapply InvTensorT'. exact H. solveLL.
      simpl... solveLL.
      eapply InvPlus... solveLL. LLExact H1.       
exists [!⌈ Go1 ⌉], (S (S (S x1))), 1%nat.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      left. exists []...
      LLright. solveLL. 
      apply seqNtoSeq in H5...
      LLfocus1. 
      lia. intros.
  LLPerm ([⌈ t_bcon OR Fo1 Go1 ⌉] ++ Delta1++[]).
      eapply InvTensorT'. exact H. solveLL.
      simpl... solveLL.
      eapply InvPlusComm... solveLL. LLExact H1.       

    - apply FocusingPlusPos in H4...
      exists [!⌈ Fo1 ⌉], (S (S (S x0))), 1%nat.
      split... do 2 constructor... 
      inversion H0...  inversion H...
      right... 
      LLleft. solveLL. 
      apply seqNtoSeq in H5...
      LLfocus1.
      lia. intros.
      simpl;solveLL...  
      eapply InvPlus... solveLL. LLExact H.        
      
      exists [!⌈ Go1 ⌉], (S (S (S x0))), 1%nat.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      right... 
      LLright. solveLL. 
      apply seqNtoSeq in H5...
       LLfocus1.
      lia. intros.
      simpl... solveLL.
      eapply InvPlusComm... solveLL. LLExact H.       

  + exists Requirement1.BOneP.
     do 3 intro. intros. 
     apply FocusingClause in H...
    - apply FocusingPlus in H4...
      exists [⌊ Fo1 ⌋], x1, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      left. exists x0...
      LLleft. solveLL. 
      apply seqNtoSeq in H2...
      LLExact H2.
      lia. intros.
      LLtheory (makeLRuleB AND Fo1 Go1).
       
      LLtensor [⌊ t_bcon AND Fo1 Go1 ⌋] Delta1. 
      LLleft. solveLL. LLExact H1.
      exists [⌊ Go1 ⌋], x1, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      left. exists x0...
      LLright. solveLL. 
      apply seqNtoSeq in H2...
      LLExact H2.
      lia. intros.
      LLtheory (makeLRuleB AND Fo1 Go1).
       
      LLtensor [⌊ t_bcon AND Fo1 Go1 ⌋] Delta1. 
      LLright. solveLL. LLExact H1.
    - apply FocusingPlus in H4...
      exists [⌊ Fo1 ⌋], x0, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H...
      right... 
      LLleft. solveLL. 
      apply seqNtoSeq in H2...
      LLExact H2.
      lia. intros. simpl. solveLL.
     apply InvPlus... solveLL.
     LLExact H.
      exists [⌊ Go1 ⌋], x0, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      right...
 simpl. 
      LLright. solveLL. 
      apply seqNtoSeq in H2...
      LLExact H2.
      lia. intros.
 simpl. solveLL.
     apply InvPlusComm... solveLL.
     LLExact H.
 + exists Requirement1.BTwoPA.
     do 3 intro. intros. 
     apply FocusingClause in H...
    - apply FocusingWithPos in H4...
      exists x0, [!⌈ Fo1 ⌉],  [!⌈ Go1 ⌉], x1, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      do 2 constructor... 
      inversion H0...  inversion H... 
      left. split... simpl. solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
(*       apply BangConN in H2... *)
      LLExact H2.
(*       apply BangConN in H5... *)
      LLExact H5. 
      lia. intros.
      LLtheory (makeRRuleB AND Fo1 Go1).
       
      LLtensor [⌈ t_bcon AND Fo1 Go1 ⌉ ] Delta12.
     simpl. solveLL. LLExact H1. LLExact H4.  
    - apply FocusingWithPos in H4...
      exists Delta, [!⌈ Fo1 ⌉],  [!⌈ Go1 ⌉], x0, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      do 2 constructor... 
      inversion H0...  inversion H... 
      right. split... simpl. solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
(*      apply BangConN in H2... *)
      LLExact H2.
(*       apply BangConN in H5... *)
      LLExact H5.
      lia. intros.
     simpl; solveLL. LLExact H. LLExact H1.
 + exists Requirement1.BTwoPM.
     do 3 intro. intros. 
     apply FocusingClause in H...
    - apply FocusingTensorPos in H4...
      exists  x0, [⌈ Fo1 ⌉],  [⌊ Go1 ⌋], x1, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      do 2 constructor... 
      inversion H0...  inversion H... 
      left. split... simpl. 
      LLtensor (@nil oo) x0; solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
      LLExact H5.
      lia. intros.
      LLtheory (makeLRuleB IMP Fo1 Go1).
       
      LLtensor [⌊ t_bcon IMP Fo1 Go1 ⌋ ] (Delta0). 
      simpl. LLtensor (@nil oo) (Delta0); solveLL.  LLExact H4.
    - apply FocusingTensorPos in H4...
      exists Delta, [⌈ Fo1 ⌉],  [⌊ Go1 ⌋], x0, 4.
      split... do 2 constructor... 
      inversion H0...  inversion H... 
      do 2 constructor... 
      inversion H0...  inversion H... 
      right. split... simpl. solveLL.
      LLtensor (@nil oo) Delta; solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
      LLExact H5.
      lia. intros.
      simpl; solveLL. 
     LLPerm ((! ⌈ Fo1 ⌉) ⊗ ⌊ Go1 ⌋ :: []++Delta0).
     apply InvTensor';solveLL... LLfocus1.   LLExact H1.
  + exists Requirement1.BOneP.
     do 3 intro. intros. 
     apply FocusingClause in H...
    - apply FocusingParPos in H4...
      exists [!⌈ Go1 ⌉ ; ⌊ Fo1 ⌋], x1, 5.
      split... constructor... constructor... 
      inversion H0...  inversion H...
      constructor... constructor... 
      inversion H0...  inversion H...

      left. exists x0...
      simpl.  solveLL. 
      apply seqNtoSeq in H1...
      LLExact H1.
      lia. intros.
      LLtheory (makeRRuleB IMP Fo1 Go1).
       
      LLtensor [⌈ t_bcon IMP Fo1 Go1 ⌉] Delta1. 
      simpl. solveLL.  LLExact H2. 
    - apply FocusingParPos in H4...
      exists [!⌈ Go1 ⌉ ; ⌊ Fo1 ⌋], x0, 5.
      split... constructor... constructor... 
      inversion H0...  inversion H...
      constructor... constructor... 
      inversion H0...  inversion H...

      right... 
      simpl.  solveLL. 
      apply seqNtoSeq in H1...
      LLExact H1.
      lia. intros.
      simpl; solveLL. LLExact H.
Qed.

Lemma wellBipoleLJQ : wellFormedQ'.
Proof with sauto. 
  unfold wellFormedQ';intros.
  destruct lab.
Qed.

Lemma wellFormedLJ : wellFormedTheory'.
Proof.
  split.
  apply wellBipoleLJC.
  split.  
 apply wellBipoleLJU.
  split. 
apply wellBipoleLJB. 
 apply wellBipoleLJQ.
Qed.

Lemma checkEncodeCasesD'
     : forall (L : list uexp) (x : list oo) (F G : uexp),
  Permutation (atom (up G) :: ⌞ L ⌟ ) (⌊ F ⌋ :: x) ->
       exists x1 : list uexp,
         Permutation (⌞ L ⌟) (⌊ F ⌋ :: ⌞ x1 ⌟) /\
         Permutation (atom (up G) :: ⌞ x1 ⌟ ) x.
Proof with sauto.
   intros.
   assert(Permutation (⌈ G ⌉ :: ⌞ L ⌟) ( LEncode L ++ REncode [G]))...
   rewrite H0 in H.
   apply checkEncodeCasesD in H...
   exists x0... rewrite <- H2...
Qed.

Lemma wellBipoleLJCI : wellFormedCI.
Proof with sauto.
  unfold wellFormedCI;intros.
  destruct lab.
 * exists Requirement1.BCFail.  
    do 2 intro.
    apply FocusingClause in H...
   - inversion H3... 
     solvePolarity.
   - inversion H3... 
     solvePolarity.
 * exists Requirement1.BCAxiom.  
    do 3 intro.
    apply FocusingClause in H...
   - left. apply checkEncodeCasesD' in H3...  
     exists x1... simpl. solveLL.
     intros.
      LLtheory ((makeLRuleC FF )).
     LLtensor [⌊ t_ccon FF ⌋] Delta1.
    simpl. solveLL.
   - right. split... simpl. solveLL.
     intros.
      LLtheory ((makeLRuleC FF )).
     LLtensor (@nil oo) Delta1.
    simpl. solveLL.
Qed.

Lemma wellBipoleLJUI : wellFormedUI.
Proof with sauto. 
  unfold wellFormedUI;intros.
  destruct lab.
Qed.

Lemma wellBipoleLJQI : wellFormedQI.
Proof with sauto.
  unfold wellFormedQI. intros.
  destruct lab.
Qed.



 Lemma wellBipoleLJBI : wellFormedBI.
Proof with sauto.
  unfold wellFormedBI;intros.
  destruct lab.
 + exists Requirement1.BTwoPA.
     do 3 intro. intros. 
     apply FocusingClause in H...
    - apply FocusingWith in H4...
     apply checkEncodeCasesD' in H3... 
      exists x, [ Fo1 ],  [ Go1 ], x1, 4.
      split...  constructor... 
      inversion H0...  inversion H3... 
      constructor... 
      inversion H0...  inversion H3... 
      left. split... rewrite H1... simpl. solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5... 
      LLExact H2.  rewrite <- H1... rewrite LEncodeApp...
      LLExact H5.  rewrite <- H1... rewrite LEncodeApp...
      lia. intros.
      LLtheory (makeLRuleB OR Fo1 Go1).
       
      LLtensor [⌊ t_bcon OR Fo1 Go1 ⌋ ]  Delta12.
      simpl. solveLL. LLExact H4. LLExact H6.
    - apply FocusingWith in H4...
      exists Delta, [ Fo1 ],  [ Go1], x0, 4.
      split... constructor... 
      inversion H0...  inversion H... 
      constructor... 
      inversion H0...  inversion H... 
      right. split... simpl. solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
      LLExact H2. simpl... 
      LLExact H5. simpl...
      lia. intros.
    (*   LLtheory (makeLRuleBin OR Fo1 Go1).
       
   LLtensor (@nil oo) (⌈ F ⌉ :: ⌞ Delta12 ⌟).       *) 
      simpl. solveLL. 
      LLExact H. LLExact H1.
  + exists Requirement1.BOneP.
     do 3 intro. intros. 
     apply FocusingClause in H...
    - apply FocusingPlus in H4...
       apply checkEncodeCasesD' in H3...  
       exists   [Fo1 ], x1, 4.
      split...
     constructor... 
      inversion H0...  inversion H3...  
     left. exists x. split... 
      rewrite H1...
      LLleft. solveLL. 
      apply seqNtoSeq in H2...
      LLExact H2. rewrite <- H1 ... rewrite LEncodeApp...
      lia. intros.
      LLtheory (makeLRuleB AND Fo1 Go1).
       
      LLtensor [⌊ t_bcon AND Fo1 Go1 ⌋ ] Delta1.
      LLleft. solveLL. LLExact H4. 

       apply checkEncodeCasesD' in H3...  
       exists  [Go1 ], x1, 4.
      split...
     constructor... 
      inversion H0...  inversion H3...  
     left. exists x. split... 
      rewrite H1...
      LLright. solveLL. 
      apply seqNtoSeq in H2...
      LLExact H2.   rewrite <- H1 ... rewrite LEncodeApp...
      lia. intros.
      LLtheory (makeLRuleB AND Fo1 Go1).
       
      LLtensor [⌊ t_bcon AND Fo1 Go1 ⌋ ] Delta1.
      LLright. solveLL. LLExact H4. 
     - apply FocusingPlus in H4...
       exists  [Fo1 ], x0, 4.
      split...
     constructor... 
      inversion H0...  inversion H...  
     right. split... 
      LLleft. solveLL. 
      apply seqNtoSeq in H2...
      LLExact H2. 
      lia. intros.
  LLleft. solveLL. LLExact H. 
exists  [Go1 ], x0, 4.
      split...
     constructor... 
      inversion H0...  inversion H...  
     right. split... 
      LLright. solveLL. 
      apply seqNtoSeq in H2...
      LLExact H2. 
      lia. intros.
  LLright. solveLL. LLExact H.
 + exists Requirement1.BTwoPM.
     do 3 intro. intros. 
     apply FocusingClause in H...
    - apply FocusingTensorPos in H4...
       apply checkEncodeCasesD' in H3...  
       exists x. exists [Go1], [⌈ Fo1 ⌉], x1, 4.
      split... 1-2: constructor...  inversion H0... inversion H3... 
 constructor...  inversion H0... inversion H3...
      left. split... simpl. 
      LLtensor (@nil oo)  (⌞ x ⌟ ++ [⌈ F ⌉]) ; solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
      LLExact H5.   rewrite <- H1...
LLExact H5.   rewrite <- H1... rewrite LEncodeApp...
      lia. intros. 
      LLPerm ([⌊ t_bcon IMP Fo1 Go1 ⌋] ++ (Delta0)).
     eapply InvTensorT'. exact H3. solveLL.  simpl.  solveLL. 
      LLPerm ((! ⌈ Fo1 ⌉) ⊗ ⌊ Go1 ⌋ :: [ ] ++  Delta0).
       eapply InvTensor';solveLL. LLfocus1. 
 LLExact H4. 
    - apply FocusingTensorPos in H4...
     exists Delta, [Go1 ]. exists [⌈ Fo1 ⌉], x0, 4.
    split...  
    1-2: constructor...
    inversion H0...
    inversion H...
constructor...
    inversion H0...
    inversion H...
right.
      split... 
      LLtensor (@nil oo)  (⌞Delta⌟ ++ [⌈ F ⌉]) ; solveLL. 
      apply seqNtoSeq in H2...
      apply seqNtoSeq in H5...
      LLExact H5. LLExact H5. rewrite LEncodeApp... 
      lia. intros. simpl;solveLL.
        LLtensor (@nil oo)  Delta0; solveLL. 
 LLExact H. 
Qed.

Lemma wellFormedI : wellFormedTheoryI.
Proof.
  split.
  apply wellBipoleLJCI.
  split.  
 apply wellBipoleLJUI. 
  split. 
apply wellBipoleLJBI. 
 apply wellBipoleLJQI.
Qed.

(** ** Cut-coherency properties *)

(** *** Binary Connectives *)
Lemma CutCoherenceOR: CutCoherenceB cutR2 (rulesB OR).
Proof with sauto; try solveLL.
  unfold CutCoherenceB;intros.
  simpl...
  apply InvPlus...
  apply InvPlusComm...
Qed.


Lemma CutCoherenceAND: CutCoherenceB cutR2 (rulesB AND).
Proof with sauto; try solveLL.
  unfold CutCoherenceB;intros.
  simpl...
  LLPerm  [(? ⌈ F ⌉^) ⊕ (? ⌈ G ⌉^); ⌊ F ⌋^].
  apply InvPlus...
  LLPerm  [(? ⌈ F ⌉^) ⊕ (? ⌈ G ⌉^); ⌊ G ⌋^].
  apply InvPlusComm...
Qed.

Lemma CutCoherenceIMP: CutCoherenceB cutR2 (rulesB IMP).
Proof with sauto; try solveLL.
  unfold CutCoherenceB;intros.
  simpl...
  LLPerm  ((⌊ F ⌋^ ⊗ (? ⌈ G ⌉^)):: ([]++[⌊G ⌋^])).
  apply InvTensor'...
  simpl...
  apply weakening...
Qed.
 
Lemma CutCoherenceLJ : CutCoherence cutR2.
Proof.
 split;intros. 
  destruct lab...
  split;intros; try destruct lab.
  simpl. auto. simpl. solveLL. 
  split;intros; try destruct lab.
  simpl. auto. simpl. solveLL. 
  split;intros; try destruct lab.
  split;intros; try destruct lab.
  apply CutCoherenceOR.
   apply CutCoherenceAND.
  apply CutCoherenceIMP.
Qed.

Check OLCutElimination  wellFormedLJ CutCoherenceLJ wellFormedI . 
