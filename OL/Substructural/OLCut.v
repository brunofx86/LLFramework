
(** * LL as a Meta-logical framework.  *)

(** In this file we show how the cut-elimination procedure for FLL can
be used to prove cut-elimination for object logics that are
cut-coherent in the sense of Miller & Pimentel. Roughly, a system is
cut-coherent if the encoding of the right and left rules of each
connective are dual. *)

Require Export LL.Misc.Hybrid.
Require Export LL.OL.Definitions.
Require Import Coq.Init.Nat.
Require Import LL.SL.FLL.CutElimination.
Import LL.Misc.Permutations.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Cut Elimination Procedure *)
Section CutElimination .
  Context `{OLR: OORules}.

  (** As a general hypothesis, we assume that the Object logic is cut-coherent *)
  Hypothesis LTWell : wellTheory.
  
  (** Extracting the needed facts given that all the OL constants are well-defined *)
Ltac wellConstant HSeq :=
    let HS := type of HSeq in
    match HS with
    | seqN ?Rules ?n ?Gamma ?M (DW (?Side ?C)) =>
      let Side' :=
          match Side with 
          makeRRuleConstant => Right
           | makeLRuleConstant => Left end in
      
      match goal with
        [  LTWell:wellTheory |- _ ] =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize ((proj1 (proj2 LTWell)) Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ];
          destruct bpEnum;[ apply LTWell' in HSeq; contradiction (* fail case *)
                          | generalize (LTWell' _ HSeq);intro;CleanContext (* axiom *)
                          | generalize (LTWell' _ HSeq);intro;CleanContext] (* one premise *)
      end
    end.
 
  (** Extracting well-formed conditions for binary predicates *)
  Ltac wellFormedBin HSeq :=
    let HS := type of HSeq in
    match HS with
    | (seqN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F ?G))) =>
      let Side' :=
          match Side with makeRRuleBin => Right | makeLRuleBin => Left end in
      match goal with
        [  LTWell:wellTheory |- _ ] =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize ((proj1 (proj2 (proj2 (proj2 LTWell)))) Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ]; destruct bpEnum;generalize (LTWell' _ _ _ HSeq);intro;CleanContext
      end
    end.

   Ltac wellFormedU HSeq  :=
    let HS := type of HSeq in
    match HS with
    | (seqN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with 
          makeRRuleUnary => Right 
          | makeLRuleUnary => Left end in
      match goal with
        [  LTWell:wellTheory |- _ ] => 
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize ((proj1 (proj2 (proj2 LTWell))) Rules Gamma M C Side' );intro LTWell';generalize (LTWell' _ _ HSeq);intro;CleanContext
      end
    end.
     
  Ltac wellFormedQ HSeq :=
    let HS := type of HSeq in
    match HS with
    | (seqN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with makeRRuleQ => Right | makeLRuleQ => Left end in
      
      match goal with
        [  LTWell:wellTheory |- _ ] =>
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
         let HUniform := fresh "HUniform" in
        generalize ((proj2 (proj2 (proj2 (proj2 LTWell)))) Rules Gamma M C Side' F); intro LTWell';destruct LTWell' as [HUniform LTWell'];generalize (LTWell'  _ HSeq); intro;CleanContext; clear LTWell'
      end
    end.
  

 (** This is the case when a constant is principal in both premises *)
  Theorem ConstantPrincipalCase :
    forall Gamma M N C,
      (seq (OLTheory nPnN) Gamma M (DW (rc_leftBody (rulesCte C)))) ->
      (seq (OLTheory nPnN) Gamma N (DW (rc_rightBody (rulesCte C)))) ->
      seq (OLTheory nPnN) Gamma (N ++ M) (UP []).
 Proof with sauto.     
    intros.
    apply seqtoSeqN in H... 
    apply seqtoSeqN in H0...
    generalize( (proj1 (proj1 LTWell)) C);intro CutC.
    unfold CutCoherenceCte in CutC.
    destruct CutC as [Hc CutC].
    apply EmptySubSet with (theory:= (OLTheory nPnN) ) in CutC.
    apply weakeningGen with (CC':= Gamma) in CutC .
    apply seqtoSeqN in CutC.   destruct CutC as [h CutC].
    rewrite app_nil_r in CutC.
    assert(HCut1: seq (OLTheory nPnN) Gamma ([] ++ N)  ( UP [ (rc_leftBody (rulesCte C)) ^])).
    eapply @GeneralCut with  (C:=  rc_rightBody (rulesCte C) ^);eauto. 
    rewrite <- ng_involutive;eauto.
    
    
    apply seqtoSeqN in HCut1.  destruct HCut1 as [h2 HCut1].
    eapply @GeneralCut with  (C:= (rc_leftBody (rulesCte C)) ^); eauto. 
    rewrite <- ng_involutive;eauto.
  Qed.

  (** This is the case when a unary connective is principal in both premises *)
  Theorem UConnectivePrincipalCase :
    forall Gamma M N C F n n',
      (seq (OLTheory nPnN) Gamma M (DW (ru_leftBody (rulesUnary C) F))) ->
      (seq (OLTheory nPnN) Gamma N (DW (ru_rightBody (rulesUnary C) F))) ->
      (lengthUexp (t_ucon C F) n') ->
      isOLFormula (t_ucon C F) ->
      n' <= n ->
      seq (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply seqtoSeqN in H.     
    apply seqtoSeqN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize( (proj1 (proj2 ((proj1 LTWell)))) C);intro CutC.
    unfold CutCoherenceUnary in CutC.
    
    generalize (CutC F n1);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply seqtoSeqN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
    assert(Cut1': seq (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[(ru_leftBody (rulesUnary C) F) ^] )).
    eapply @GeneralCut with(C := (ru_rightBody (rulesUnary C) F)  ^) ;eauto.
    
    rewrite <- ng_involutive;eauto.

    apply seqtoSeqN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:= (ru_leftBody (rulesUnary C) F) ^); eauto.
    rewrite <- ng_involutive;eauto.
  Qed.
  
  (** This is the case when a binary connective is principal in both premises *)
  Theorem BinConnectivePrincipalCase :
    forall Gamma M N C F G n n',
      (seq (OLTheory nPnN) Gamma M (DW (rb_leftBody (rulesBin C) F G))) ->
      (seq (OLTheory nPnN) Gamma N (DW (rb_rightBody (rulesBin C) F G))) ->
      lengthUexp (t_bin C F G) n' ->
      isOLFormula (t_bin C F G) ->
      n' <= n ->
      seq (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply seqtoSeqN in H.     apply seqtoSeqN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize ((proj1 (proj2 (proj2 (proj1 LTWell)))) C);intro CutC.
    unfold CutCoherenceBin in CutC.
    
    generalize (CutC F G n1 n2);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply seqtoSeqN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
    
    assert(Cut1': seq (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[ (rb_leftBody (rulesBin C) F G) ^] )).
    eapply @GeneralCut with (C := (rb_rightBody (rulesBin C) F G) ^) ;eauto.
    rewrite <- ng_involutive;eauto.
 
    apply seqtoSeqN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:= (rb_leftBody (rulesBin C) F G) ^); eauto.     rewrite <- ng_involutive;eauto.
  Qed.

  (** This is the case when a quantifier is principal in both premises *)
  Theorem QuantifierPrincipalCase :
    forall Gamma M N C FX FX0 n n',
      (seq (OLTheory nPnN) Gamma M (DW (rq_leftBody (rulesQ C) FX0))) ->
      (seq (OLTheory nPnN) Gamma N (DW (rq_rightBody (rulesQ C) FX))) ->
      isOLFormula (t_quant C FX) ->
      isOLFormula (t_quant C FX0) ->
      lengthUexp (t_quant C FX) n' ->
      uniform FX -> uniform FX0 ->
      lbind 0%nat FX0 = lbind 0%nat FX ->
      n' <= n ->
      seq (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1. inversion H8.
    inversion H2. inversion H12.
    subst.
    assert (ext_eq FX FX0).
    eapply lbindEq;eauto.
    assert (ext_eq FX FX1). eapply lbindEq;eauto.
    assert (ext_eq FX FX2). eapply lbindEq;eauto.  rewrite <- H6. auto.
    inversion H3...
    destruct n ;[ lia | simpl].
    assert (ext_eq FX M0). eapply lbindEq;eauto.
    generalize ( ( proj2 ( proj2 ( proj2 (proj1 LTWell)))) C) ;intro CutC.
    assert (Hsize: lengthUexp (FX (Var 0%nat)) n0).
    { rewrite H17...  apply proper_VAR.  }
    assert(HIs: (forall t : expr Econ, proper t -> isOLFormula (FX t))).
    {intros t pt. rewrite H12... }
    unfold CutCoherenceQ in *.
    generalize (CutC FX FX0 n0); intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply WeakTheory with (theory' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb1.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (theory' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheory with (theory' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
   
    apply seqtoSeqN in H.  apply seqtoSeqN in H0. apply seqtoSeqN in Cut1.
    destruct H as [h1 H]. 
    destruct H0 as [h2 H0]. destruct Cut1 as [h3 Cut1].
    

    assert(Cut1': seq (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[(rq_leftBody (rulesQ C) FX0) ^] )).
    eapply @GeneralCut with  (C := (rq_rightBody (rulesQ C) FX) ^) ;eauto.
    rewrite <- ng_involutive;eauto.
    simpl in Cut1'.
    apply seqtoSeqN in Cut1'.
    destruct Cut1' as [h4 Cut1']. 

    
    eapply @GeneralCut with (C := (rq_leftBody (rulesQ C) FX0) ^) ;eauto.
    rewrite <- ng_involutive;eauto.
  Qed.

 (** Inductive hypothesis in the theorem [OLCutElimStep]. This is
  useful to simplify the theorems below *)
  Definition OOCut n' h : Prop :=
    forall n h1 h2 FCut M N Gamma,
      h1 + h2 < h ->
          n' <= n ->
            isOLFormula FCut ->
            lengthUexp FCut n' ->
              IsPositiveAtomFormulaL M ->
                IsPositiveAtomFormulaL N ->
                  IsPositiveAtomFormulaL Gamma ->
                  seqN (OLTheory nPnN) h1 Gamma (atom (up FCut)::N) (UP [] ) ->
                  seqN (OLTheory nPnN) h2 Gamma (atom (down FCut)::M) (UP []) -> seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
                  
 Ltac applyOOCut := 
  match goal with
  | [ H: OOCut _ _ |- 
         seqN ?th ?x ?BX (?FF::?N) (UP []) -> 
         seqN ?th ?y ?BX (?GG::?M) (UP [])-> 
         seq ?thc ?BX (?M++?N) (UP []) ] => eapply H
  | _ => idtac end.
  
Ltac cutOL P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | seqN ?th ?h1 ?B (atom (up ?FC) :: ?N) (UP []) => 
          match tP2 with 
          | seqN ?th ?h2 ?B (atom (down ?FC) :: ?M) (UP []) =>  
           match goal with
           | [ H: OOCut ?n' _, Hn: ?n' <= ?n  |- _ ] =>    assert(H': tP1 -> tP2 -> seq (OLTheoryCut nPnN (pred n)) B (M++N) (UP []));applyOOCut
           end
           | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto.
   
Ltac SubCases :=
repeat 
match goal with
  | H: Permutation (_::_) (_::_) |- _ => checkPermutationCases H
  | H: Permutation (_ ++ _) (_ :: _) |- _ => checkPermutationCases H
  | H: Permutation (_ :: _) (_ ++ _) |- _ => checkPermutationCases H
  | H:  (⌈ ?F ⌉) =  (⌈ ?G ⌉) |- _ => inversion H;sauto
  | H:  (⌊ ?F ⌋) =  (⌊ ?G ⌋) |- _ => inversion H;sauto      
end.
      
Ltac Cases H := destruct H;sauto;SubCases;
repeat
match goal with
| H: Permutation ?M (_::_) |- context[?M] => rewrite H
| H: Permutation (_++_) ?M  |- context[?M] => rewrite <- H
end
.
 
Ltac PermuteLeft :=    
  match goal with 
     |[ Hr: seqN _ ?x (?G ++ ?Y1) (?X ++ _) (UP []),   
        Hr': seqN _ ?x (?G ++ ?Y2) (?X ++ _) (UP []),             
       Hl: seqN ?th ?n ?G ( (⌈ ?F ⌉) :: ?N) (UP []),
       Hp: Permutation ?X ((⌊ ?F ⌋) :: _) |- _] =>
   assert(Hl': seqN th n G ( (⌈ F ⌉) :: N) (UP [])) by auto; 
   apply weakeningGenN_rev with (CC':= Y1) in Hl;
   apply weakeningGenN_rev with (CC':= Y2) in Hl';
   rewrite Hp in Hr, Hr';
    rewrite <- app_comm_cons in Hr, Hr'
   |[ Hr: seqN _ ?x (?G ++ ?Y1) (?X ++ _) (UP []),   
        Hr': seqN _ ?x (?G ++ ?Y2) (?X ++ _) (UP []),             
       Hl: seqN ?th ?n ?G ( (⌈ ?F ⌉) :: ?N) (UP []),
       Hp: Permutation ( (⌊ ?F ⌋) :: _) ?X |- _] =>
   assert(Hl': seqN th n G ( (⌈ F ⌉) :: N) (UP [])) by auto; 
   apply weakeningGenN_rev with (CC':= Y1) in Hl;
   apply weakeningGenN_rev with (CC':= Y2) in Hl';
   rewrite <- Hp in Hr, Hr';
    rewrite <- app_comm_cons in Hr, Hr'    
   |[ Hr: seqN _ ?x (?G ++ ?Y) (?X ++ _) (UP []),               
       Hl: seqN _ ?n ?G ( (⌈ ?F ⌉) :: ?N) (UP []),
       Hp: Permutation ?X ((⌊ ?F ⌋) :: _) |- _] =>
       apply weakeningGenN_rev with (CC':= Y) in Hl;
       rewrite Hp in Hr;
       rewrite <- app_comm_cons in Hr
   |[ Hr: seqN _ ?x (?G ++ ?Y) (?X ++ _) (UP []),               
       Hl: seqN _ ?n ?G ( (⌈ ?F ⌉) :: ?N) (UP []) |- _] =>
       apply weakeningGenN_rev with (CC':= Y) in Hl;
       rewrite <- app_comm_cons in Hr       

       end.
       
(** Unary Right is not principal on the left branch *)    
Lemma UnaryRightNotPrincipalL n n' n0 n1 C FCut F Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_ucon C F) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeRRuleUnary C F) ->
seqN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
seqN (OLTheory nPnN) n1 Gamma ((⌊ FCut ⌋) :: M)
     (DW (makeRRuleUnary C F)) ->
seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellFormedU H9.
  * Cases H10.
     - PermuteLeft.
        cutOL H8 H14.
        1-2: OLSolve.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     -  PermuteLeft.
        cutOL H8 H15.
        1-2: OLSolve.
        TFocus (makeRRuleUnary C F).
        inversion H10.
        FLLsplit (@nil oo) (M++N).
        apply H19...
        rewrite Permutation_assoc_comm... 
Qed.

(** Unary Left is not principal on the left branch *) 
Lemma UnaryLeftNotPrincipalL n n' n0 n1 C FCut F Gamma M N: 
FCut <> t_ucon C F ->
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_ucon C F) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeLRuleUnary C F) ->
seqN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
seqN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeLRuleUnary C F)) ->
seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellFormedU H10.
  * Cases H11.
     - PermuteLeft. 
        cutOL H9 H15.
        1-2: OLSolve.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H20...
        rewrite Permutation_assoc_comm...
     - PermuteLeft. 
        cutOL H9 H16.
        1-2: OLSolve.
        TFocus (makeLRuleUnary C F).
        inversion H11.
        FLLsplit (@nil oo) (M++N).
        apply H20...
        rewrite Permutation_assoc_comm...  
Qed.        

(** Binary Right is not principal on the left branch *) 
Lemma BinaryRightNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bin C F G) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeRRuleBin C F G) ->
seqN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
seqN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeRRuleBin C F G)) ->
seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellFormedBin H9.
  * Cases H10.
     - PermuteLeft. 
        cutOL H8 H14.
        1-2: OLSolve.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - PermuteLeft. 
        cutOL H8 H15.
        1-2: OLSolve.
        TFocus (makeRRuleBin C F G).
        inversion H10.
        FLLsplit (@nil oo) (M++N). 
        apply H19...
        rewrite Permutation_assoc_comm...
  * Cases H10.
     - PermuteLeft.
       cutOL H8 H17.
       1-2: OLSolve.
       rewrite <- H21 in H20.
       rewrite H20 in H4.
       inversion H4...
       OLSolve.
       rewrite <- app_comm_cons.
        rewrite Permutation_assoc_comm...
        apply H22...
        rewrite Permutation_assoc_comm...
        apply seqNtoSeq in H18...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H18;auto using TheoryEmb1.
    -  PermuteLeft.
        cutOL H8 H18.
        1-2: OLSolve.
       rewrite <- H21 in H20.
       rewrite H20 in H4.
       inversion H4...
       OLSolve.
          rewrite <- app_comm_cons.
        rewrite app_assoc_reverse. 
        apply H22...
        apply seqNtoSeq in H17...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.
        rewrite Permutation_assoc_comm...
    -  PermuteLeft.  
        cutOL H8 H18.
        1-2: OLSolve.
       rewrite <- H21 in H4.
       OLSolve.
        
        rewrite app_assoc_reverse.
        TFocus (makeRRuleBin C F G).
        inversion H10.
        FLLsplit (@nil oo) ((x7 ++ N )++ x0). 
        apply H23...
         rewrite Permutation_assoc_comm...
    apply seqNtoSeq in H19...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H19;auto using TheoryEmb1.
     -  PermuteLeft.  
        cutOL H8 H19.
        1-2: OLSolve.
       rewrite <- H21 in H4.
       OLSolve.
        TFocus (makeRRuleBin C F G).
        inversion H10.
        FLLsplit (@nil oo) (x++(x7 ++ N )). 
        apply H23...
          apply seqNtoSeq in H18...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H18;auto using TheoryEmb1.       
        
         rewrite Permutation_assoc_comm...
* Cases H10.
     - PermuteLeft.
       cutOL H8 H17.
       1-2: OLSolve.
       rewrite H20 in H4.
        OLSolve.
        cutOL Hl' H18.
       1-2: OLSolve.
       rewrite H20 in H4.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H22...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
      - PermuteLeft.
        cutOL H8 H18.
        1-2: OLSolve.
        cutOL Hl' H19.
        1-2: OLSolve.
        TFocus (makeRRuleBin C F G).
        inversion H10.
        FLLsplit (@nil oo) (M ++ N). 
        apply H23...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
Qed.    

(** Unary Left is not principal on the left branch *)  
Lemma BinaryLeftNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
FCut <> t_bin C F G ->
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bin C F G) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeLRuleBin C F G) ->
seqN (OLTheory nPnN) (S n0) Gamma ((⌈ FCut ⌉) :: N) (UP []) ->
seqN (OLTheory nPnN) n1 Gamma ((⌊ FCut ⌋) :: M)
     (DW (makeLRuleBin C F G)) ->
seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellFormedBin H10.
  * Cases H11.
     - PermuteLeft.  
        cutOL H9 H15.
        1-2: OLSolve.
        rewrite H18 in H5.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H20...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H9 H16.
        1-2: OLSolve.
        TFocus (makeLRuleBin C F G).
        inversion H11.
        FLLsplit (@nil oo) (M++N).
        apply H20...
        rewrite Permutation_assoc_comm...
  * Cases H11.
     - PermuteLeft.  
        cutOL H9 H18.
        1-2: OLSolve.
        rewrite <- H22 in H21.
        rewrite H21 in H5.
        inversion H5...
        OLSolve.
        rewrite <- app_comm_cons.
        rewrite Permutation_assoc_comm...
        apply H23...
        rewrite Permutation_assoc_comm...
        apply seqNtoSeq in H19...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H19;auto using TheoryEmb1.
     - PermuteLeft. 
        cutOL H9 H19.
        1-2: OLSolve.
        rewrite <- H22 in H21.
        rewrite H21 in H5.
        inversion H5...
        OLSolve.
        rewrite <- app_comm_cons.
        rewrite app_assoc_reverse. 
        apply H23...
        apply seqNtoSeq in H18...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H18;auto using TheoryEmb1.
        rewrite Permutation_assoc_comm...
     - PermuteLeft.
       cutOL H9 H19.
       1-2: OLSolve.
       rewrite <- H22 in H5.
       OLSolve.
       rewrite Permutation_assoc_comm...
       TFocus  (makeLRuleBin C F G).
       inversion H11.
       FLLsplit (@nil oo) ((x7 ++ N) ++ x0).
       apply H24...
       rewrite Permutation_assoc_comm...
       apply seqNtoSeq in H20...
       apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H20;auto using TheoryEmb1.
     - PermuteLeft.  
        cutOL H9 H20.
        1-2: OLSolve.
        rewrite <- H22 in H5.
        OLSolve.
        rewrite app_assoc_reverse.
         TFocus  (makeLRuleBin C F G).
       inversion H11.
       FLLsplit (@nil oo) (x++(x7 ++ N)).
        apply H24...
        apply seqNtoSeq in H19...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H19;auto using TheoryEmb1.
         rewrite Permutation_assoc_comm...
  * Cases H11.
     - PermuteLeft.  
        cutOL H9 H18.
        1-2: OLSolve.
        rewrite H21 in H5.
        OLSolve.
        cutOL Hl' H19.
        1-2: OLSolve.
        rewrite H21 in H5.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H23...
        1-2: rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H9 H19.
        1-2: OLSolve.
        cutOL Hl' H20.
        1-2: OLSolve.
         TFocus  (makeLRuleBin C F G).
       inversion H11.
       FLLsplit (@nil oo) (M++N).      
        apply H24...
        1-2: rewrite Permutation_assoc_comm... 
 Qed.     

 (** Quantifier Right is not principal on the left branch *) 
 Lemma QuantifierRightNotPrincipalL n n' n0 n1 C FCut FX Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_quant C FX) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeRRuleQ C FX) ->
seqN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
seqN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeRRuleQ C FX)) ->
seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellFormedQ H9.
  * Cases H10.
     - PermuteLeft.  
        cutOL H8 H14.
        1-2: OLSolve.
        rewrite H17 in H4.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H8 H15.
        1-2: OLSolve.
        TFocus (makeRRuleQ C FX).
        inversion H10.
        FLLsplit (@nil oo) (M++N).
        apply H19...
        rewrite Permutation_assoc_comm...
Qed.

 (** Quantifier Left is not principal on the left branch *) 
 Lemma QuantifierLeftNotPrincipalL n n' n0 n1 C FCut FX Gamma M N: 
 FCut <> t_quant C FX -> 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_quant C FX) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeLRuleQ C FX) ->
seqN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
seqN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeLRuleQ C FX)) ->
seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellFormedQ H10.
  * Cases H11.
     - PermuteLeft.  
        cutOL H9 H15.
        1-2: OLSolve.
        rewrite H18 in H5.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H20...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H9 H16.
        1-2: OLSolve.
        TFocus (makeLRuleQ C FX).
        inversion H11.
        FLLsplit (@nil oo) (M++N).
        apply H20...
        rewrite Permutation_assoc_comm... 
 Qed.       
        
 
Ltac permuteUnary :=
match goal with
| [H: ?n' <= ?n,
   Hl: seqN _ _ _ (_ :: ?N) (UP []) ,
   Hr : seqN _ _ _ (_ :: ?M) (DW (makeRRuleUnary _ _))
  |-  seq _ _ (?M ++ ?N) (UP []) ] =>
   refine (UnaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: seqN _ _ _ (_ :: ?N) (UP []) ,
   Hr : seqN _ _ _ (_ :: ?M) (DW (makeLRuleUnary _ _))
  |-  seq _ _ (?M ++ ?N) (UP []) ] =>
refine (UnaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.     

 
Ltac permuteBinary :=
match goal with
| [H: ?n' <= ?n,
   Hl: seqN _ _ _ (_ :: ?N) (UP []) ,
   Hr : seqN _ _ _ (_ :: ?M) (DW (makeRRuleBin _ _ _))
  |-  seq _ _ (?M ++ ?N) (UP []) ] =>
   refine (BinaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: seqN _ _ _ (_ :: ?N) (UP []) ,
   Hr : seqN _ _ _ (_ :: ?M) (DW (makeLRuleBin _ _ _))
  |-  seq _ _ (?M ++ ?N) (UP []) ] =>
refine (BinaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    
 
 Ltac permuteQuantifier :=
match goal with
| [H: ?n' <= ?n,
   Hl: seqN _ _ _ (_ :: ?N) (UP []) ,
   Hr : seqN _ _ _ (_ :: ?M) (DW (makeRRuleQ _ _))
  |-  seq _ _ (?M ++ ?N) (UP []) ] =>
   refine (QuantifierRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: seqN _ _ _ (_ :: ?N) (UP []) ,
   Hr : seqN _ _ _ (_ :: ?M) (DW (makeLRuleQ _ _))
  |-  seq _ _ (?M ++ ?N) (UP []) ] =>
refine (QuantifierLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    
       
Ltac Cases' H := destruct H;sauto;SubCases.

 Lemma dualRev F G: F = dual G -> G = dual F.
 Proof with sauto.
 intros.
 rewrite H...
 rewrite <- ng_involutive...
 Qed.
 
Lemma ConstantRIGHT n n' n0 n1  C FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_cons C) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
  seqN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ((⌈ FCut ⌉) :: N) (DW (makeRRuleConstant C)) ->
  seqN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleConstant C) ->
  buildTheory F0 ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellConstant Hseq1'.
  * Cases H. 
     2:{ LLPerm ((⌈ t_cons C ⌉) :: x0++M)... }
    rewrite <- H4 in H2.
    clear H4.
    inversion Hth'...
           -- wellConstant Hseq2'.   
               Cases H0.
               rewrite <- app_comm_cons...
               Cases H0. 
               PermuteLeft.
               cutOL Hseq1 H6.
               1-2: OLSolve.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H11...
               LLPerm ((x4 ++ x) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H7.
               1-2: OLSolve.
               TFocus (makeRRuleConstant C0).
               inversion H0.
               FLLsplit (@nil oo) (M++N).
               apply H11...
               LLPerm ( (M ++ x) ++ N)...
           -- wellConstant Hseq2'.   
               Cases H0.
               2:{ rewrite <- app_comm_cons... }
               rewrite <- H7 in H5.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H5 H2).
            
               Cases H0. 
              rewrite <- H10 in H7.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H7 H2).
               PermuteLeft.
               cutOL Hseq1 H6.
               1-2: OLSolve.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H11...
               LLPerm ((x4 ++ x) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H7.
               1-2: OLSolve.
               TFocus (makeLRuleConstant C0).
               inversion H0.
               FLLsplit (@nil oo) (M++N).
               apply H11...
               LLPerm ( (M ++ x) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.
           -- permuteQuantifier.
(** 1.2 ONE PREMISSE *)        
  * Cases H.
     2:{
       rewrite H in H3.
        apply weakeningGenN_rev with (CC':= x0) in Hseq2.
          rewrite <- app_comm_cons in H3.
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ((⌈ t_cons C ⌉) ::(M++ x4))...
         apply H8...
         rewrite app_assoc_reverse... }
     2:{  apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
               rewrite <- app_comm_cons in H4. 
               cutOL H4 Hseq2.
               1-2: OLSolve.
               TFocus (makeRRuleConstant C).
               inversion H.
               FLLsplit (@nil oo) (M++N).
               apply H8...
               rewrite app_assoc_reverse... }

         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H1. 
               rewrite <- app_comm_cons...
           -- Cases H1. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H11.
               1-2: OLSolve.
               OLSolve.
               apply H16...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H12.
               1-2: OLSolve.
               TFocus (makeRRuleConstant C0).
               inversion H1.
               FLLsplit (@nil oo) (M++N).
               apply H16...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H1. 
               rewrite <- H12 in H10.
               rewrite <- H7 in H4.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H10 H4).
               
               rewrite <- app_comm_cons...
           -- Cases H1. 
               rewrite <- H15 in H12.
               rewrite <- H7 in H4.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.
               refine (ConstantPrincipalCase _ H12 H4).
               
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H11.
               1-2: OLSolve.
               OLSolve.
               apply H16...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H12.
               1-2: OLSolve.
               TFocus (makeLRuleConstant C0).
               inversion H1.
               FLLsplit (@nil oo) (M++N).
               apply H16...
               rewrite Permutation_assoc_comm...
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - permuteBinary.
         - permuteQuantifier.
         - permuteQuantifier.
 Qed.        
                       

Lemma UnaryRIGHT n n' n0 n1  C F FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_ucon C F) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n0) Gamma  ( (⌈ FCut ⌉) ::N) (UP []) ->
  seqN (OLTheory nPnN) (S n1)  Gamma ( (⌊ FCut ⌋) ::M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleUnary C F)) ->
  seqN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleUnary C F) ->
  buildTheory F0 ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellFormedU Hseq1'.
  * Cases H.
     2:{ apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
           rewrite H in H3.
         rewrite <- app_comm_cons in H3 . 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ((⌈ t_ucon C F ⌉) ::(M++ x4))...
         apply H8...
         rewrite app_assoc_reverse... }
     2:{  apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
               rewrite <- app_comm_cons in H4. 
               cutOL H4 Hseq2.
               1-2: OLSolve.
               TFocus (makeRRuleUnary C F).
               inversion H.
               FLLsplit (@nil oo) (M++N).
               apply H8...
               rewrite app_assoc_reverse... }
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H1. 
               rewrite <- app_comm_cons...
           -- Cases H1. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H11.
               1-2: OLSolve.
               OLSolve.
               apply H16...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H12.
               1-2: OLSolve.
               TFocus (makeRRuleConstant C0).
               inversion H1.
               FLLsplit (@nil oo) (M++N).
               apply H16...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H1. 
              rewrite <- app_comm_cons...
           -- Cases H1. 
              apply weakeningGenN_rev with (CC':= x5) in Hseq1. 
              rewrite H1 in H11.
              rewrite <- app_comm_cons in H11.
              cutOL Hseq1 H11.
               1-2: OLSolve.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
              
              apply weakeningGenN_rev with (CC':= x5) in Hseq1. 
              rewrite <- app_comm_cons in H12.
              cutOL Hseq1 H12.
               1-2: OLSolve.
                 TFocus (makeLRuleConstant C0).
                 inversion H1.
             FLLsplit (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - wellFormedU Hseq2'.
            Cases H1. 
            
            rewrite <- H7 in H4. 
            rewrite <- H15 in H12. 
            rewrite Permutation_app_comm.
            refine(UConnectivePrincipalCase _ H4 _ _ HL')...
                          apply weakeningGenN_rev with (CC':= x5) in Hseq1. 
              rewrite H1 in H11.
              rewrite <- app_comm_cons in H11.
              cutOL Hseq1 H11.
               1-2: OLSolve.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
              
              apply weakeningGenN_rev with (CC':= x5) in Hseq1. 
              rewrite <- app_comm_cons in H12.
              cutOL Hseq1 H12.
               1-2: OLSolve.
                 TFocus (makeLRuleUnary C0 F1).
                 inversion H1.
             FLLsplit (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... 
         - permuteBinary.
         - permuteBinary.
         - permuteQuantifier.
         - permuteQuantifier.
  Qed.                               
    
Ltac doubleH H :=
let tH := type of H in
   let H := fresh H in assert(H:tH) by auto.

Lemma BinaryRIGHT n n' n0 n1  C F G FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_bin C F G) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
  seqN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleBin C F G)) ->
  seqN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) ::M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleBin C F G) ->
  buildTheory F0 ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellFormedBin Hseq1'.
  * Cases H. 
     2:{ apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite H in H3.
         rewrite <- app_comm_cons in H3 . 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ( (⌈ t_bin C F G ⌉) ::(M++ x4))...
         apply H8...
         rewrite app_assoc_reverse... }
   2:{ apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite <- app_comm_cons in H4. 
         cutOL H4 Hseq2.
         1-2: OLSolve.
        TFocus (makeRRuleBin C F G).
               inversion H.
               FLLsplit (@nil oo) (M++N).
               apply H8...
               rewrite app_assoc_reverse... }
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H1. 
               rewrite <- app_comm_cons...
           -- Cases H1. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H11.
               1-2: OLSolve.
               OLSolve.
               apply H16...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H12.
               1-2: OLSolve.
               TFocus (makeRRuleConstant C0).
               inversion H1.
               FLLsplit (@nil oo) (M++N).
               apply H16...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H1. 
              rewrite <- app_comm_cons...
           -- Cases H1. 
              apply weakeningGenN_rev with (CC':= x5) in Hseq1. 
              rewrite H1 in H11.
              rewrite <- app_comm_cons in H11.
              cutOL Hseq1 H11.
               1-2: OLSolve.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
              
              apply weakeningGenN_rev with (CC':= x5) in Hseq1. 
              rewrite <- app_comm_cons in H12.
              cutOL Hseq1 H12.
               1-2: OLSolve.
                 TFocus (makeLRuleConstant C0).
                 inversion H1.
             FLLsplit (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellFormedBin Hseq2'.
           { Cases H1. 
            
            rewrite <- H7 in H4. 
            rewrite <- H15 in H12. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
            apply weakeningGenN_rev with (CC':= x5) in Hseq1. 
              rewrite H1 in H11.
              rewrite <- app_comm_cons in H11.
              cutOL Hseq1 H11.
               1-2: OLSolve.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
              
              apply weakeningGenN_rev with (CC':= x5) in Hseq1. 
              rewrite <- app_comm_cons in H12.
              cutOL Hseq1 H12.
               1-2: OLSolve.
                 TFocus (makeLRuleBin C0 F1 G0).
                 inversion H1.
             FLLsplit (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H1. 
            
            rewrite <- H7 in H4. 
            rewrite <- H18 in H12. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H14.
               1-2: OLSolve.
            rewrite <- H18 in H17.
             rewrite H17 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bin C0 F1 G0 ⌋) :: (x13 ++ N) ++ x5).
              apply H19...
              rewrite Permutation_assoc_comm...
               
               apply seqNtoSeq in H15...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              
               PermuteLeft.
            cutOL Hseq1 H15.
               1-2: OLSolve.
             rewrite <- H18 in H17.
             rewrite H17 in PosM.
             inversion PosM...
             OLSolve.  
            LLPerm ( (⌊ t_bin C0 F1 G0 ⌋) :: x4++(x13 ++ N)).
              apply H19...
              apply seqNtoSeq in H14...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H15. 
               1-2: OLSolve.
               rewrite <- H18 in PosM.
               OLSolve.
                TFocus (makeLRuleBin C0 F1 G0).
                 inversion H1.
             FLLsplit (@nil oo) ( ((x12 ++ N) ++ x5)).
               apply H20...  
               rewrite Permutation_assoc_comm...
               apply seqNtoSeq in H16...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H16. 
               1-2: OLSolve.
               rewrite <- H18 in PosM.
               OLSolve.
                TFocus (makeLRuleBin C0 F1 G0).
                 inversion H1.
             FLLsplit (@nil oo) (x4++(x12 ++ N) ).
               apply H20...
               apply seqNtoSeq in H15...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
               
           { Cases H1. 
            
            rewrite <- H7 in H4. 
            rewrite <- H18 in H12. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H14.
               1-2: OLSolve.
            OLSolve.
            cutOL Hl' H15.
               1-2: OLSolve.
            OLSolve.
            LLPerm ( (⌊ t_bin C0 F1 G0 ⌋) :: (x11 ++ N) ).
              apply H19...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H15.
               1-2: OLSolve.
             cutOL Hl' H16.
               1-2: OLSolve.
             TFocus (makeLRuleBin C0 F1 G0).
                 inversion H1.
             FLLsplit (@nil oo) (M ++ N).
               apply H20...
            1-2:  rewrite Permutation_assoc_comm... }
                           
          - permuteQuantifier.
         - permuteQuantifier.
  * Cases H. 
     2:{ apply weakeningGenN_rev with (CC':= x3) in Hseq2. 
         rewrite H5 in H6.
         rewrite <- app_comm_cons in H6 . 
         cutOL H6 Hseq2.
         1-2: OLSolve.
                      rewrite <- H10 in H9.
             rewrite H9 in PosN.
             inversion PosN...
             OLSolve.  
         LLPerm ( (⌈ t_bin C F G ⌉) ::(M++ x8)++x0)...
         apply H11...
         rewrite app_assoc_reverse... 
          apply seqNtoSeq in H7...
               apply WeakTheory with (theory := OLTheory nPnN )...  }
   2:{ apply weakeningGenN_rev with (CC':= x4) in Hseq2. 
         rewrite H5 in H7.
         rewrite <- app_comm_cons in H7. 
         cutOL H7 Hseq2.
         1-2: OLSolve.
                      rewrite <- H10 in H9.
             rewrite H9 in PosN.
             inversion PosN...
             OLSolve.  
        LLPerm ( (⌈ t_bin C F G ⌉) ::x++(M++ x8))...
         apply H11...
           apply seqNtoSeq in H6...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
               rewrite app_assoc_reverse... 
         }
     2:{ apply weakeningGenN_rev with (CC':= x3) in Hseq2. 
         rewrite H4 in H7.
         rewrite <- app_comm_cons in H7. 
         cutOL H7 Hseq2.
         1-2: OLSolve.
         rewrite <- H10 in PosN.
         OLSolve.
         TFocus (makeRRuleBin C F G).
               inversion H.
               FLLsplit (@nil oo) ((M ++ x7)++x0).
         apply H12...
         rewrite app_assoc_reverse... 
          apply seqNtoSeq in H8...
               apply WeakTheory with (theory := OLTheory nPnN )...  }
     2:{ apply weakeningGenN_rev with (CC':= x4) in Hseq2. 
         rewrite H4 in H8.
         rewrite <- app_comm_cons in H8. 
         cutOL H8 Hseq2.
         1-2: OLSolve.
         rewrite <- H10 in PosN.
         OLSolve.
         TFocus (makeRRuleBin C F G).
               inversion H.
               FLLsplit (@nil oo) (x++(M ++ x7)).
         apply H12...
          apply seqNtoSeq in H7...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1. 
               rewrite app_assoc_reverse... }               
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H5. 
               rewrite <- app_comm_cons...
           -- Cases H5. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H14.
               1-2: OLSolve.
               OLSolve.
               apply H19...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H15.
               1-2: OLSolve.
               TFocus (makeRRuleConstant C0).
               inversion H5.
               FLLsplit (@nil oo) (M++N).
               apply H19...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H5. 
              rewrite <- app_comm_cons...
           -- Cases H5. 
              apply weakeningGenN_rev with (CC':= x8) in Hseq1. 
              rewrite H5 in H14.
              rewrite <- app_comm_cons in H14.
              cutOL Hseq1 H14.
               1-2: OLSolve.
               rewrite H17 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H19...
               rewrite Permutation_assoc_comm...
              
              apply weakeningGenN_rev with (CC':= x8) in Hseq1. 
              rewrite <- app_comm_cons in H15.
              cutOL Hseq1 H15.
               1-2: OLSolve.
                 TFocus (makeLRuleConstant C0).
                 inversion H5.
             FLLsplit (@nil oo) (M++N).
               apply H19...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellFormedBin Hseq2'.
           { Cases H5. 
            
            rewrite <- H10 in H4. 
            rewrite <- H18 in H15. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
            apply weakeningGenN_rev with (CC':= x8) in Hseq1. 
              rewrite H5 in H14.
              rewrite <- app_comm_cons in H14.
              cutOL Hseq1 H14.
               1-2: OLSolve.
               rewrite H17 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H19...
               rewrite Permutation_assoc_comm...
              
              apply weakeningGenN_rev with (CC':= x8) in Hseq1. 
              rewrite <- app_comm_cons in H15.
              cutOL Hseq1 H15.
               1-2: OLSolve.
                 TFocus (makeLRuleBin C0 F1 G0).
                 inversion H5.
             FLLsplit (@nil oo) (M++N).
               apply H19...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H5. 
            
            rewrite <- H10 in H4. 
            rewrite <- H21 in H15. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H17.
               1-2: OLSolve.
                         rewrite <- H21 in H20.
             rewrite H20 in PosM.
             inversion PosM...
             OLSolve.     
            LLPerm ( (⌊ t_bin C0 F1 G0 ⌋) :: (x16 ++ N) ++ x8).
              apply H22...
              rewrite Permutation_assoc_comm...
               
               apply seqNtoSeq in H18...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              
               PermuteLeft.
            cutOL Hseq1 H18.
            1-2: OLSolve. 
                         rewrite <- H21 in H20.
             rewrite H20 in PosM.
             inversion PosM...
             OLSolve.  
            LLPerm ( (⌊ t_bin C0 F1 G0 ⌋) :: x7++(x16 ++ N)).
              apply H22...
              apply seqNtoSeq in H17...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H18. 
               1-2: OLSolve.
               rewrite <- H21 in PosM.
               OLSolve.
                TFocus (makeLRuleBin C0 F1 G0).
                 inversion H5.
             FLLsplit (@nil oo) ( ((x15 ++ N) ++ x8)).
               apply H23...  
               rewrite Permutation_assoc_comm...
               apply seqNtoSeq in H19...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H19. 
               1-2: OLSolve.
               rewrite <- H21 in PosM.
               OLSolve.
                TFocus (makeLRuleBin C0 F1 G0).
                 inversion H5.
             FLLsplit (@nil oo) (x7++(x15 ++ N) ).
               apply H23...
               apply seqNtoSeq in H18...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
               
           { Cases H5. 
            
            rewrite <- H10 in H4. 
            rewrite <- H21 in H15. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H17.
               1-2: OLSolve.
            OLSolve.
            cutOL Hl' H18.
               1-2: OLSolve.
            OLSolve.
            LLPerm ( (⌊ t_bin C0 F1 G0 ⌋) :: (x14 ++ N) ).
              apply H22...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H18.
               1-2: OLSolve.
             cutOL Hl' H19.
               1-2: OLSolve.
             TFocus (makeLRuleBin C0 F1 G0).
                 inversion H5.
             FLLsplit (@nil oo) (M ++ N).
               apply H23...
            1-2:  rewrite Permutation_assoc_comm... }
                           
          - permuteQuantifier.
         - permuteQuantifier.
  * Cases H. 
     2:{ 
        doubleH Hseq2.
        apply weakeningGenN_rev with (CC':= x2) in Hseq2. 
        apply weakeningGenN_rev with (CC':= x3) in Hseq0. 
        
         rewrite H5 in H6.
         rewrite <- app_comm_cons in H6 . 
         cutOL H6 Hseq2.
         1-2: OLSolve.
         rewrite H9 in PosN.
         OLSolve.
         
         rewrite H5 in H7.
         rewrite <- app_comm_cons in H7 . 
         cutOL H7 Hseq0.
         1-2: OLSolve.
         rewrite H9 in PosN.
         OLSolve.
         
         LLPerm ((⌈ t_bin C F G ⌉) ::M++ x6)...
         apply H11...
         1-2: rewrite app_assoc_reverse... 
          }
   2:{ 
     doubleH Hseq2.
        apply weakeningGenN_rev with (CC':= x2) in Hseq2. 
        apply weakeningGenN_rev with (CC':= x3) in Hseq0. 
        
         rewrite <- H4 in H7.
         rewrite <- app_comm_cons in H7 . 
         cutOL H7 Hseq2.
         1-2: OLSolve.
         
         rewrite <- H4 in H8.
         rewrite <- app_comm_cons in H8. 
         cutOL H8 Hseq0.
         1-2: OLSolve.
         TFocus (makeRRuleBin C F G).
               inversion H.
               FLLsplit (@nil oo) (M ++N).
         apply H12...
        1-2: rewrite app_assoc_reverse... } 
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H5. 
               rewrite <- app_comm_cons...
           -- Cases H5. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H14.
               1-2: OLSolve.
               OLSolve.
               apply H19...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H15.
               1-2: OLSolve.
               TFocus (makeRRuleConstant C0).
               inversion H5.
               FLLsplit (@nil oo) (M++N).
               apply H19...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H5. 
              rewrite <- app_comm_cons...
           -- Cases H5.
               PermuteLeft.
               cutOL Hseq1 H14.
               1-2: OLSolve.
               rewrite H17 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H19...
               rewrite Permutation_assoc_comm...
              
              PermuteLeft.
              cutOL Hseq1 H15.
               1-2: OLSolve.
                 TFocus (makeLRuleConstant C0).
                 inversion H5.
             FLLsplit (@nil oo) (M++N).
               apply H19...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellFormedBin Hseq2'.
           { Cases H5. 
            
            rewrite <- H10 in H4. 
            rewrite <- H18 in H15. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
             
             PermuteLeft.
              cutOL Hseq1 H14.
               1-2: OLSolve.
               rewrite H17 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H19...
               rewrite Permutation_assoc_comm...
              
              PermuteLeft.
              cutOL Hseq1 H15.
               1-2: OLSolve.
                 TFocus (makeLRuleBin C0 F1 G0).
                 inversion H5.
             FLLsplit (@nil oo) (M++N).
               apply H19...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H5. 
            
            rewrite <- H10 in H4. 
            rewrite <- H21 in H15. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H17.
               1-2: OLSolve.
             rewrite <- H21 in H20.
             rewrite H20 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bin C0 F1 G0 ⌋) :: (x15 ++ N) ++ x7).
              apply H22...
              rewrite Permutation_assoc_comm...
               
               apply seqNtoSeq in H18...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              
               PermuteLeft.
            cutOL Hseq1 H18.
               1-2: OLSolve.
             rewrite <- H21 in H20.
             rewrite H20 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bin C0 F1 G0 ⌋) :: x6++(x15 ++ N)).
              apply H22...
              apply seqNtoSeq in H17...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H18. 
               1-2: OLSolve.
               rewrite <- H21 in PosM.
               OLSolve.
                TFocus (makeLRuleBin C0 F1 G0).
                 inversion H5.
             FLLsplit (@nil oo) ( ((x14 ++ N) ++ x7)).
               apply H23...  
               rewrite Permutation_assoc_comm...
               apply seqNtoSeq in H19...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H19. 
               1-2: OLSolve.
               rewrite <- H21 in PosM.
               OLSolve.
                TFocus (makeLRuleBin C0 F1 G0).
                 inversion H5.
             FLLsplit (@nil oo) (x6++(x14 ++ N) ).
               apply H23...
               apply seqNtoSeq in H18...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
               
           { Cases H5. 
            
            rewrite <- H10 in H4. 
            rewrite <- H21 in H15. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H4 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H17.
               1-2: OLSolve.
            OLSolve.
            cutOL Hl' H18.
               1-2: OLSolve.
            OLSolve.
            LLPerm ((⌊ t_bin C0 F1 G0 ⌋) :: (x13 ++ N) ).
              apply H22...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H18.
               1-2: OLSolve.
             cutOL Hl' H19.
               1-2: OLSolve.
             TFocus (makeLRuleBin C0 F1 G0).
                 inversion H5.
             FLLsplit (@nil oo) (M ++ N).
               apply H23...
            1-2:  rewrite Permutation_assoc_comm... }
                           
          - permuteQuantifier.
         - permuteQuantifier.         
  Qed.                        
   
Lemma QuantifierRIGHT n n' n0 n1  C FX FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_quant C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n0)  Gamma ( (⌈ FCut ⌉) ::N) (UP []) ->
  seqN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleQ C FX)) ->
  seqN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleQ C FX) ->
  buildTheory F0 ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellFormedQ Hseq1'.
  Cases H. 
  2:{ apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite H in H3.
         rewrite <- app_comm_cons in H3 . 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ( (⌈ t_quant C FX ⌉) ::(M++ x4))...
         apply H8...
         rewrite app_assoc_reverse... }
  2:{ apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
          rewrite <- app_comm_cons in H4 . 
         cutOL H4 Hseq2.
         1-2: OLSolve.
         TFocus (makeRRuleQ C FX).
         inversion H.
         FLLsplit (@nil oo) (M++N).
         apply H8...
         rewrite app_assoc_reverse... }         
    inversion Hth'... 
           -- wellConstant Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               Cases H1. 
               PermuteLeft.
               cutOL Hseq1 H11.
               1-2: OLSolve.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H16...
               LLPerm ((x9 ++ x4) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H12.
               1-2: OLSolve.
               TFocus (makeRRuleConstant C0).
               inversion H1.
               FLLsplit (@nil oo) (M++N).
               apply H16...
               LLPerm ( (M ++ x4) ++ N)...
           -- wellConstant Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               Cases H1. 
               PermuteLeft.
               cutOL Hseq1 H11.
               1-2: OLSolve.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H16...
               LLPerm ((x9 ++ x4) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H12.
               1-2: OLSolve.
               TFocus (makeLRuleConstant C0).
               inversion H1.
               FLLsplit (@nil oo) (M++N).
               apply H16...
               LLPerm ( (M ++ x4) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.           
           -- wellFormedQ Hseq2'.
               destruct H1...
               checkPermutationCases H1.
               inversion H14...
               rewrite <- H7 in H4.
               rewrite <- H15 in H12.
               rewrite Permutation_app_comm.
               refine (QuantifierPrincipalCase H12 H4 _ _ _ _ _ _ HL')...   
               PermuteLeft.
               cutOL Hseq1 H11.
               1-2: OLSolve.
               OLSolve.
               rewrite H14.
               LLPerm ( (⌊t_quant C0 FX0 ⌋) :: x9++ N).
               apply H16...
               LLPerm ((x9 ++ x4) ++ N)...
               
               PermuteLeft.
               cutOL Hseq1 H12.
               1-2: OLSolve.
              TFocus (makeLRuleQ C0 FX0).
               inversion H1.
               FLLsplit (@nil oo) (M++N).
               apply H16...
               LLPerm ((M ++ x4) ++ N)...
     Qed.         
             
Definition ConnectiveLeft connective rule := forall n n' n0 n1  FCut M N Gamma,
  n' <= n ->
  isOLFormula connective ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW rule) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory rule ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
     

             
Lemma ConstantLEFT n n' n0 n1  C FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_cons C) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleConstant C)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleConstant C) ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellConstant Hseq1'.
  * Cases H. 
     + LLPerm ( (⌊ t_cons C ⌋) :: x0++M)...
  * Cases H. 
     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite H in H3.
         rewrite <- app_comm_cons in H3. 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ( (⌊ t_cons C ⌋) ::(M++ x4)).
         apply H8...
         LLPerm(M ++ x4 ++ x)...
    +  apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite <- app_comm_cons in H4.  
         cutOL H4 Hseq2.
         1-2: OLSolve.
         TFocus (makeLRuleConstant C).
         inversion H.
         FLLsplit (@nil oo) (M++N).
         apply H8... 
         LLPerm(M ++ N ++ x)...
Qed.                  
         
 Lemma UnaryLEFT n n' n0 n1 C F FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_ucon C F) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n1) Gamma  ( (⌊ FCut ⌋) :: M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleUnary C F)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleUnary C F) ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellFormedU Hseq1'.
  * Cases H. 
     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite H in H3. 
         rewrite <- app_comm_cons in H3. 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ( (⌊ t_ucon C F ⌋) ::(M++ x4)).
         apply H8...
         LLPerm(M ++ x4 ++ x)...
     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite <- app_comm_cons in H4. 
         cutOL H4 Hseq2.
         1-2: OLSolve.
         TFocus (makeLRuleUnary C F).
         inversion H.
         FLLsplit (@nil oo) (M++N).
         apply H8... 
         LLPerm(M ++ N ++ x)...
Qed.       

 Lemma BinaryLEFT n n' n0 n1 C F G FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_bin C F G) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleBin C F G)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleBin C F G) ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellFormedBin Hseq1'.
  * Cases H. 
     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite H in H3. 
         rewrite <- app_comm_cons in H3. 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ( (⌊t_bin C F G ⌋) ::(M++ x4)).
         apply H8...
         LLPerm(M ++ x4 ++ x)...
     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite <- app_comm_cons in H4. 
         cutOL H4 Hseq2.
         1-2: OLSolve.
         TFocus (makeLRuleBin C F G).
         inversion H.
         FLLsplit (@nil oo) (M++N).
         apply H8... 
         LLPerm(M ++ N ++ x)...
  * Cases H. 
     + 
     apply weakeningGenN_rev with (CC':= x3) in Hseq2. 
         rewrite H5 in H6.
         rewrite <- app_comm_cons in H6. 
         cutOL H6 Hseq2.
         1-2: OLSolve.
         rewrite  <- H10 in H9. 
         rewrite H9 in PosN.
         inversion PosN...
         OLSolve.
         LLPerm ((⌊ t_bin C F G ⌋) :: (M++x8) ++ x0).
         apply H11...
         rewrite app_assoc_reverse...
         apply seqNtoSeq in H7...
         apply WeakTheory with (theory := OLTheory nPnN )... 
     + 
     apply weakeningGenN_rev with (CC':= x4) in Hseq2. 
         rewrite H5 in H7.
         rewrite <- app_comm_cons in H7. 
         cutOL H7 Hseq2.
         1-2: OLSolve.
         rewrite  <- H10 in H9. 
         rewrite H9 in PosN.
         inversion PosN...
         OLSolve.
         LLPerm ( (⌊ t_bin C F G ⌋) :: x++(M++x8)).
         apply H11...
         apply seqNtoSeq in H6...
         apply WeakTheory with (theory := OLTheory nPnN )... 
          
         rewrite app_assoc_reverse...
     + 
     apply weakeningGenN_rev with (CC':= x3) in Hseq2. 
         rewrite H4 in H7.
         rewrite <- app_comm_cons in H7. 
         cutOL H7 Hseq2.
         1-2: OLSolve.
         rewrite  <- H10 in PosN.
         OLSolve.
         TFocus  (makeLRuleBin C F G).
         inversion H.
         FLLsplit (@nil oo) ((M ++ x7) ++ x0).
         apply H12...
         rewrite app_assoc_reverse...
         apply seqNtoSeq in H8...
         apply WeakTheory with (theory := OLTheory nPnN )... 
     + 
     apply weakeningGenN_rev with (CC':= x4) in Hseq2. 
         rewrite H4 in H8.
         rewrite <- app_comm_cons in H8. 
         cutOL H8 Hseq2.
         1-2: OLSolve.
         rewrite  <- H10 in PosN.
         OLSolve.
         TFocus  (makeLRuleBin C F G).
         inversion H.
         FLLsplit (@nil oo) (x++(M ++ x7)).
         apply H12...
         apply seqNtoSeq in H7...
         apply WeakTheory with (theory := OLTheory nPnN )... 
           rewrite app_assoc_reverse...
  * Cases H. 
     + doubleH Hseq2.
     apply weakeningGenN_rev with (CC':= x2) in Hseq2. 
     apply weakeningGenN_rev with (CC':= x3) in Hseq0. 
     
         rewrite H5 in H6, H7.
         rewrite <- app_comm_cons in H6,H7. 
         cutOL H6 Hseq2.
         1-2: OLSolve.
         rewrite H9 in PosN.
         OLSolve.
         cutOL H7 Hseq0.
         1-2: OLSolve.
         rewrite H9 in PosN.
         OLSolve.
         LLPerm ( (⌊ t_bin C F G ⌋) :: M++x6).
         apply H11...
         1-2: rewrite app_assoc_reverse...
     + doubleH Hseq2.
     apply weakeningGenN_rev with (CC':= x2) in Hseq2. 
     apply weakeningGenN_rev with (CC':= x3) in Hseq0. 
     
         rewrite <- H4 in H7, H8.
         rewrite <- app_comm_cons in H7, H8. 
         cutOL H7 Hseq2.
         1-2: OLSolve.
         cutOL H8 Hseq0.
         1-2: OLSolve.
         TFocus (makeLRuleBin C F G). 
         inversion H.
         FLLsplit (@nil oo) (M++N).
         apply H12...
         1-2: rewrite app_assoc_reverse... 
Qed.         
         
 Lemma QuantifierLEFT n n' n0 n1 C FX FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_quant C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  seqN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  seqN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleQ C FX)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleQ C FX) ->
  seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellFormedQ Hseq1'.
  * Cases H. 
     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite H in H3. 
         rewrite <- app_comm_cons in H3. 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ( (⌊ t_quant C FX ⌋) ::(M++ x4)).
         apply H8...
         LLPerm(M ++ x4 ++ x)...
     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite <- app_comm_cons in H4. 
         cutOL H4 Hseq2.
         1-2: OLSolve.
         TFocus (makeLRuleQ C FX).
         inversion H.
         FLLsplit (@nil oo) (M++N).
         apply H8... 
         LLPerm(M ++ N ++ x)...
Qed.
 
 (** Main theorem showing that it is possible to fins a proof with
  the theory [ (OLTheoryCut nPnN (pred n))] *)
  Theorem OLCutElimStep :
    forall h1 h2 n N M Gamma FCut n',
      isOLFormula FCut ->
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtomFormulaL N ->
      IsPositiveAtomFormulaL M ->
      seqN (OLTheory nPnN) h1 Gamma ( atom(up FCut)::N) (UP []) ->
      seqN (OLTheory nPnN) h2 Gamma (atom (down FCut)::M) (UP []) ->
      lengthUexp FCut n' -> n'<=n ->
      (seq (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP [])) .
  Proof with sauto.
    intros h1 h2 n N M Gamma FCut n' HisF PosG PosN PosM Hseq1 Hseq2 HL HL'.
    remember (plus h1 h2) as h.
    generalize dependent Gamma.
    generalize dependent N.
    generalize dependent M.
    generalize dependent FCut.
    generalize dependent n. 
    generalize dependent h1.
    generalize dependent h2.
  
    induction h using lt_wf_ind; intros. 

    inversion Hseq1...
    cut(False);intros...
    refine (onlyAtomsLinear _ H0 H1)...
    cut(False);intros...
    refine (onlyAtomsClassical _ H0 H1)...

    inversion Hseq2...
    cut(False);intros...
    refine (onlyAtomsLinear _ H3 H4)...
    cut(False);intros...
    refine (onlyAtomsClassical _ H3 H4)...
    
    assert(OOCut n' (S n0 + S n1)).
    {
    unfold OOCut; intros.
    revert H13 H14.
    eapply H with  (m:=h1 + h2)... }
    clear H.
    rename n0 into h1.
    rename n1 into h2.
   (* Now we proceed by cases on the last rule applied on both derivations *)
    inversion H1 ;inversion H4...
    * inversion H...
       - refine(ConstantRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)... 
       - refine(ConstantLEFT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
       - refine(UnaryRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)... 
       - refine(UnaryLEFT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
       - refine(BinaryRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)... 
       - refine(BinaryLEFT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
       - refine(QuantifierRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)...        
       - refine(QuantifierLEFT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
    * apply FocusingInitRuleU in H5...
       - checkPermutationCases H7. 
          inversion H7...
          apply seqNtoSeq in Hseq1.
          apply WeakTheory with (theory := OLTheory nPnN )... 
        - inversion H9...
           apply absorptionInN in Hseq1...
          apply seqNtoSeq in Hseq1.
          apply WeakTheory with (theory := OLTheory nPnN )... 
    * apply FocusingInitRuleU in H2...
       - checkPermutationCases H7. 
          inversion H9...
          apply seqNtoSeq in Hseq2.
          apply WeakTheory with (theory := OLTheory nPnN )... 
         LLExact Hseq2.
        - inversion H7...
           apply absorptionInN in Hseq2...
          apply seqNtoSeq in Hseq2.
          apply WeakTheory with (theory := OLTheory nPnN )... 
    * apply FocusingInitRuleU in H2...
       - checkPermutationCases H7. 
          inversion H9...
          apply seqNtoSeq in Hseq2.
          apply WeakTheory with (theory := OLTheory nPnN )... 
         LLExact Hseq2.
        - inversion H7...
           apply absorptionInN in Hseq2...
          apply seqNtoSeq in Hseq2.
          apply WeakTheory with (theory := OLTheory nPnN )... 
 Qed.                   
         
  Theorem OLCutElimAux :
    forall n h  B N ,
      IsPositiveAtomFormulaL B ->
      IsPositiveAtomFormulaL N ->
      seqN  (OLTheoryCut nPnN n) h  B N (UP[] ) ->
      seq  (OLTheoryCut nPnN 0) B N (UP[] ) .
  Proof with sauto;try OLSolve.
  induction n ; induction h using lt_wf_ind; intros *;intros isFB isFN Hh.
    * eapply seqNtoSeq;eauto.
    * inversion Hh...
       cut(False);intros...
       refine (onlyAtomsLinear _ H0 H1)...
       cut(False);intros...
       refine (onlyAtomsClassical _ H0 H1)...
       inversion H1...
       inversion H3...
       inversion H4...
      + (* constant *)
         wellConstant H2.
         Cases H6.
         apply H10...
         Cases H6.
         apply H15...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         TFocus (makeRRuleConstant C).
         FLLsplit (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* constant *)
         wellConstant H2.
         Cases H6.
         apply H10...
         Cases H6.
         apply H15...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         TFocus (makeLRuleConstant C).
         FLLsplit (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* unary *)
         wellFormedU H2.
         Cases H6.
         apply H15...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         TFocus (makeRRuleUnary C F0).
         FLLsplit (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* unary *)
         wellFormedU H2.
         Cases H6.
         apply H15...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         TFocus (makeLRuleUnary C F0).
         FLLsplit (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* binary *)
         wellFormedBin H2.
         { Cases H6.
         apply H15...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         TFocus (makeRRuleBin C F0 G).
         FLLsplit (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)... }
         { Cases H6.
         apply H18...
         refine (H _ _ _ _ _ _ H13)...
         OLSolve.
         rewrite H12 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H14)...
         rewrite H12 in isFN.
         inversion isFN...
         TFocus (makeRRuleBin C F0 G).
         FLLsplit (@nil oo) N.
         rewrite H11.
         apply H19...
         refine (H _ _ _ _ _ _ H14)... 
         rewrite H11 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H15)... 
         rewrite H11 in isFN.
         inversion isFN... }
         { Cases H6.
         apply H18...
         refine (H _ _ _ _ _ _ H13)...
         OLSolve.
         rewrite H12 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H14)...
         TFocus (makeRRuleBin C F0 G).
         FLLsplit (@nil oo) N.
         rewrite H11.
         apply H19...
         refine (H _ _ _ _ _ _ H14)... 
         rewrite H11 in isFN...
         refine (H _ _ _ _ _ _ H15)... 
         rewrite H11 in isFN...  } 
      + (* binary *)
         wellFormedBin H2.
         { Cases H6.
         apply H15...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         TFocus (makeLRuleBin C F0 G).
         FLLsplit (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)... }
         { Cases H6.
         apply H18...
         refine (H _ _ _ _ _ _ H13)...
         OLSolve.
         rewrite H12 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H14)...
         rewrite H12 in isFN.
         inversion isFN...
         TFocus (makeLRuleBin C F0 G).
         FLLsplit (@nil oo) N.
         rewrite H11.
         apply H19...
         refine (H _ _ _ _ _ _ H14)... 
         rewrite H11 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H15)... 
         rewrite H11 in isFN.
         inversion isFN... }
         { Cases H6.
         apply H18...
         refine (H _ _ _ _ _ _ H13)...
         OLSolve.
         rewrite H12 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H14)...
         TFocus (makeLRuleBin C F0 G).
         FLLsplit (@nil oo) N.
         rewrite H11.
         apply H19...
         refine (H _ _ _ _ _ _ H14)... 
         rewrite H11 in isFN...
         refine (H _ _ _ _ _ _ H15)... 
         rewrite H11 in isFN...  } 
      + (* quantifier *)
         wellFormedQ H2.
         Cases H6.
         apply H15...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         TFocus (makeRRuleQ C FX).
         FLLsplit (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* quantifier *)
         wellFormedQ H2.
         Cases H6.
         apply H15...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         TFocus (makeLRuleQ C FX).
         FLLsplit (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* init *)
         apply FocusingInitRuleU in H2...
         rewrite H5.
         TFocus (RINIT OO).
         FLLsplit [ (⌈ OO ⌉)] [(⌊ OO ⌋)].
         TFocus (RINIT OO).
         FLLsplit [ (⌈ OO ⌉)] (@nil oo).
         TFocus (RINIT OO).
         FLLsplit (@nil oo) [ (⌊ OO ⌋)].
         TFocus (RINIT OO).
         FLLsplit.
      + (* cut *)
         inversion H3...
         inversion H2...
         2:{ inversion H8. }
         invTri H13.
         invTri H14.
         invTri H13.
         invTri H15.
         clear H0 H1 H2 H3 Hh.
         apply H in H16...
         2: repeat OLSolve. 
         apply H in H14...
         2: repeat OLSolve. 
         apply WeakTheory with (theory' := OLTheory nPnN) in H16;auto;try apply OOTheryCut0.
         apply WeakTheory with (theory' := OLTheory nPnN) in H14;auto;try apply OOTheryCut0.
         rewrite H9.
         apply WeakTheory with (theory := OLTheory nPnN).
         apply OOTheryCut0.
  
         destruct m.
         generalize(LengthFormula H4 H5);intro;lia.
         assert (seq (OLTheoryCut nPnN (pred  (S (n)))) B (M ++ N0) (UP [])) .
         rewrite Permutation_app_comm.
         apply seqtoSeqN in H16...
         apply seqtoSeqN in H14...
         refine(OLCutElimStep _ _ _ _ H14 H16 H5 _)...  
         apply seqtoSeqN in H0...
         apply IHn in H0...
         apply WeakTheory with (theory' := OLTheory nPnN) in H0;auto;try apply  OOTheryCut0.
Qed.   
  
  (** Cut-elimination theorem for Object Logics satisfying cut-]
  coherence *)
  Theorem OLCutElimination :
    forall n h  B N ,
      IsPositiveAtomFormulaL B ->
      IsPositiveAtomFormulaL N ->
      seqN (OLTheoryCut nPnN n) h  B N (UP [] ) ->
      seq (OLTheory nPnN) B N (UP [] ) .
  Proof with sauto.
    intros. 
    apply OLCutElimAux in H1 ...
    eapply WeakTheory with (theory':= OLTheory nPnN) in H1 ...
    apply OOTheryCut0.
  Qed.     
  
End CutElimination.
