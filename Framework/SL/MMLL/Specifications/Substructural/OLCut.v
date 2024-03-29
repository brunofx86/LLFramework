
(** * LL as a Meta-logical framework.  *)

(** In this file we show how the cut-elimination procedure for FLL can
be used to prove cut-elimination for object logics that are
cut-coherent in the sense of Miller & Pimentel. Roughly, a system is
cut-coherent if the encoding of the right and left rules of each
connective are dual. *)

Require Export LL.Misc.Hybrid.
Require Export LL.Framework.SL.MMLL.Specifications.StructuralClauses. 

Require Export LL.Framework.SL.MMLL.Specifications.Requirement1.

Require Export LL.Framework.SL.MMLL.Specifications.OLTheory.

Require Import Coq.Init.Nat.
Require Import LL.Framework.SL.MMLL.CutEliminationUnb.
Require Import LL.Framework.SL.MMLL.Reasoning.
Require Import LL.Framework.OL.SyntaxResults.

Import LL.Misc.Permutations.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Cut Elimination Procedure *)
Section CutElimination .

  Context `{OLR: OORules}.
  Context {SIU: UNoDSigMMLL} .

  (** As a general hypothesis, we assume that the Object logic is cut-coherent *)
  Hypothesis LTWell1 : wellFormedTheory.
  Hypothesis LTCutCoherence: CutCoherence cutR1.
   
  Definition ctWellFormed := proj1 LTWell1.
  Definition unWellFormed := proj1 (proj2 LTWell1).
  Definition biWellFormed := proj1 (proj2 (proj2 LTWell1)).
  Definition quWellFormed := proj2 (proj2 (proj2 LTWell1)).

  Definition ctCutCo := proj1 LTCutCoherence.
  Definition unCutCo := proj1 (proj2 LTCutCoherence).
  Definition biCutCo := proj1 (proj2 (proj2 LTCutCoherence)).
  Definition quCutCo := proj2 (proj2 (proj2 LTCutCoherence)).

   (** Extracting the needed facts given that all the OL constants are well-defined *)
   Ltac wellConstant HSeq :=
    let HS := type of HSeq in
    match HS with
    | MLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C)) =>
      let Side' :=
          match Side with 
          makeRRuleC => Right
           | makeLRuleC => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize (ctWellFormed Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ];
          destruct bpEnum;[ apply LTWell' in HSeq; contradiction (* fail case *)
                          | generalize (LTWell' _ HSeq);intro;clear LTWell' (* axiom *)
                          | generalize (LTWell' _ HSeq);intro;clear LTWell'] (* one premise *)
    end.
    
   Ltac wellUnary HSeq  :=
    let HS := type of HSeq in
    match HS with
    | (MLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with 
          makeRRuleU => Right 
          | makeLRuleU => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize  (unWellFormed Rules Gamma M C Side' );
        intro LTWell';generalize (LTWell' _ _ HSeq);intro;clear LTWell'
    end.
 
  (** Extracting well-formed conditions for binary predicates *)
  Ltac wellBinary HSeq :=
    let HS := type of HSeq in
    match HS with
    | (MLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F ?G))) =>
      let Side' :=
          match Side with makeRRuleB => Right | makeLRuleB => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize (biWellFormed Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ]; 
        destruct bpEnum;generalize (LTWell' _ _ _ HSeq);intro;clear LTWell'
    end.

  Ltac wellQuantifier HSeq :=
    let HS := type of HSeq in
    match HS with
    | (MLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with makeRRuleQ => Right | makeLRuleQ => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
         let HUniform := fresh "HUniform" in
        generalize  (quWellFormed Rules Gamma M C Side' F); intro LTWell';
      destruct LTWell' as [HUniform LTWell'];generalize (LTWell'  _ HSeq); intro; clear LTWell'
    end.
Definition EmptyTheory (F :oo) := False.

Lemma EmptySubSetN : forall (theory : oo-> Prop) CC LC X n,
      MLLN EmptyTheory n CC LC X -> MLLN theory n CC LC X.
Proof.    
  intros.
  apply WeakTheoryN with (th:= EmptyTheory);auto.
  intros.
  inversion H0.
Qed.
  
Lemma EmptySubSet : forall (theory : oo-> Prop) CC LC X,
      MLLS EmptyTheory CC LC X -> MLLS theory CC LC X.
Proof.
  intros.
  apply WeakTheory with (th:= EmptyTheory);auto.
  intros.
  inversion H0.
Qed.


 (** This is the case when a constant is principal in both premises *)
  Theorem ConstantPrincipalCase :
    forall Gamma M N C,
      (MLLS (OLTheory nPnN) Gamma M (DW (rc_lftBody (rulesC C)))) ->
      (MLLS (OLTheory nPnN) Gamma N (DW (rc_rgtBody (rulesC C)))) ->
      MLLS (OLTheory nPnN) Gamma (N ++ M) (UP []).
 Proof with sauto.     
    intros.
    apply MLLStoSeqN in H... 
    apply MLLStoSeqN in H0...
    generalize( ctCutCo C);intro CutC.
    unfold CutCoherenceCte in CutC.
    destruct CutC as [Hc CutC].
    apply EmptySubSet with (theory:= (OLTheory nPnN) ) in CutC.
    apply weakeningGen with (CC':= Gamma) in CutC .
    apply MLLStoSeqN in CutC.   destruct CutC as [h CutC].
    rewrite app_nil_r in CutC.
    assert(HCut1: MLLS (OLTheory nPnN) Gamma ([] ++ N)  ( UP [ (rc_lftBody (rulesC C)) ^])).
    eapply @GeneralCut with  (C:=  rc_rgtBody (rulesC C) ^);eauto. 
    rewrite <- dualInvolutive;eauto.
    
    
    apply MLLStoSeqN in HCut1.  destruct HCut1 as [h2 HCut1].
    eapply @GeneralCut with  (C:= (rc_lftBody (rulesC C)) ^); eauto. 
    rewrite <- dualInvolutive;eauto. sauto.
  Qed.

  (** This is the case when a unary connective is principal in both premises *)
  Theorem UConnectivePrincipalCase :
    forall Gamma M N C F n n',
      (MLLS (OLTheory nPnN) Gamma M (DW (ru_lftBody (rulesU C) F))) ->
      (MLLS (OLTheory nPnN) Gamma N (DW (ru_rgtBody (rulesU C) F))) ->
      (lengthUexp (t_ucon C F) n') ->
      isOLFormula (t_ucon C F) ->
      n' <= n ->
      MLLS (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply MLLStoSeqN in H.     
    apply MLLStoSeqN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize( unCutCo C);intro CutC.
    unfold CutCoherenceUnary in CutC.
    
    generalize (CutC F n1);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply MLLStoSeqN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (th' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (th' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (th' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
    assert(Cut1': MLLS (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[(ru_lftBody (rulesU C) F) ^] )).
    eapply @GeneralCut with(C := (ru_rgtBody (rulesU C) F)  ^) ;eauto.
    
    rewrite <- dualInvolutive;eauto.

    apply MLLStoSeqN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:= (ru_lftBody (rulesU C) F) ^); eauto.
    rewrite <- dualInvolutive;eauto. sauto.
  Qed.
  
  (** This is the case when a binary connective is principal in both premises *)
  Theorem BinConnectivePrincipalCase :
    forall Gamma M N C F G n n',
      (MLLS (OLTheory nPnN) Gamma M (DW (rb_lftBody (rulesB C) F G))) ->
      (MLLS (OLTheory nPnN) Gamma N (DW (rb_rgtBody (rulesB C) F G))) ->
      lengthUexp (t_bcon C F G) n' ->
      isOLFormula (t_bcon C F G) ->
      n' <= n ->
      MLLS (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply MLLStoSeqN in H.     apply MLLStoSeqN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize (biCutCo C);intro CutC.
    unfold CutCoherenceBin in CutC.
    
    generalize (CutC F G n1 n2);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply MLLStoSeqN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (th' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (th' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (th' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
    
    assert(Cut1': MLLS (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[ (rb_lftBody (rulesB C) F G) ^] )).
    eapply @GeneralCut with (C := (rb_rgtBody (rulesB C) F G) ^) ;eauto.
    rewrite <- dualInvolutive;eauto.
 
    apply MLLStoSeqN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:= (rb_lftBody (rulesB C) F G) ^); eauto.     rewrite <- dualInvolutive;eauto.
sauto.
  Qed.

  (** This is the case when a quantifier is principal in both premises *)
  Theorem QuantifierPrincipalCase :
    forall Gamma M N C FX FX0 n n',
      (MLLS (OLTheory nPnN) Gamma M (DW (rq_lftBody (rulesQ C) FX0))) ->
      (MLLS (OLTheory nPnN) Gamma N (DW (rq_rgtBody (rulesQ C) FX))) ->
      isOLFormula (t_qcon C FX) ->
      isOLFormula (t_qcon C FX0) ->
      lengthUexp (t_qcon C FX) n' ->
      uniform FX -> uniform FX0 ->
      lbind 0%nat FX0 = lbind 0%nat FX ->
      n' <= n ->
      MLLS (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
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
    generalize ( quCutCo C) ;intro CutC.
    assert (Hsize: lengthUexp (FX (Var 0%nat)) n0).
    { rewrite H17...  apply proper_VAR.  }
    assert(HIs: (forall t : expr Econ, proper t -> isOLFormula (FX t))).
    {intros t pt. rewrite H12... }
    unfold CutCoherenceQ in *.
    generalize (CutC FX FX0 n0); intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply WeakTheory with (th' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb1.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (th' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheory with (th' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
   
    apply MLLStoSeqN in H.  apply MLLStoSeqN in H0. apply MLLStoSeqN in Cut1.
    destruct H as [h1 H]. 
    destruct H0 as [h2 H0]. destruct Cut1 as [h3 Cut1].
    

    assert(Cut1': MLLS (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[(rq_lftBody (rulesQ C) FX0) ^] )).
    eapply @GeneralCut with  (C := (rq_rgtBody (rulesQ C) FX) ^) ;eauto.
    rewrite <- dualInvolutive;eauto.
    simpl in Cut1'.
    apply MLLStoSeqN in Cut1'.
    destruct Cut1' as [h4 Cut1']. 

    
    eapply @GeneralCut with (C := (rq_lftBody (rulesQ C) FX0) ^) ;eauto.
    rewrite <- dualInvolutive;eauto. sauto.
  Qed.

 (** Inductive hypothesis in the theorem [OLCutElimStep]. This is
  useful to simplify the theorems below *)
  Definition OOCut n' h : Prop :=
    forall n h1 h2 FCut M N Gamma,
      h1 + h2 < h ->
          n' <= n ->
            isOLFormula FCut ->
            lengthUexp FCut n' ->
              posAtomFormulaL M ->
                posAtomFormulaL N ->
                  posAtomFormulaL (second Gamma) ->
                  MLLN (OLTheory nPnN) h1 Gamma (atom (up FCut)::N) (UP [] ) ->
                  MLLN (OLTheory nPnN) h2 Gamma (atom (down FCut)::M) (UP []) -> MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
                  
 Ltac applyOOCut := 
  match goal with
  | [ H: OOCut _ _ |- 
         MLLN ?th ?x ?BX (?FF::?N) (UP []) -> 
         MLLN ?th ?y ?BX (?GG::?M) (UP [])-> 
         MLLS ?thc ?BX (?M++?N) (UP []) ] => eapply H
  | _ => idtac end.
  
Ltac cutOL P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | MLLN ?th ?h1 ?B (atom (up ?FC) :: ?N) (UP []) => 
          match tP2 with 
          | MLLN ?th ?h2 ?B (atom (down ?FC) :: ?M) (UP []) =>  
           match goal with
           | [ H: OOCut ?n' _, Hn: ?n' <= ?n  |- _ ] =>    assert(H': tP1 -> tP2 -> MLLS (OLTheoryCut nPnN (pred n)) B (M++N) (UP []));applyOOCut
           end
           | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto;try OLSolve.
   
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

Ltac unformSeq :=
repeat
  match goal with 
   |[ H: MLLN _ ?n ?G ( (atom ( _ _ ) :: _) ++ _) (UP []) |- _] =>
      try rewrite <- app_comm_cons in H       
   | _ => idtac
end.


 
Ltac PermuteLeft :=    
  match goal with 
     |[ Hr: MLLN _ ?x ?G (?X ++ _) (UP []),   
        Hr': MLLN _ ?x ?G (?X ++ _) (UP []),             
       Hl: MLLN ?th ?n ?G ( (⌈ ?F ⌉) :: _) (UP []),
       Hp: Permutation ?X ((⌊ ?F ⌋) :: _) |- _] =>
   rewrite Hp in Hr, Hr'
   |[ Hr: MLLN _ ?x ?G (?X ++ _) (UP []),   
        Hr': MLLN _ ?x ?G (?X ++ _) (UP []),             
       Hl: MLLN ?th ?n ?G ( (⌊ ?F  ⌋) :: _) (UP []),
       Hp: Permutation ?X ( (⌈ ?F ⌉) :: _)  |- _] =>
   rewrite Hp in Hr, Hr'
   |[ Hr: MLLN _ ?x ?G (?X ++ _) (UP []),               
       Hl: MLLN _ ?n ?G ( (⌈ ?F ⌉) :: _) (UP []),
       Hp: Permutation ?X ((⌊ ?F ⌋) :: _) |- _] =>
       rewrite Hp in Hr
   |[ Hr: MLLN _ ?x ?G (?X ++ _) (UP []),               
       Hl: MLLN _ ?n ?G ( (⌊ ?F ⌋) :: _) (UP []),
       Hp: Permutation ?X ((⌈ ?F ⌉) :: _) |- _] =>
       rewrite Hp in Hr
   | _ => idtac
       end;unformSeq.
       

(** Unary Right is not principal on the left branch *)    
Lemma UnaryRightNotPrincipalL n n' n0 n1 C FCut F Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_ucon C F) ->
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL (second Gamma) ->
buildTheory (makeRRuleU C F) ->
MLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
MLLN (OLTheory nPnN) n1 Gamma ((⌊ FCut ⌋) :: M)
     (DW (makeRRuleU C F)) ->
MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto; try OLSolve.
  intros.
  wellUnary H9.
  * Cases H10.
     - PermuteLeft.
        cutOL H8 H12. 
        OLSolve. 
        rewrite <- app_comm_cons.
        apply H18...
        rewrite Permutation_assoc_comm...
     -  PermuteLeft.
        cutOL H8 H15.
        LLtheory (makeRRuleU C F).
        inversion H13.
        LLtensor (@nil oo) (M++N). eauto.
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
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL (second Gamma) ->
buildTheory (makeLRuleU C F) ->
MLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
MLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeLRuleU C F)) ->
MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellUnary H10.
  * Cases H11.
     - PermuteLeft. 
        cutOL H9 H13.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - PermuteLeft. 
        cutOL H9 H16.
        LLtheory (makeLRuleU C F).
        inversion H14.
        LLtensor (@nil oo) (M++N). eauto.
        apply H20...
        rewrite Permutation_assoc_comm...  
Qed.        

(** Binary Right is not principal on the left branch *) 
Lemma BinaryRightNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bcon C F G) ->
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL (second Gamma) ->
buildTheory (makeRRuleB C F G) ->
MLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
MLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeRRuleB C F G)) ->
MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellBinary H9.
  * Cases H10.
     - PermuteLeft. 
        cutOL H8 H12.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H18...
        rewrite Permutation_assoc_comm...
     - PermuteLeft. 
        cutOL H8 H15.
        LLtheory (makeRRuleB C F G).
        inversion H13.
        LLtensor (@nil oo) (M++N). eauto. 
        apply H19...
        rewrite Permutation_assoc_comm...
  * Cases H10.
     - PermuteLeft.
       cutOL H8 H15.
       rewrite <- H19 in H18.
       rewrite H18 in H4.
       inversion H4...
       OLSolve.
       rewrite <- app_comm_cons.
        rewrite Permutation_assoc_comm...
        apply H20...
        rewrite Permutation_assoc_comm...
        apply MLLNtoSeq in H16...
        apply WeakTheory with (th' := OLTheoryCut nPnN (pred n)) in H16;auto using TheoryEmb1.
    -  PermuteLeft.
        cutOL H8 H16.
       rewrite <- H19 in H18.
       rewrite H18 in H4.
       inversion H4...
       OLSolve.
          rewrite <- app_comm_cons.
        rewrite app_assoc_reverse. 
        apply H20...
        apply MLLNtoSeq in H15...
        apply WeakTheory with (th' := OLTheoryCut nPnN (pred n)) in H15;auto using TheoryEmb1.
        rewrite Permutation_assoc_comm...
    -  PermuteLeft.  
        cutOL H8 H17.
       rewrite <- H20 in H4.
       OLSolve.
        
        rewrite app_assoc_reverse.
        LLtheory (makeRRuleB C F G).
        inversion H12.
        LLtensor (@nil oo) ((x6 ++ N )++ x0).  eauto.
        apply H22...
         rewrite Permutation_assoc_comm...
    apply MLLNtoSeq in H18...
        apply WeakTheory with (th' := OLTheoryCut nPnN (pred n)) in H18;auto using TheoryEmb1.
     -  PermuteLeft.  
        cutOL H8 H18.
       rewrite <- H20 in H4.
       OLSolve.
        LLtheory (makeRRuleB C F G).
        inversion H12.
        LLtensor (@nil oo) (x++(x6 ++ N )). eauto.
        apply H22...
          apply MLLNtoSeq in H17...
        apply WeakTheory with (th' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.       
         rewrite Permutation_assoc_comm...
* Cases H10.
     - PermuteLeft.
       cutOL H8 H15.
       rewrite H18 in H4.
        OLSolve.
        cutOL H8 H16.
       rewrite H18 in H4.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H20...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
      - PermuteLeft.
        cutOL H8 H16.
        cutOL H8 H17.
        LLtheory (makeRRuleB C F G).
        inversion H12.
        LLtensor (@nil oo) (M ++ N). eauto. 
        apply H21...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
Qed.    

(** Unary Left is not principal on the left branch *)  
Lemma BinaryLeftNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
FCut <> t_bcon C F G ->
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bcon C F G) ->
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL (second Gamma) ->
buildTheory (makeLRuleB C F G) ->
MLLN (OLTheory nPnN) (S n0) Gamma ((⌈ FCut ⌉) :: N) (UP []) ->
MLLN (OLTheory nPnN) n1 Gamma ((⌊ FCut ⌋) :: M)
     (DW (makeLRuleB C F G)) ->
MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellBinary H10.
  * Cases H11.
     - PermuteLeft.  
        cutOL H9 H13.
        rewrite H17 in H5.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H9 H16.
        LLtheory (makeLRuleB C F G).
        inversion H14.
        LLtensor (@nil oo) (M++N). eauto.
        apply H20...
        rewrite Permutation_assoc_comm...
  * Cases H11.
     - PermuteLeft.  
        cutOL H9 H16.
        rewrite <- H20 in H19.
        rewrite H19 in H5.
        inversion H5...
        OLSolve.
        rewrite <- app_comm_cons.
        rewrite Permutation_assoc_comm...
        apply H21...
        rewrite Permutation_assoc_comm...
        apply MLLNtoSeq in H17...
        apply WeakTheory with (th' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.
     - PermuteLeft. 
        cutOL H9 H17.
        rewrite <- H20 in H19.
        rewrite H19 in H5.
        inversion H5...
        OLSolve.
        rewrite <- app_comm_cons.
        rewrite app_assoc_reverse. 
        apply H21...
        apply MLLNtoSeq in H16...
        apply WeakTheory with (th' := OLTheoryCut nPnN (pred n)) in H16;auto using TheoryEmb1.
        rewrite Permutation_assoc_comm...
     - PermuteLeft.
       cutOL H9 H18.
       rewrite <- H21 in H5.
       OLSolve.
       rewrite Permutation_assoc_comm...
       LLtheory  (makeLRuleB C F G).
       inversion H13.
       LLtensor (@nil oo) ((x6 ++ N) ++ x0). eauto.
       apply H23...
       rewrite Permutation_assoc_comm...
       apply MLLNtoSeq in H19...
       apply WeakTheory with (th' := OLTheoryCut nPnN (pred n)) in H19;auto using TheoryEmb1.
     - PermuteLeft.  
        cutOL H9 H19.
        rewrite <- H21 in H5.
        OLSolve.
        rewrite app_assoc_reverse.
         LLtheory  (makeLRuleB C F G).
       inversion H13.
       LLtensor (@nil oo) (x++(x6 ++ N)). eauto.
        apply H23...
        apply MLLNtoSeq in H18...
        apply WeakTheory with (th' := OLTheoryCut nPnN (pred n)) in H18;auto using TheoryEmb1.
         rewrite Permutation_assoc_comm...
  * Cases H11.
     - PermuteLeft.  
        cutOL H9 H16.
        rewrite H19 in H5.
        OLSolve.
        cutOL H9 H17.
        rewrite H19 in H5.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H21...
        1-2: rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H9 H17.
        cutOL H9 H18.
         LLtheory  (makeLRuleB C F G).
       inversion H13.
       LLtensor (@nil oo) (M++N). eauto.      
        apply H22...
        1-2: rewrite Permutation_assoc_comm... 
 Qed.     

 (** Quantifier Right is not principal on the left branch *) 
 Lemma QuantifierRightNotPrincipalL n n' n0 n1 C FCut FX Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_qcon C FX) ->
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL (second Gamma) ->
buildTheory (makeRRuleQ C FX) ->
MLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
MLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeRRuleQ C FX)) ->
MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellQuantifier H9.
  * Cases H10.
     - PermuteLeft.  
        cutOL H8 H12.
        rewrite H16 in H4.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H18...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H8 H15.
        LLtheory (makeRRuleQ C FX).
        inversion H13.
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
        rewrite Permutation_assoc_comm...
Qed.

 (** Quantifier Left is not principal on the left branch *) 
 Lemma QuantifierLeftNotPrincipalL n n' n0 n1 C FCut FX Gamma M N: 
 FCut <> t_qcon C FX -> 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_qcon C FX) ->
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL (second Gamma) ->
buildTheory (makeLRuleQ C FX) ->
MLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
MLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeLRuleQ C FX)) ->
MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellQuantifier H10.
  * Cases H11.
     - PermuteLeft.  
        cutOL H9 H13.
        rewrite H17 in H5.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H9 H16.
        LLtheory (makeLRuleQ C FX).
        inversion H14.
        LLtensor (@nil oo) (M++N). eauto.
        apply H20...
        rewrite Permutation_assoc_comm... 
 Qed.       
        
 
Ltac permuteUnary :=
match goal with
| [H: ?n' <= ?n,
   Hl: MLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : MLLN _ _ _ (_ :: ?M) (DW (makeRRuleU _ _))
  |-  MLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (UnaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: MLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : MLLN _ _ _ (_ :: ?M) (DW (makeLRuleU _ _))
  |-  MLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (UnaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.     

 
Ltac permuteBinary :=
match goal with
| [H: ?n' <= ?n,
   Hl: MLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : MLLN _ _ _ (_ :: ?M) (DW (makeRRuleB _ _ _))
  |-  MLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (BinaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: MLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : MLLN _ _ _ (_ :: ?M) (DW (makeLRuleB _ _ _))
  |-  MLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (BinaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    
 
 Ltac permuteQuantifier :=
match goal with
| [H: ?n' <= ?n,
   Hl: MLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : MLLN _ _ _ (_ :: ?M) (DW (makeRRuleQ _ _))
  |-  MLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (QuantifierRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: MLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : MLLN _ _ _ (_ :: ?M) (DW (makeLRuleQ _ _))
  |-  MLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (QuantifierLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    
       
Ltac Cases' H := destruct H;sauto;SubCases.

 Lemma dualRev F G: F = dual G -> G = dual F.
 Proof with sauto.
 intros.
 rewrite H...
 rewrite <- dualInvolutive...
 Qed.
 
Lemma ConstantRIGHT n n' n0 n1  C FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_ccon C) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
  MLLN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ((⌈ FCut ⌉) :: N) (DW (makeRRuleC C)) ->
  MLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleC C) ->
  buildTheory F0 ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellConstant Hseq1'.
  * Cases H. 
     2:{ LLPerm ((⌈ t_ccon C ⌉) :: x0++M)... }
    rewrite <- H4 in H2.
    clear H4.
    inversion Hth'...
           -- wellConstant Hseq2'.   
               Cases H0.
               rewrite <- app_comm_cons...
              eapply H7 with (a:=x)...
               Cases H0. 
               PermuteLeft.
               cutOL Hseq1 H4.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H10...
               LLPerm ((x3 ++ x) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H7.
               LLtheory (makeRRuleC C0).
               inversion H5.
               LLtensor (@nil oo) (M++N). eauto.
               apply H11...
               LLPerm ( (M ++ x) ++ N)...
           -- wellConstant Hseq2'.   
               Cases H0.
               2:{ rewrite <- app_comm_cons... }
               rewrite <- H7 in H5.
               rewrite Permutation_app_comm.
               apply WeakTheory with (th := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H5 H2).
            eapply H7 with (a:=x)...
              
               Cases H0. 
              rewrite <- H9 in H6.
               rewrite Permutation_app_comm.
               apply WeakTheory with (th := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H6 H2).
               PermuteLeft.
               cutOL Hseq1 H4.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H10...
               LLPerm ((x3 ++ x) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H7.
               LLtheory (makeLRuleC C0).
               inversion H5.
               LLtensor (@nil oo) (M++N). eauto.
               apply H11...
               LLPerm ( (M ++ x) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.
           -- permuteQuantifier.
           -- eapply H4 with (a:=x)...
(** 1.2 ONE PREMISSE *)        
  * Cases H.
     2:{
       PermuteLeft.
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ((⌈ t_ccon C ⌉) ::(M++ x3))...
         apply H7...
         rewrite app_assoc_reverse... }
     2:{  PermuteLeft.
               cutOL H4 Hseq2.
               LLtheory (makeRRuleC C).
               inversion H2.
               LLtensor (@nil oo) (M++N). eauto.
               apply H8...
               rewrite app_assoc_reverse... }

         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H2. 
               rewrite <- app_comm_cons...
eapply H11 with (a:=x3)...
              
           -- Cases H2. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               apply H14...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H11.
               LLtheory (makeRRuleC C0).
               inversion H9.
               LLtensor (@nil oo) (M++N). eauto.
               apply H15...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H2. 
               rewrite <- H11 in H9.
               rewrite <- H6 in H3.
               rewrite Permutation_app_comm.
               apply WeakTheory with (th := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H9 H3).
               
               rewrite <- app_comm_cons...
               eapply H11 with (a:=x3)...
              
           -- Cases H2. 
               rewrite <- H13 in H10.
               rewrite <- H6 in H3.
               rewrite Permutation_app_comm.
               apply WeakTheory with (th := OLTheory nPnN ). auto using TheoryEmb1.
               refine (ConstantPrincipalCase _ H10 H3).
               
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               apply H14...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H11.
               LLtheory (makeLRuleC C0).
               inversion H9.
               LLtensor (@nil oo) (M++N). eauto.
               apply H15...
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
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n0) Gamma  ( (⌈ FCut ⌉) ::N) (UP []) ->
  MLLN (OLTheory nPnN) (S n1)  Gamma ( (⌊ FCut ⌋) ::M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleU C F)) ->
  MLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleU C F) ->
  buildTheory F0 ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellUnary Hseq1'.
  * Cases H.
     2:{  PermuteLeft.
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ((⌈ t_ucon C F ⌉) ::(M++ x3))...
         apply H7...
         rewrite app_assoc_reverse... }
     2:{ PermuteLeft. 
        cutOL H4 Hseq2.
               LLtheory (makeRRuleU C F).
               inversion H2.
               LLtensor (@nil oo) (M++N). eauto.
               apply H8...
               rewrite app_assoc_reverse... }
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H2. 
               rewrite <- app_comm_cons...
             eapply H11 with (a:=x3)...
              
           -- Cases H2. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               apply H14...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H11.
               LLtheory (makeRRuleC C0).
               inversion H9.
               LLtensor (@nil oo) (M++N). eauto.
               apply H15...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H2. 
              rewrite <- app_comm_cons...
              eapply H11 with (a:=x3)...
           -- Cases H2. 
              PermuteLeft. 
              cutOL Hseq1 H8.
               rewrite H12 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H14...
               rewrite Permutation_assoc_comm...
              PermuteLeft.
              cutOL Hseq1 H11.
                 LLtheory (makeLRuleC C0).
                 inversion H9.
             LLtensor (@nil oo) (M++N). eauto.
               apply H15...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - wellUnary Hseq2'.
            Cases H2. 
            
            rewrite <- H6 in H3. 
            rewrite <- H13 in H10. 
            rewrite Permutation_app_comm.
            refine(UConnectivePrincipalCase _ H3 _ _ HL')...
             PermuteLeft. 
              cutOL Hseq1 H8.
               rewrite H12 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H14...
               rewrite Permutation_assoc_comm...
              
PermuteLeft.
              cutOL Hseq1 H11.
                 LLtheory (makeLRuleU C0 F1).
                 inversion H9.
             LLtensor (@nil oo) (M++N). eauto.
               apply H15...  
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
  isOLFormula (t_bcon C F G) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
  MLLN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleB C F G)) ->
  MLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) ::M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleB C F G) ->
  buildTheory F0 ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
Admitted.
(*   intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellBinary Hseq1'.
  * Cases H. 
     2:{ apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite H in H3.
         rewrite <- app_comm_cons in H3 . 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ( (⌈ t_bcon C F G ⌉) ::(M++ x4))...
         apply H8...
         rewrite app_assoc_reverse... }
   2:{ apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite <- app_comm_cons in H4. 
         cutOL H4 Hseq2.
         1-2: OLSolve.
        LLtheory (makeRRuleB C F G).
               inversion H.
               LLtensor (@nil oo) (M++N).
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
               LLtheory (makeRRuleC C0).
               inversion H1.
               LLtensor (@nil oo) (M++N).
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
                 LLtheory (makeLRuleC C0).
                 inversion H1.
             LLtensor (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellBinary Hseq2'.
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
                 LLtheory (makeLRuleB C0 F1 G0).
                 inversion H1.
             LLtensor (@nil oo) (M++N).
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
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x13 ++ N) ++ x5).
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
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: x4++(x13 ++ N)).
              apply H19...
              apply seqNtoSeq in H14...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H15. 
               1-2: OLSolve.
               rewrite <- H18 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
                 inversion H1.
             LLtensor (@nil oo) ( ((x12 ++ N) ++ x5)).
               apply H20...  
               rewrite Permutation_assoc_comm...
               apply seqNtoSeq in H16...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H16. 
               1-2: OLSolve.
               rewrite <- H18 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
                 inversion H1.
             LLtensor (@nil oo) (x4++(x12 ++ N) ).
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
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x11 ++ N) ).
              apply H19...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H15.
               1-2: OLSolve.
             cutOL Hl' H16.
               1-2: OLSolve.
             LLtheory (makeLRuleB C0 F1 G0).
                 inversion H1.
             LLtensor (@nil oo) (M ++ N).
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
         LLPerm ( (⌈ t_bcon C F G ⌉) ::(M++ x8)++x0)...
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
        LLPerm ( (⌈ t_bcon C F G ⌉) ::x++(M++ x8))...
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
         LLtheory (makeRRuleB C F G).
               inversion H.
               LLtensor (@nil oo) ((M ++ x7)++x0).
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
         LLtheory (makeRRuleB C F G).
               inversion H.
               LLtensor (@nil oo) (x++(M ++ x7)).
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
               LLtheory (makeRRuleC C0).
               inversion H5.
               LLtensor (@nil oo) (M++N).
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
                 LLtheory (makeLRuleC C0).
                 inversion H5.
             LLtensor (@nil oo) (M++N).
               apply H19...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellBinary Hseq2'.
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
                 LLtheory (makeLRuleB C0 F1 G0).
                 inversion H5.
             LLtensor (@nil oo) (M++N).
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
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x16 ++ N) ++ x8).
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
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: x7++(x16 ++ N)).
              apply H22...
              apply seqNtoSeq in H17...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H18. 
               1-2: OLSolve.
               rewrite <- H21 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
                 inversion H5.
             LLtensor (@nil oo) ( ((x15 ++ N) ++ x8)).
               apply H23...  
               rewrite Permutation_assoc_comm...
               apply seqNtoSeq in H19...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H19. 
               1-2: OLSolve.
               rewrite <- H21 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
                 inversion H5.
             LLtensor (@nil oo) (x7++(x15 ++ N) ).
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
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x14 ++ N) ).
              apply H22...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H18.
               1-2: OLSolve.
             cutOL Hl' H19.
               1-2: OLSolve.
             LLtheory (makeLRuleB C0 F1 G0).
                 inversion H5.
             LLtensor (@nil oo) (M ++ N).
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
         
         LLPerm ((⌈ t_bcon C F G ⌉) ::M++ x6)...
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
         LLtheory (makeRRuleB C F G).
               inversion H.
               LLtensor (@nil oo) (M ++N).
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
               LLtheory (makeRRuleC C0).
               inversion H5.
               LLtensor (@nil oo) (M++N).
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
                 LLtheory (makeLRuleC C0).
                 inversion H5.
             LLtensor (@nil oo) (M++N).
               apply H19...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellBinary Hseq2'.
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
                 LLtheory (makeLRuleB C0 F1 G0).
                 inversion H5.
             LLtensor (@nil oo) (M++N).
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
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x15 ++ N) ++ x7).
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
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: x6++(x15 ++ N)).
              apply H22...
              apply seqNtoSeq in H17...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H18. 
               1-2: OLSolve.
               rewrite <- H21 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
                 inversion H5.
             LLtensor (@nil oo) ( ((x14 ++ N) ++ x7)).
               apply H23...  
               rewrite Permutation_assoc_comm...
               apply seqNtoSeq in H19...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H19. 
               1-2: OLSolve.
               rewrite <- H21 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
                 inversion H5.
             LLtensor (@nil oo) (x6++(x14 ++ N) ).
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
            LLPerm ((⌊ t_bcon C0 F1 G0 ⌋) :: (x13 ++ N) ).
              apply H22...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H18.
               1-2: OLSolve.
             cutOL Hl' H19.
               1-2: OLSolve.
             LLtheory (makeLRuleB C0 F1 G0).
                 inversion H5.
             LLtensor (@nil oo) (M ++ N).
               apply H23...
            1-2:  rewrite Permutation_assoc_comm... }
                           
          - permuteQuantifier.
         - permuteQuantifier.         
  Qed.                        
   
 *)

Lemma QuantifierRIGHT n n' n0 n1  C FX FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_qcon C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n0)  Gamma ( (⌈ FCut ⌉) ::N) (UP []) ->
  MLLN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleQ C FX)) ->
  MLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleQ C FX) ->
  buildTheory F0 ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellQuantifier Hseq1'.
  Cases H. 
  2:{ PermuteLeft. 
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ( (⌈ t_qcon C FX ⌉) ::(M++ x3))...
         apply H7...
         rewrite app_assoc_reverse... }
  2:{ PermuteLeft. 
         cutOL H4 Hseq2.
         LLtheory (makeRRuleQ C FX).
         inversion H2.
         LLtensor (@nil oo) (M++N). eauto.
         apply H8...
         rewrite app_assoc_reverse... }         
    inversion Hth'... 
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
               eapply H11 with (a:=x3)... Cases H2. 
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H14...
               LLPerm ((x7 ++ x3) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H11.
               LLtheory (makeRRuleC C0).
               inversion H9.
               LLtensor (@nil oo) (M++N). eauto.
               apply H15...
               LLPerm ( (M ++ x3) ++ N)...
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...
eapply H11 with (a:=x3)...
               Cases H2. 
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H14...
               LLPerm ((x7 ++ x3) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H11.
               LLtheory (makeLRuleC C0).
               inversion H9.
               LLtensor (@nil oo) (M++N). eauto.
               apply H15...
               LLPerm ( (M ++ x3) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.           
           -- wellQuantifier Hseq2'.
               destruct H2...
               checkPermutationCases H2.
               inversion H12...
               rewrite <- H6 in H3.
               rewrite <- H13 in H10.
               rewrite Permutation_app_comm.
               refine (QuantifierPrincipalCase H10 H3 _ _ _ _ _ _ HL')...   
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               rewrite H12.
               LLPerm ( (⌊t_qcon C0 FX0 ⌋) :: x7++ N).
               apply H14...
               LLPerm ((x7 ++ x3) ++ N)...
               
               PermuteLeft.
               cutOL Hseq1 H11.
              LLtheory (makeLRuleQ C0 FX0).
               inversion H9.
               LLtensor (@nil oo) (M++N). eauto.
               apply H15...
               LLPerm ((M ++ x3) ++ N)...
     Qed.         
             
Definition ConnectiveLeft connective rule := forall n n' n0 n1  FCut M N Gamma,
  n' <= n ->
  isOLFormula connective ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW rule) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory rule ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
     

             
Lemma ConstantLEFT n n' n0 n1  C FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_ccon C) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleC C)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleC C) ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellConstant Hseq1'.
  * Cases H. 
     + LLPerm ( (⌊ t_ccon C ⌋) :: x0++M)...
     + eauto. 
  * Cases H. 
     + PermuteLeft.  
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ( (⌊ t_ccon C ⌋) ::(M++ x3)).
         apply H7...
         LLPerm(M ++ x3 ++ x)...
    + PermuteLeft.   
         cutOL H4 Hseq2.
         LLtheory (makeLRuleC C).
         inversion H2.
         LLtensor (@nil oo) (M++N). eauto.
         apply H8... 
         LLPerm(M ++ N ++ x)...
Qed.                  
         
 Lemma UnaryLEFT n n' n0 n1 C F FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_ucon C F) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n1) Gamma  ( (⌊ FCut ⌋) :: M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleU C F)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleU C F) ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellUnary Hseq1'.
  * Cases H. 
     + PermuteLeft.  
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ( (⌊ t_ucon C F ⌋) ::(M++ x3)).
         apply H7...
         LLPerm(M ++ x3 ++ x)...
     + PermuteLeft.  
         cutOL H4 Hseq2.
         LLtheory (makeLRuleU C F).
         inversion H2.
         LLtensor (@nil oo) (M++N). eauto.
         apply H8... 
         LLPerm(M ++ N ++ x)...
Qed.       

 Lemma BinaryLEFT n n' n0 n1 C F G FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_bcon C F G) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleB C F G)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleB C F G) ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellBinary Hseq1'.
  * Cases H. 
Admitted.
 (*     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite H in H3. 
         rewrite <- app_comm_cons in H3. 
         cutOL H3 Hseq2.
         1-2: OLSolve.
         OLSolve.
         LLPerm ( (⌊t_bcon C F G ⌋) ::(M++ x4)).
         apply H8...
         LLPerm(M ++ x4 ++ x)...
     + apply weakeningGenN_rev with (CC':= x0) in Hseq2. 
         rewrite <- app_comm_cons in H4. 
         cutOL H4 Hseq2.
         1-2: OLSolve.
         LLtheory (makeLRuleB C F G).
         inversion H.
         LLtensor (@nil oo) (M++N).
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
         LLPerm ((⌊ t_bcon C F G ⌋) :: (M++x8) ++ x0).
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
         LLPerm ( (⌊ t_bcon C F G ⌋) :: x++(M++x8)).
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
         LLtheory  (makeLRuleB C F G).
         inversion H.
         LLtensor (@nil oo) ((M ++ x7) ++ x0).
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
         LLtheory  (makeLRuleB C F G).
         inversion H.
         LLtensor (@nil oo) (x++(M ++ x7)).
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
         LLPerm ( (⌊ t_bcon C F G ⌋) :: M++x6).
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
         LLtheory (makeLRuleB C F G). 
         inversion H.
         LLtensor (@nil oo) (M++N).
         apply H12...
         1-2: rewrite app_assoc_reverse... 
Qed.         
  *)        
 
Lemma QuantifierLEFT n n' n0 n1 C FX FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_qcon C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL (second Gamma) ->
  MLLN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  MLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleQ C FX)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleQ C FX) ->
  MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellQuantifier Hseq1'.
  * Cases H. 
     + PermuteLeft.  
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ( (⌊ t_qcon C FX ⌋) ::(M++ x3)).
         apply H7...
         LLPerm(M ++ x3 ++ x)...
     + PermuteLeft.  
         cutOL H4 Hseq2.
         LLtheory (makeLRuleQ C FX).
         inversion H2.
         LLtensor (@nil oo) (M++N). eauto.
         apply H8... 
         LLPerm(M ++ N ++ x)...
Qed.
 
 (** Main theorem showing that it is possible to fins a proof with
  the theory [ (OLTheoryCut nPnN (pred n))] *)
  Theorem OLCutElimStep :
    forall h1 h2 n N M Gamma FCut n',
      isOLFormula FCut ->
      posAtomFormulaL (second Gamma) ->
      posAtomFormulaL N ->
      posAtomFormulaL M ->
      MLLN (OLTheory nPnN) h1 Gamma ( atom(up FCut)::N) (UP []) ->
      MLLN (OLTheory nPnN) h2 Gamma (atom (down FCut)::M) (UP []) ->
      lengthUexp FCut n' -> n'<=n ->
      (MLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP [])) .
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
       refine (onlyAtomsClassical _ _  _ H2 H3)...
  assert(In (i,F) Gamma).
   rewrite <- H3 ...
 apply onlyAtomsClassical in H5...

   inversion Hseq2...

   
cut(False);intros...
       refine (onlyAtomsLinear _ H3 H4)... 

  cut(False);intros...
 apply onlyAtomsClassical in H6...
  assert(In (i,F0) Gamma).
   rewrite <- H6 ...
 apply onlyAtomsClassical in H8...

    assert(OOCut n' (S n0 + S n1)).
    {
    unfold OOCut; intros.
    revert H13 H14.
    eapply H with  (m:=h1 + h2)... }
    clear H.
    rename n0 into h1.
    rename n1 into h2.
   (* Now we proceed by cases on the last rule applied on both derivations *)
    inversion H0 ;inversion H3...
   all: try match goal with
    | H: neg nPnN |- _ => inversion H 
    | H: pos nPnN |- _ => inversion H 
    end.
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
          apply MLLNtoSeq in Hseq1.
          apply WeakTheory with (th := OLTheory nPnN )... 
        - inversion H5...
           apply absorptionInN with (i:=x) in Hseq1...
          apply MLLNtoSeq in Hseq1.
          apply WeakTheory with (th := OLTheory nPnN )... 
    * apply FocusingInitRuleU in H2...
       - checkPermutationCases H7. 
          inversion H9...
          apply MLLNtoSeq in Hseq2.
          apply WeakTheory with (th := OLTheory nPnN )... 
         LLExact Hseq2.
        - inversion H2...
           apply absorptionInN with (i:=x) in Hseq2...
          apply MLLNtoSeq in Hseq2.
          apply WeakTheory with (th := OLTheory nPnN )... 
    * apply FocusingInitRuleU in H2...
       - checkPermutationCases H7. 
          inversion H9...
          apply MLLNtoSeq in Hseq2.
          apply WeakTheory with (th := OLTheory nPnN )... 
         LLExact Hseq2.
        - inversion H2...
           apply absorptionInN with (i:=x) in Hseq2...
          apply MLLNtoSeq in Hseq2.
          apply WeakTheory with (th := OLTheory nPnN )... 
 Qed.                   
         
  Theorem OLCutElimAux :
    forall n h  B N ,
      posAtomFormulaL (second B) ->
      posAtomFormulaL N ->
      MLLN  (OLTheoryCut nPnN n) h  B N (UP[] ) ->
      MLLS  (OLTheoryCut nPnN 0) B N (UP[] ) .
  Proof with sauto;try OLSolve.
  induction n ; induction h using lt_wf_ind; intros *;intros isFB isFN Hh.
    * eapply MLLNtoSeq;eauto.
    * inversion Hh...
      cut(False);intros...
      apply onlyAtomsLinear in H1...
      cut(False);intros...
      apply onlyAtomsClassical in H3...
      apply onlyAtomsClassical2 in H3...
       inversion H0...
       inversion H3...
       inversion H4...
      + (* constant *)
         wellConstant H2.
         Cases H6.
         apply H10... eauto.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeRRuleC C).
         LLtensor (@nil oo) N. eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* constant *)
         wellConstant H2.
         Cases H6.
         apply H10... eauto.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeLRuleC C).
         LLtensor (@nil oo) N. eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* unary *)
         wellUnary H2.
         Cases H6.
         apply H14... 
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeRRuleU C F0).
         LLtensor (@nil oo) N. eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* unary *)
         wellUnary H2.
         Cases H6. 
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeLRuleU C F0).
         LLtensor (@nil oo) N.  eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* binary *)
         wellBinary H2.
         { Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeRRuleB C F0 G).
         LLtensor (@nil oo) N. eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)... }
         { Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         OLSolve.
         rewrite H10 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H12)...
         rewrite H10 in isFN.
         inversion isFN...
         LLtheory (makeRRuleB C F0 G).
         LLtensor (@nil oo) N. eauto.
         rewrite H10.
         apply H18...
         refine (H _ _ _ _ _ _ H13)... 
         rewrite H10 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H14)... 
         rewrite H10 in isFN.
         inversion isFN... }
         { Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         OLSolve.
         rewrite H10 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H12)...
         LLtheory (makeRRuleB C F0 G).
         LLtensor (@nil oo) N. eauto.
         apply H17...
         refine (H _ _ _ _ _ _ H12)... 
         refine (H _ _ _ _ _ _ H13)...  } 
      + (* binary *)
         wellBinary H2.
         { Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeLRuleB C F0 G).
         LLtensor (@nil oo) N.  eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)... }
         { Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         rewrite H10 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H12)...
         rewrite H10 in isFN.
         inversion isFN...
         LLtheory (makeLRuleB C F0 G).
         LLtensor (@nil oo) N. eauto.
         rewrite H10.
         apply H18...
         refine (H _ _ _ _ _ _ H13)... 
         rewrite H10 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H14)... 
         rewrite H10 in isFN.
         inversion isFN... }
         { Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         rewrite H10 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H12)...
         rewrite H10 in isFN.
         inversion isFN...
         LLtheory (makeLRuleB C F0 G).
         LLtensor (@nil oo) N. eauto.
         apply H17...
         refine (H _ _ _ _ _ _ H12)... 
         refine (H _ _ _ _ _ _ H13)...  } 
      + (* quantifier *)
         wellQuantifier H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeRRuleQ C FX).
         LLtensor (@nil oo) N.  eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* quantifier *)
         wellQuantifier H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeLRuleQ C FX).
         LLtensor (@nil oo) N.  eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* init *)
         apply FocusingInitRuleU in H2...
         rewrite H5.
         LLtheory (RINIT OO).
         LLtensor [ (⌈ OO ⌉)] [(⌊ OO ⌋)].
         LLtheory (RINIT OO).
         LLtensor [ (⌈ OO ⌉)] (@nil oo). eauto.
         LLtheory (RINIT OO).
         LLtensor (@nil oo) [ (⌊ OO ⌋)].  eauto.
         LLtheory (RINIT OO).
         LLtensor.  eauto.  eauto.
      + inversion f.
     + inversion f. 
      + (* cut *)
          inversion H3... 2:{ firstorder. }
         inversion H2...
         2:{ inversion H8. }
         invTri H17.
         invTri H18.
         invTri H19.
         invTri H20.
         clearPolarity.
         apply SETXempty in H12,H13... 
         rewrite <- H10 in H22, H23.
         clear H11 H10.
         apply H in H22...
         2: repeat OLSolve. 
         apply H in H23...
         2: repeat OLSolve. 
         apply WeakTheory with (th' := OLTheory nPnN) in H22, H23;auto;try apply OOTheryCut0.
         rewrite H9.
         apply WeakTheory with (th := OLTheory nPnN).
         apply OOTheryCut0.
  
         destruct m.
         generalize(LengthFormula H4 H5);intro;lia.
         assert (MLLS (OLTheoryCut nPnN (pred  (S (n)))) B (M ++ N0) (UP [])) .
         rewrite Permutation_app_comm.
         apply MLLStoSeqN in H22, H23...
         refine(OLCutElimStep _ _ _ _ H22 H23 H5 _)...
        simpl in H7...
       apply MLLStoSeqN in H7...
        apply IHn in H7...
        apply WeakTheory with (th' := OLTheory nPnN) in H7;auto;try apply  OOTheryCut0.
+ solveSignature1. 
Qed.
         (** Cut-elimination theorem for Object Logics satisfying cut-]
  coherence *)
  Theorem OLCutElimination :
    forall n h  B N ,
      posAtomFormulaL (second B) ->
      posAtomFormulaL N ->
      MLLN (OLTheoryCut nPnN n) h  B N (UP [] ) ->
      MLLS (OLTheory nPnN) B N (UP [] ) .
  Proof with sauto.
    intros. 
    apply OLCutElimAux in H1 ...
    eapply WeakTheory with (th':= OLTheory nPnN) in H1 ...
    apply OOTheryCut0.
  Qed.     
  
End CutElimination.
