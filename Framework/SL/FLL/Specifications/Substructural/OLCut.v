
(** * LL as a Meta-logical framework.  *)

(** In this file we show how the cut-elimination procedure for FLL can
be used to prove cut-elimination for object logics that are
cut-coherent in the sense of Miller & Pimentel. Roughly, a system is
cut-coherent if the encoding of the right and left rules of each
connective are dual. *)

Require Export LL.Misc.Hybrid.
Require Export LL.Framework.SL.FLL.Specifications.StructuralClauses. 

Require Export LL.Framework.SL.FLL.Specifications.Requirement1.

Require Export LL.Framework.SL.FLL.Specifications.OLTheory.

Require Import Coq.Init.Nat.
Require Import LL.Framework.SL.FLL.CutElimination.
Require Import LL.Framework.SL.FLL.Reasoning.
Require Import LL.Framework.OL.SyntaxResults.

Import LL.Misc.Permutations.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


(** ** Cut Elimination Procedure *)
Section CutElimination .

  Context `{OLR: OORules}.
 
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
    | FLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C)) =>
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
    | (FLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
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
    | (FLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F ?G))) =>
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
    | (FLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with makeRRuleQ => Right | makeLRuleQ => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
         let HUniform := fresh "HUniform" in
        generalize  (quWellFormed Rules Gamma M C Side' F); intro LTWell';
      generalize (LTWell' _ HSeq); intro;clear LTWell'  
    end.

Definition EmptyTheory (F :oo) := False.

Lemma EmptySubSetN : forall (theory : oo-> Prop) CC LC X n,
      FLLN EmptyTheory n CC LC X -> FLLN theory n CC LC X.
Proof.    
  intros.
  apply WeakTheoryN with (theory:= EmptyTheory);auto.
  intros.
  inversion H0.
Qed.
  
Lemma EmptySubSet : forall (theory : oo-> Prop) CC LC X,
      FLLS EmptyTheory CC LC X -> FLLS theory CC LC X.
Proof.
  intros.
  apply WeakTheory with (theory:= EmptyTheory);auto.
  intros.
  inversion H0.
Qed.


 (** This is the case when a constant is principal in both premises *)
  Theorem ConstantPrincipalCase :
    forall Gamma M N C,
      (FLLS (OLTheory nPnN) Gamma M (DW (rc_lftBody (rulesC C)))) ->
      (FLLS (OLTheory nPnN) Gamma N (DW (rc_rgtBody (rulesC C)))) ->
      FLLS (OLTheory nPnN) Gamma (N ++ M) (UP []).
 Proof with sauto.     
    intros.
    apply  FLLStoFLLN in H... 
    apply FLLStoFLLN in H0...
    generalize( ctCutCo C);intro CutC.
    unfold CutCoherenceC in CutC.
    destruct CutC as [Hc CutC].
    apply EmptySubSet with (theory:= (OLTheory nPnN) ) in CutC.
    apply weakeningGen with (CC':= Gamma) in CutC .
    apply FLLStoFLLN in CutC.   destruct CutC as [h CutC].
    rewrite app_nil_r in CutC.
    assert(HCut1: FLLS (OLTheory nPnN) Gamma ([] ++ N)  ( UP [dual (rc_lftBody (rulesC C))])).
    eapply @GeneralCut with  (C:=  dual (rc_rgtBody (rulesC C) ));eauto. 
    rewrite <- dualInvolutive;eauto.
    
    
    apply FLLStoFLLN in HCut1.  destruct HCut1 as [h2 HCut1].
    eapply @GeneralCut with  (C:=dual (rc_lftBody (rulesC C)) ); eauto. 
    rewrite <- dualInvolutive;eauto.   Qed.

  (** This is the case when a unary connective is principal in both premises *)
  Theorem UConnectivePrincipalCase :
    forall Gamma M N C F n n',
      (FLLS (OLTheory nPnN) Gamma M (DW (ru_lftBody (rulesU C) F))) ->
      (FLLS (OLTheory nPnN) Gamma N (DW (ru_rgtBody (rulesU C) F))) ->
      (lengthUexp (t_ucon C F) n') ->
      isOLFormula (t_ucon C F) ->
      n' <= n ->
      FLLS (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply FLLStoFLLN in H.     
    apply FLLStoFLLN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize( unCutCo C);intro CutC.
    unfold CutCoherenceU in CutC.
    
    generalize (CutC F n1);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply FLLStoFLLN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
    assert(Cut1': FLLS (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[dual(ru_lftBody (rulesU C) F) ] )).
    eapply @GeneralCut with(C :=dual (ru_rgtBody (rulesU C) F)  ) ;eauto.
    
    rewrite <- dualInvolutive;eauto.

    apply FLLStoFLLN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:=dual (ru_lftBody (rulesU C) F) ); eauto.
    rewrite <- dualInvolutive;eauto. 
  Qed.
  
  (** This is the case when a binary connective is principal in both premises *)
  Theorem BinConnectivePrincipalCase :
    forall Gamma M N C F G n n',
      (FLLS (OLTheory nPnN) Gamma M (DW (rb_lftBody (rulesB C) F G))) ->
      (FLLS (OLTheory nPnN) Gamma N (DW (rb_rgtBody (rulesB C) F G))) ->
      lengthUexp (t_bcon C F G) n' ->
      isOLFormula (t_bcon C F G) ->
      n' <= n ->
      FLLS (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply FLLStoFLLN in H.     apply FLLStoFLLN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize (biCutCo C);intro CutC.
    unfold CutCoherenceB in CutC.
    
    generalize (CutC F G n1 n2);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply FLLStoFLLN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
    
    assert(Cut1': FLLS (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[dual (rb_lftBody (rulesB C) F G) ] )).
    eapply @GeneralCut with (C := dual(rb_rgtBody (rulesB C) F G) ) ;eauto.
    rewrite <- dualInvolutive;eauto.
 
    apply FLLStoFLLN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:= dual(rb_lftBody (rulesB C) F G) ); eauto.     rewrite <- dualInvolutive;eauto.
  Qed.

  (** This is the case when a quantifier is principal in both premises *)
  Theorem QuantifierPrincipalCase :
    forall Gamma M N C FX FX0 n n',
      (FLLS (OLTheory nPnN) Gamma M (DW (rq_lftBody (rulesQ C) FX0))) ->
      (FLLS (OLTheory nPnN) Gamma N (DW (rq_rgtBody (rulesQ C) FX))) ->
      isOLFormula (t_qcon C FX) ->
      isOLFormula (t_qcon C FX0) ->
      lengthUexp (t_qcon C FX) n' ->
      uniform FX -> uniform FX0 ->
      lbind 0%nat FX0 = lbind 0%nat FX ->
      n' <= n ->
      FLLS (OLTheoryCut nPnN (pred n)) Gamma (N ++ M) (UP []).
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
    apply WeakTheory with (theory' := OLTheoryCut nPnN n) in Cut1;auto using TheoryEmb1.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (theory' := OLTheoryCut nPnN n) in H;auto using TheoryEmb1.
    apply WeakTheory with (theory' := OLTheoryCut nPnN n) in H0;auto using TheoryEmb1.
   
    apply FLLStoFLLN in H.  apply FLLStoFLLN in H0. apply FLLStoFLLN in Cut1.
    destruct H as [h1 H]. 
    destruct H0 as [h2 H0]. destruct Cut1 as [h3 Cut1].
    

    assert(Cut1': FLLS (OLTheoryCut nPnN n) Gamma ([] ++ N) ( UP[dual(rq_lftBody (rulesQ C) FX0) ] )).
    eapply @GeneralCut with  (C :=dual (rq_rgtBody (rulesQ C) FX) ) ;eauto.
    rewrite <- dualInvolutive;eauto.
    simpl in Cut1'.
    apply FLLStoFLLN in Cut1'.
    destruct Cut1' as [h4 Cut1']. 

    
    eapply @GeneralCut with (C := dual(rq_lftBody (rulesQ C) FX0) ) ;eauto.
    rewrite <- dualInvolutive;eauto. 
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
                  FLLN (OLTheory nPnN) h1 Gamma (atom (up FCut)::N) (UP [] ) ->
                  FLLN (OLTheory nPnN) h2 Gamma (atom (down FCut)::M) (UP []) -> FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
                  
 Ltac applyOOCut := 
  match goal with
  | [ H: OOCut _ _ |- 
         FLLN ?th ?x ?BX (?FF::?N) (UP []) -> 
         FLLN ?th ?y ?BX (?GG::?M) (UP [])-> 
         FLLS ?thc ?BX (?M++?N) (UP []) ] => eapply H
  | _ => idtac end.
  
Ltac cutOL P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | FLLN ?th ?h1 ?B (atom (up ?FC) :: ?N) (UP []) => 
          match tP2 with 
          | FLLN ?th ?h2 ?B (atom (down ?FC) :: ?M) (UP []) =>  
           match goal with
           | [ H: OOCut ?n' _, Hn: ?n' <= ?n  |- _ ] =>    assert(H': tP1 -> tP2 -> FLLS (OLTheoryCut nPnN (pred n)) B (M++N) (UP []));applyOOCut
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
   |[ H: FLLN _ ?n ?G ( (atom ( _ _ ) :: _) ++ _) (UP []) |- _] =>
      try rewrite <- app_comm_cons in H       
   | _ => idtac
end.


 
Ltac PermuteLeft :=    
  match goal with 
     |[ Hr: FLLN _ ?x ?G (?X ++ _) (UP []),   
        Hr': FLLN _ ?x ?G (?X ++ _) (UP []),             
       Hl: FLLN ?th ?n ?G ( (⌈ ?F ⌉) :: _) (UP []),
       Hp: Permutation ?X ((⌊ ?F ⌋) :: _) |- _] =>
   rewrite Hp in Hr, Hr'
   |[ Hr: FLLN _ ?x ?G (?X ++ _) (UP []),   
        Hr': FLLN _ ?x ?G (?X ++ _) (UP []),             
       Hl: FLLN ?th ?n ?G ( (⌊ ?F  ⌋) :: _) (UP []),
       Hp: Permutation ?X ( (⌈ ?F ⌉) :: _)  |- _] =>
   rewrite Hp in Hr, Hr'
   |[ Hr: FLLN _ ?x ?G (?X ++ _) (UP []),               
       Hl: FLLN _ ?n ?G ( (⌈ ?F ⌉) :: _) (UP []),
       Hp: Permutation ?X ((⌊ ?F ⌋) :: _) |- _] =>
       rewrite Hp in Hr
   |[ Hr: FLLN _ ?x ?G (?X ++ _) (UP []),               
       Hl: FLLN _ ?n ?G ( (⌊ ?F ⌋) :: _) (UP []),
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
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeRRuleU C F) ->
FLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
FLLN (OLTheory nPnN) n1 Gamma ((⌊ FCut ⌋) :: M)
     (DW (makeRRuleU C F)) ->
FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
        cutOL H8 H14.
        LLtheory (makeRRuleU C F).
        LLtensor (@nil oo) (M++N). eauto.
        apply H18...
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
buildTheory (makeLRuleU C F) ->
FLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
FLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeLRuleU C F)) ->
FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
        cutOL H9 H15.
        LLtheory (makeLRuleU C F).
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
        rewrite Permutation_assoc_comm...  
Qed.        

(** Binary Right is not principal on the left branch *) 
Lemma BinaryRightNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bcon C F G) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeRRuleB C F G) ->
FLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
FLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeRRuleB C F G)) ->
FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
        cutOL H8 H14.
        LLtheory (makeRRuleB C F G).
        LLtensor (@nil oo) (M++N). eauto. 
        apply H18...
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
        apply FLLNtoFLLS in H16...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H16;auto using TheoryEmb1.
    -  PermuteLeft.
        cutOL H8 H16.
       rewrite <- H19 in H18.
       rewrite H18 in H4.
       inversion H4...
       OLSolve.
          rewrite <- app_comm_cons.
        rewrite app_assoc_reverse. 
        apply H20...
        apply FLLNtoFLLS in H15...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H15;auto using TheoryEmb1.
        rewrite Permutation_assoc_comm...
    -  PermuteLeft.  
        cutOL H8 H16.
       rewrite <- H19 in H4.
       OLSolve.
        
        rewrite app_assoc_reverse.
        LLtheory (makeRRuleB C F G).
        LLtensor (@nil oo) ((x5 ++ N )++ x0).  eauto.
        apply H21...
         rewrite Permutation_assoc_comm...
    apply FLLNtoFLLS in H17...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.
     -  PermuteLeft.  
        cutOL H8 H17.
       rewrite <- H19 in H4.
       OLSolve.
        LLtheory (makeRRuleB C F G).
        LLtensor (@nil oo) (x++(x5 ++ N )). eauto.
        apply H21...
          apply FLLNtoFLLS in H16...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H16;auto using TheoryEmb1.       
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
        cutOL H8 H15.
        cutOL H8 H16.
        LLtheory (makeRRuleB C F G).
        LLtensor (@nil oo) (M ++ N). eauto. 
        apply H20...
        1-2: rewrite Permutation_assoc_comm...
Qed.    

(** Unary Left is not principal on the left branch *)  
Lemma BinaryLeftNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
FCut <> t_bcon C F G ->
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bcon C F G) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeLRuleB C F G) ->
FLLN (OLTheory nPnN) (S n0) Gamma ((⌈ FCut ⌉) :: N) (UP []) ->
FLLN (OLTheory nPnN) n1 Gamma ((⌊ FCut ⌋) :: M)
     (DW (makeLRuleB C F G)) ->
FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
        cutOL H9 H15.
        LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
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
        apply FLLNtoFLLS in H17...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.
     - PermuteLeft. 
        cutOL H9 H17.
        rewrite <- H20 in H19.
        rewrite H19 in H5.
        inversion H5...
        OLSolve.
        rewrite <- app_comm_cons.
        rewrite app_assoc_reverse. 
        apply H21...
        apply FLLNtoFLLS in H16...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H16;auto using TheoryEmb1.
        rewrite Permutation_assoc_comm...
     - PermuteLeft.
       cutOL H9 H17.
       rewrite <- H20 in H5.
       OLSolve.
       rewrite Permutation_assoc_comm...
       LLtheory  (makeLRuleB C F G).
       LLtensor (@nil oo) ((x5 ++ N) ++ x0). eauto.
       apply H22...
       rewrite Permutation_assoc_comm...
       apply FLLNtoFLLS in H18...
       apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H18;auto using TheoryEmb1.
     - PermuteLeft.  
        cutOL H9 H18.
        rewrite <- H20 in H5.
        OLSolve.
        rewrite app_assoc_reverse.
         LLtheory  (makeLRuleB C F G).
       LLtensor (@nil oo) (x++(x5 ++ N)). eauto.
        apply H22...
        apply FLLNtoFLLS in H17...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.
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
        cutOL H9 H16.
        cutOL H9 H17.
         LLtheory  (makeLRuleB C F G).
       LLtensor (@nil oo) (M++N). eauto.      
        apply H21...
        1-2: rewrite Permutation_assoc_comm... 
 Qed.     

 (** Quantifier Right is not principal on the left branch *) 
 Lemma QuantifierRightNotPrincipalL n n' n0 n1 C FCut FX Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_qcon C FX) ->
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeRRuleQ C FX) ->
FLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
FLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeRRuleQ C FX)) ->
FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellQuantifier H9.  
 Cases H10.
     - PermuteLeft.  
        cutOL H8 H12.
        rewrite H16 in H4.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H18...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.  
        cutOL H8 H14.
        LLtheory (makeRRuleQ C FX).
        LLtensor (@nil oo) (M++N). eauto.
        apply H18...
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
IsPositiveAtomFormulaL M ->
IsPositiveAtomFormulaL N ->
IsPositiveAtomFormulaL Gamma ->
buildTheory (makeLRuleQ C FX) ->
FLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
FLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M)
     (DW (makeLRuleQ C FX)) ->
FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
        cutOL H9 H15.
        LLtheory (makeLRuleQ C FX).
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
        rewrite Permutation_assoc_comm... 
 Qed.       
        
 
Ltac permuteUnary :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeRRuleU _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (UnaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeLRuleU _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (UnaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.     

 
Ltac permuteBinary :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeRRuleB _ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (BinaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeLRuleB _ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (BinaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    
 
 Ltac permuteQuantifier :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeRRuleQ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (QuantifierRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeLRuleQ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
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
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  FLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
  FLLN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ((⌈ FCut ⌉) :: N) (DW (makeRRuleC C)) ->
  FLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleC C) ->
  buildTheory F0 ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
               Cases H0. 
               PermuteLeft.
               cutOL Hseq1 H4.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H10...
               LLPerm ((x3 ++ x) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H6.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N). eauto.
               apply H10...
               LLPerm ( (M ++ x) ++ N)...
           -- wellConstant Hseq2'.   
               Cases H0.
               2:{ rewrite <- app_comm_cons... }
               rewrite <- H7 in H5.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H5 H2).
               Cases H0. 
              rewrite <- H9 in H6.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H6 H2).
               PermuteLeft.
               cutOL Hseq1 H4.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H10...
               LLPerm ((x3 ++ x) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H6.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N). eauto.
               apply H10...
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
       PermuteLeft.
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ((⌈ t_ccon C ⌉) ::(M++ x3))...
         apply H7...
         rewrite app_assoc_reverse... }
     2:{  PermuteLeft.
               cutOL H3 Hseq2.
               LLtheory (makeRRuleC C).
               LLtensor (@nil oo) (M++N). eauto.
               apply H7...
               rewrite app_assoc_reverse... }

         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H2. 
               rewrite <- app_comm_cons...
           -- Cases H2. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               apply H14...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H10.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N). eauto.
               apply H14...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H2. 
               rewrite <- H11 in H9.
               rewrite <- H6 in H3.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConstantPrincipalCase _ H9 H3).
               
               rewrite <- app_comm_cons...
           -- Cases H2. 
               rewrite <- H13 in H10.
               rewrite <- H6 in H3.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.
               refine (ConstantPrincipalCase _ H10 H3).
               
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               apply H14...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H10.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N). eauto.
               apply H14...
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
  FLLN (OLTheory nPnN) (S n0) Gamma  ( (⌈ FCut ⌉) ::N) (UP []) ->
  FLLN (OLTheory nPnN) (S n1)  Gamma ( (⌊ FCut ⌋) ::M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleU C F)) ->
  FLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleU C F) ->
  buildTheory F0 ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
        cutOL H3 Hseq2.
               LLtheory (makeRRuleU C F).
               LLtensor (@nil oo) (M++N). eauto.
               apply H7...
               rewrite app_assoc_reverse... }
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H2. 
               rewrite <- app_comm_cons...
           -- Cases H2. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               apply H14...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H10.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N). eauto.
               apply H14...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H2. 
              rewrite <- app_comm_cons...
           -- Cases H2. 
              PermuteLeft. 
              cutOL Hseq1 H8.
               rewrite H12 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H14...
               rewrite Permutation_assoc_comm...
              PermuteLeft.
              cutOL Hseq1 H10.
                 LLtheory (makeLRuleC C0).
             LLtensor (@nil oo) (M++N). eauto.
               apply H14...  
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
              cutOL Hseq1 H10.
                 LLtheory (makeLRuleU C0 F1).
             LLtensor (@nil oo) (M++N). eauto.
               apply H14...  
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
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  FLLN (OLTheory nPnN) (S n0) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
  FLLN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleB C F G)) ->
  FLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) ::M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleB C F G) ->
  buildTheory F0 ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
   intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellBinary Hseq1'.
  * Cases H. 
     2:{  rewrite H in H1.
         rewrite <- app_comm_cons in H1 . 
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ( (⌈ t_bcon C F G ⌉) ::(M++ x3))...
         apply H7...
         rewrite app_assoc_reverse... }
   2:{ rewrite <- app_comm_cons in H3. 
         cutOL H3 Hseq2.
         OLSolve.
        LLtheory (makeRRuleB C F G).
               LLtensor (@nil oo) (M++N).
               apply H7...
               rewrite app_assoc_reverse... }
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H2. 
               rewrite <- app_comm_cons...
           -- Cases H2. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               apply H14...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H10.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H14...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H2. 
              rewrite <- app_comm_cons...
           -- Cases H2. 
              rewrite H2 in H8.
              rewrite <- app_comm_cons in H8.
              cutOL Hseq1 H8.
               rewrite H12 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H14...
               rewrite Permutation_assoc_comm...
              rewrite <- app_comm_cons in H10.
              cutOL Hseq1 H10.
                 LLtheory (makeLRuleC C0).
             LLtensor (@nil oo) (M++N).
               apply H14...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellBinary Hseq2'.
           { Cases H2. 
            
            rewrite <- H13 in H10. 
            rewrite <- H6 in H3. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H3 _ _ HL')...
              rewrite H2 in H8.
              rewrite <- app_comm_cons in H8.
              cutOL Hseq1 H8.
               rewrite H12 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H14...
               rewrite Permutation_assoc_comm...
              
              rewrite <- app_comm_cons in H10.
              cutOL Hseq1 H10.
                 LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (M++N).
               apply H14...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H2. 
            
            rewrite <- H15 in H8. 
            rewrite <- H6 in H3. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H3 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H11.
            rewrite <- H15 in H14.
             rewrite H14 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x10 ++ N) ++ x4).
              apply H16...
              rewrite Permutation_assoc_comm...
               
               apply FLLNtoFLLS in H12...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              
               PermuteLeft.
            cutOL Hseq1 H12.
            rewrite <- H15 in H14.
             rewrite H14 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: x3++(x10 ++ N)).
              apply H16...
              apply FLLNtoFLLS in H11...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H12. 
               rewrite <- H15 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) ( ((x9 ++ N) ++ x4)).
               apply H17...  
               rewrite Permutation_assoc_comm...
               apply FLLNtoFLLS in H13...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H13. 
               rewrite <- H15 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (x3++(x9 ++ N) ).
               apply H17...
               apply FLLNtoFLLS in H12...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
           { Cases H2. 
            
            rewrite <- H15 in H8. 
            rewrite <- H6 in H3. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H3 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H11.
             rewrite H14 in PosM.
             inversion PosM...
             OLSolve.
            cutOL Hseq1 H12.
             rewrite H14 in PosM.
             inversion PosM...
             OLSolve.
  LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x8 ++ N) ).
              apply H16...
            1-2:  rewrite Permutation_assoc_comm...
 
   
               PermuteLeft.
            cutOL Hseq1 H11.
            cutOL Hseq1 H12.
                LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (M++N).
               apply H16...  
               1-2: rewrite Permutation_assoc_comm... }
          - permuteQuantifier.
         - permuteQuantifier.
  * Cases H. 
     2:{   rewrite H3 in H4.
         rewrite <- app_comm_cons in H4. 
         cutOL H4 Hseq2.
          rewrite <- H8 in H7.
             rewrite H7 in PosN.
             inversion PosN...
             OLSolve.  
         LLPerm ( (⌈ t_bcon C F G ⌉) ::(M++ x6)++x0)...
         apply H9...
         rewrite app_assoc_reverse... 
          apply FLLNtoFLLS in H5...
               apply WeakTheory with (theory := OLTheory nPnN )...  }
   2:{ rewrite H3 in H5.
         rewrite <- app_comm_cons in H5. 
         cutOL H5 Hseq2.
         1-2: OLSolve.
          rewrite <- H8 in H7.
             rewrite H7 in PosN.
             inversion PosN...
             OLSolve.  
        LLPerm ( (⌈ t_bcon C F G ⌉) ::x++(M++ x6))...
         apply H9...
           apply FLLNtoFLLS in H4...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
               rewrite app_assoc_reverse... 
         }
     2:{ 
         rewrite H1 in H5.
         rewrite <- app_comm_cons in H5. 
         cutOL H5 Hseq2.
         rewrite <- H8 in PosN.
         OLSolve.
         LLtheory (makeRRuleB C F G).
               LLtensor (@nil oo) ((M ++ x5)++x0).
         apply H10...
         rewrite app_assoc_reverse... 
          apply FLLNtoFLLS in H6...
               apply WeakTheory with (theory := OLTheory nPnN )...  }
     2:{
        rewrite H1 in H6.
         rewrite <- app_comm_cons in H6. 
         cutOL H6 Hseq2.
         rewrite <- H8 in PosN.
         OLSolve.
         LLtheory (makeRRuleB C F G).
          LLtensor (@nil oo) (x++(M ++ x5)).
         apply H10...
          apply FLLNtoFLLS in H5...
               apply WeakTheory with (theory := OLTheory nPnN )... 
          rewrite app_assoc_reverse... }
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H3. 
               rewrite <- app_comm_cons...
           -- Cases H3. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H10.
               OLSolve.
               apply H16...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H12.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H16...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H3. 
              rewrite <- app_comm_cons...
           -- Cases H3. 
              rewrite H3 in H10.
              rewrite <- app_comm_cons in H10.
              cutOL Hseq1 H10.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
              
              rewrite <- app_comm_cons in H12.
              cutOL Hseq1 H12.
                 LLtheory (makeLRuleC C0).
             LLtensor (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellBinary Hseq2'.
           { Cases H3. 
            
            rewrite <- H15 in H12. 
            rewrite <- H8 in H1. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H1 _ _ HL')...
              rewrite H3 in H10.
              rewrite <- app_comm_cons in H10.
              cutOL Hseq1 H10.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
             
              rewrite <- app_comm_cons in H12.
              cutOL Hseq1 H12.
                 LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H3. 
            
            rewrite <- H8 in H1. 
            rewrite <- H17 in H10. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H1 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H13.
                         rewrite <- H17 in H16.
             rewrite H16 in PosM.
             inversion PosM...
             OLSolve.     
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x12 ++ N) ++ x6).
              apply H18...
              rewrite Permutation_assoc_comm...
               
               apply FLLNtoFLLS in H14...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              
               PermuteLeft.
            cutOL Hseq1 H14.
                         rewrite <- H17 in H16.
             rewrite H16 in PosM.
             inversion PosM...
             OLSolve.     
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: x5++(x12 ++ N)).
              apply H18...
              apply FLLNtoFLLS in H13...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H14. 
                          rewrite <- H17 in PosM.
             OLSolve.     
                LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) ( ((x11 ++ N) ++ x6)).
               apply H19...  
               rewrite Permutation_assoc_comm...
               apply FLLNtoFLLS in H15...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H15. 
               rewrite <- H17 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (x5++(x11 ++ N) ).
               apply H19...
               apply FLLNtoFLLS in H14...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
               
           { Cases H3. 
            
            rewrite <- H17 in H10. 
            rewrite <- H8 in H1. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H1 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H13.
            OLSolve.
            cutOL Hseq1 H14.
            OLSolve.
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x10 ++ N) ).
              apply H18...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H13.
            OLSolve.
            cutOL Hseq1 H14.
            OLSolve.
             LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (M ++ N).
               apply H18...
            1-2:  rewrite Permutation_assoc_comm... }
                           
          - permuteQuantifier.
         - permuteQuantifier.
  * Cases H. 
     2:{ 
         rewrite H3 in H4, H5.
         rewrite <- app_comm_cons in H4, H5 . 
         cutOL H4 Hseq2.
         rewrite H7 in PosN.
         OLSolve.
         cutOL H5 Hseq2.
         rewrite H7 in PosN.
         OLSolve.
         
         
         LLPerm ((⌈ t_bcon C F G ⌉) ::M++ x4)...
         apply H9...
         1-2: rewrite app_assoc_reverse... 
          }
   2:{ 
         rewrite <- app_comm_cons in H4, H5 . 
         cutOL H4 Hseq2.
         cutOL H5 Hseq2.
         LLtheory (makeRRuleB C F G).
               LLtensor (@nil oo) (M ++N).
         apply H9...
        1-2: rewrite app_assoc_reverse... } 
         inversion Hth'...
         - wellConstant Hseq2'.
           -- Cases H3. 
               rewrite <- app_comm_cons...
           -- Cases H3. 
               rewrite <- app_comm_cons...
               PermuteLeft.
               cutOL Hseq1 H10.
               OLSolve.
               apply H16...
               rewrite Permutation_assoc_comm...
               PermuteLeft.
               cutOL Hseq1 H12.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H16...
               rewrite Permutation_assoc_comm...
         - wellConstant Hseq2'.
           -- Cases H3. 
              rewrite <- app_comm_cons...
           -- Cases H3.
               PermuteLeft.
               cutOL Hseq1 H10.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
              
              PermuteLeft.
              cutOL Hseq1 H12.
                 LLtheory (makeLRuleC C0).
             LLtensor (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... 
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - wellBinary Hseq2'.
           { Cases H3. 
            
            rewrite <- H8 in H1. 
            rewrite <- H15 in H12. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H1 _ _ HL')...
             
             PermuteLeft.
              cutOL Hseq1 H10.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
              
              PermuteLeft.
              cutOL Hseq1 H12.
                 LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H3. 
            
            rewrite <- H8 in H1. 
            rewrite <- H17 in H10. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H1 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H13.
             rewrite <- H17 in H16.
             rewrite H16 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: (x11 ++ N) ++ x5).
              apply H18...
              rewrite Permutation_assoc_comm...
               
               apply FLLNtoFLLS in H14...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              
               PermuteLeft.
            cutOL Hseq1 H14.
             rewrite <- H17 in H16.
             rewrite H16 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bcon C0 F1 G0 ⌋) :: x4++(x11 ++ N)).
              apply H18...
              apply FLLNtoFLLS in H13...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H14. 
                rewrite <- H17 in PosM.
             OLSolve.   
                LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) ( ((x10 ++ N) ++ x5)).
               apply H19...  
               rewrite Permutation_assoc_comm...
               apply FLLNtoFLLS in H15...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H15. 
                rewrite <- H17 in PosM.
             OLSolve.   
                LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (x4++(x10 ++ N) ).
               apply H19...
               apply FLLNtoFLLS in H14...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
               
           { Cases H3. 
            
            rewrite <- H8 in H1. 
            rewrite <- H17 in H10. 
            rewrite Permutation_app_comm.
            refine(BinConnectivePrincipalCase _ H1 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H13.
            OLSolve.
            cutOL Hseq1 H14.
            OLSolve.
            LLPerm ((⌊ t_bcon C0 F1 G0 ⌋) :: (x9 ++ N) ).
              apply H18...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H13.
            cutOL Hseq1 H14.
             LLtheory (makeLRuleB C0 F1 G0).
             LLtensor (@nil oo) (M ++ N).
               apply H18...
            1-2:  rewrite Permutation_assoc_comm... }
                           
          - permuteQuantifier.
         - permuteQuantifier.         
  Qed.                        
   

Lemma QuantifierRIGHT n n' n0 n1  C FX FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_qcon C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  FLLN (OLTheory nPnN) (S n0)  Gamma ( (⌈ FCut ⌉) ::N) (UP []) ->
  FLLN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeRRuleQ C FX)) ->
  FLLN (OLTheory nPnN) n1 Gamma ( (⌊ FCut ⌋) :: M) (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleQ C FX) ->
  buildTheory F0 ->
  uniform FX ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth' Hu.
  wellQuantifier Hseq1'.
  Cases H. 
  2:{ PermuteLeft. 
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ( (⌈ t_qcon C FX ⌉) ::(M++ x3))...
         apply H7...
         rewrite app_assoc_reverse... }
  2:{ PermuteLeft. 
         cutOL H3 Hseq2.
         LLtheory (makeRRuleQ C FX).
         LLtensor (@nil oo) (M++N). eauto.
         apply H7...
         rewrite app_assoc_reverse... }         
    inversion Hth'... 
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons... 
 Cases H2. 
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H14...
               LLPerm ((x7 ++ x3) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H10.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N). eauto.
               apply H14...
               LLPerm ( (M ++ x3) ++ N)...
           -- wellConstant Hseq2'.   
               Cases H2.
               rewrite <- app_comm_cons...               Cases H2. 
               PermuteLeft.
               cutOL Hseq1 H8.
               OLSolve.
               rewrite <- app_comm_cons...
               apply H14...
               LLPerm ((x7 ++ x3) ++ N)...
               PermuteLeft.
               cutOL Hseq1 H10.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N). eauto.
               apply H14...
               LLPerm ( (M ++ x3) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.           
           -- wellQuantifier Hseq2'.
               destruct H5...
               checkPermutationCases H5.
               inversion H13...
               rewrite <- H6 in H3.
               rewrite <- H14 in H11.
               rewrite Permutation_app_comm.
               refine (QuantifierPrincipalCase H11 H3 _ _ _ _ _ _ HL')...   
               PermuteLeft.
               cutOL Hseq1 H9.
               OLSolve.
               rewrite H13.
               LLPerm ( (⌊t_qcon C0 FX0 ⌋) :: x7++ N).
               apply H15...
               LLPerm ((x7 ++ x3) ++ N)...
               
               PermuteLeft.
               cutOL Hseq1 H11.
              LLtheory (makeLRuleQ C0 FX0).
               LLtensor (@nil oo) (M++N). eauto.
               apply H15...
               LLPerm ((M ++ x3) ++ N)...
     Qed.         
             
Definition ConnectiveLeft connective rule := forall n n' n0 n1  FCut M N Gamma,
  n' <= n ->
  isOLFormula connective ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  FLLN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW rule) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory rule ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
     

             
Lemma ConstantLEFT n n' n0 n1  C FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_ccon C) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  FLLN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleC C)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleC C) ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellConstant Hseq1'.
  * Cases H. 
     + LLPerm ( (⌊ t_ccon C ⌋) :: x0++M)...
  * Cases H. 
     + PermuteLeft.  
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ( (⌊ t_ccon C ⌋) ::(M++ x3)).
         apply H7...
         LLPerm(M ++ x3 ++ x)...
    + PermuteLeft.   
         cutOL H3 Hseq2.
         LLtheory (makeLRuleC C).
         LLtensor (@nil oo) (M++N). eauto.
         apply H7... 
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
  FLLN (OLTheory nPnN) (S n1) Gamma  ( (⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleU C F)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleU C F) ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
         cutOL H3 Hseq2.
         LLtheory (makeLRuleU C F).
         LLtensor (@nil oo) (M++N). eauto.
         apply H7... 
         LLPerm(M ++ N ++ x)...
Qed.       

 Lemma BinaryLEFT n n' n0 n1 C F G FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_bcon C F G) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  FLLN (OLTheory nPnN) (S n1) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleB C F G)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleB C F G) ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellBinary Hseq1'.
  * Cases H. 
   +   rewrite H in H1. 
         rewrite <- app_comm_cons in H1. 
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ( (⌊t_bcon C F G ⌋) ::(M++ x3)).
         apply H7...
         LLPerm(M ++ x3 ++ x)...
     + rewrite <- app_comm_cons in H3. 
         cutOL H3 Hseq2.
         LLtheory (makeLRuleB C F G).
         LLtensor (@nil oo) (M++N).
         apply H7... 
         LLPerm(M ++ N ++ x)...
  * Cases H. 
     + 
         rewrite H3 in H4.
         rewrite <- app_comm_cons in H4. 
         cutOL H4 Hseq2.
         rewrite  <- H8 in H7. 
         rewrite H7 in PosN.
         inversion PosN...
         OLSolve.
         LLPerm ((⌊ t_bcon C F G ⌋) :: (M++x6) ++ x0).
         apply H9...
         rewrite app_assoc_reverse...
         apply FLLNtoFLLS in H5...
         apply WeakTheory with (theory := OLTheory nPnN )... 
     + 
         rewrite H3 in H5.
         rewrite <- app_comm_cons in H5. 
         cutOL H5 Hseq2.
         rewrite  <- H8 in H7. 
         rewrite H7 in PosN.
         inversion PosN...
         OLSolve.
         LLPerm ( (⌊ t_bcon C F G ⌋) :: x++(M++x6)).
         apply H9...
         apply FLLNtoFLLS in H4...
         apply WeakTheory with (theory := OLTheory nPnN )... 
          
         rewrite app_assoc_reverse...
     + 
         rewrite H1 in H5.
         rewrite <- app_comm_cons in H5. 
         cutOL H5 Hseq2.
         rewrite  <- H8 in PosN.
         OLSolve.
         LLtheory  (makeLRuleB C F G).
         LLtensor (@nil oo) ((M ++ x5) ++ x0).
         apply H10...
         rewrite app_assoc_reverse...
         apply FLLNtoFLLS in H6...
         apply WeakTheory with (theory := OLTheory nPnN )... 
     + 
         rewrite H1 in H6.
         rewrite <- app_comm_cons in H6. 
         cutOL H6 Hseq2.
         rewrite  <- H8 in PosN.
         OLSolve.
         LLtheory  (makeLRuleB C F G).
         LLtensor (@nil oo) (x++(M ++ x5)).
         apply H10...
         apply FLLNtoFLLS in H5...
         apply WeakTheory with (theory := OLTheory nPnN )... 
           rewrite app_assoc_reverse...
  * Cases H. 
     + rewrite H3 in H4, H5.
         rewrite <- app_comm_cons in H4, H5. 
         cutOL H4 Hseq2.
         rewrite H7 in PosN.
         OLSolve.
         cutOL H5 Hseq2.
         rewrite H7 in PosN.
         OLSolve.
         LLPerm ( (⌊ t_bcon C F G ⌋) :: M++x4).
         apply H9...
         1-2: rewrite app_assoc_reverse...
     + rewrite <- app_comm_cons in H4, H5. 
         cutOL H4 Hseq2.
         cutOL H5 Hseq2.
         LLtheory (makeLRuleB C F G). 
         LLtensor (@nil oo) (M++N).
         apply H9...
         1-2: rewrite app_assoc_reverse... 
Qed.         
 
Lemma QuantifierLEFT n n' n0 n1 C FX FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_qcon C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  IsPositiveAtomFormulaL M ->
  IsPositiveAtomFormulaL N ->
  IsPositiveAtomFormulaL Gamma ->
  FLLN (OLTheory nPnN) (S n1) Gamma ( (⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) n0 Gamma ( (⌈ FCut ⌉) :: N) (DW (makeLRuleQ C FX)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleQ C FX) ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
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
         cutOL H3 Hseq2.
         LLtheory (makeLRuleQ C FX).
         LLtensor (@nil oo) (M++N). eauto.
         apply H7... 
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
      FLLN (OLTheory nPnN) h1 Gamma ( atom(up FCut)::N) (UP []) ->
      FLLN (OLTheory nPnN) h2 Gamma (atom (down FCut)::M) (UP []) ->
      lengthUexp FCut n' -> n'<=n ->
      (FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP [])) .
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
pose proof  (onlyAtomsClassical PosG  H0  H1)...
 
   inversion Hseq2...

   
cut(False);intros...
       refine (onlyAtomsLinear _ H3 H4)... 

  cut(False);intros...
 apply onlyAtomsClassical in H4...
 
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
                           H9 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8 H7)...        
       - refine(QuantifierLEFT 
                           HL' 
                           H9 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
    * apply FocusingInitRuleU in H5...
       - checkPermutationCases H7. 
          inversion H7...
          apply FLLNtoFLLS in Hseq1.
          apply WeakTheory with (theory := OLTheory nPnN )... 
        - inversion H9...
           apply absorptionInN  in Hseq1...
          apply FLLNtoFLLS in Hseq1.
          apply WeakTheory with (theory := OLTheory nPnN )... 
    * apply FocusingInitRuleU in H2...
       - checkPermutationCases H7. 
          inversion H9...
          apply FLLNtoFLLS in Hseq2.
          apply WeakTheory with (theory := OLTheory nPnN )... 
         LLExact Hseq2.
        - inversion H7...
           apply absorptionInN in Hseq2...
          apply FLLNtoFLLS in Hseq2.
          apply WeakTheory with (theory := OLTheory nPnN )... 
    * apply FocusingInitRuleU in H2...
       - checkPermutationCases H7. 
          inversion H9...
          apply FLLNtoFLLS in Hseq2.
          apply WeakTheory with (theory := OLTheory nPnN )... 
         LLExact Hseq2.
        - inversion H7...
           apply absorptionInN in Hseq2...
          apply FLLNtoFLLS in Hseq2.
          apply WeakTheory with (theory := OLTheory nPnN )... 
 Qed.                   
         
  Theorem OLCutElimAux :
    forall n h  B N ,
      IsPositiveAtomFormulaL B ->
      IsPositiveAtomFormulaL N ->
      FLLN  (OLTheoryCut nPnN n) h  B N (UP[] ) ->
      FLLS  (OLTheoryCut nPnN 0) B N (UP[] ) .
  Proof with sauto;try OLSolve.
  induction n ; induction h using lt_wf_ind; intros *;intros isFB isFN Hh.
    * eapply FLLNtoFLLS;eauto. 
    * inversion Hh...
       apply onlyAtomsLinear in H1...
      apply onlyAtomsClassical in H1...
      inversion H1...
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
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
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
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
      + (* unary *)
         wellUnary H2.
         Cases H6.
         apply H14... 
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeRRuleU C F0).
         LLtensor (@nil oo) N. eauto.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
      + (* unary *)
         wellUnary H2.
         Cases H6. 
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeLRuleU C F0).
         LLtensor (@nil oo) N.  eauto.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
      + (* binary *)
         wellBinary H2.
         { Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeRRuleB C F0 G).
         LLtensor (@nil oo) N. eauto.
         apply H14...
         refine (H _ _ _ _ _ _ H10)... }
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
         rewrite H8.
         apply H17...
         refine (H _ _ _ _ _ _ H12)... 
         rewrite H8 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H13)... 
         rewrite H8 in isFN.
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
         apply H16...
         refine (H _ _ _ _ _ _ H11)... 
         refine (H _ _ _ _ _ _ H12)...  } 
      + (* binary *)
         wellBinary H2.
         { Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeLRuleB C F0 G).
         LLtensor (@nil oo) N.  eauto.
         apply H14...
         refine (H _ _ _ _ _ _ H10)... }
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
         rewrite H8.
         apply H17...
         refine (H _ _ _ _ _ _ H12)... 
         rewrite H8 in isFN.
         inversion isFN...
         refine (H _ _ _ _ _ _ H13)... 
         rewrite H8 in isFN.
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
         apply H16...
         refine (H _ _ _ _ _ _ H11)... 
         refine (H _ _ _ _ _ _ H12)...  } 
      + (* quantifier *)
         wellQuantifier H2.
         Cases H7.
         apply H15...
         refine (H _ _ _ _ _ _ H9)...
         OLSolve.
         LLtheory (makeRRuleQ C FX).
         LLtensor (@nil oo) N.  eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* quantifier *)
         wellQuantifier H2.
         Cases H7.
         apply H15...
         refine (H _ _ _ _ _ _ H9)...
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
         LLtensor. 
      + inversion f.
     + inversion f. 
      + (* cut *)
          inversion H3... 2:{ firstorder. }
         inversion H2...
         2:{ inversion H8. }
         invTri H13.
         invTri H14.
         invTri H15.
         invTri H13.
         clearPolarity.
         apply H in H16...
         2: repeat OLSolve. 
         apply H in H15...
         2: repeat OLSolve. 
         apply WeakTheory with (theory' := OLTheory nPnN) in H15, H16;auto;try apply OOTheryCut0.
         rewrite H9.
         apply WeakTheory with (theory := OLTheory nPnN).
         apply OOTheryCut0.
  
         destruct m.
         generalize(LengthFormula H4 H5);intro;lia.
         assert (FLLS (OLTheoryCut nPnN (pred  (S (n)))) B (M ++ N0) (UP [])) .
         rewrite Permutation_app_comm.
         apply FLLStoFLLN in H15, H16...
         refine(OLCutElimStep _ _ _ _ H16 H15 H5 _)...
        simpl in H7...
       apply FLLStoFLLN in H7...
        apply IHn in H7...
        apply WeakTheory with (theory' := OLTheory nPnN) in H7;auto;try apply  OOTheryCut0.
Qed.
     
         (** Cut-elimination theorem for Object Logics satisfying cut-coherence *)
  Theorem OLCutElimination :
    forall n h  B N ,
      IsPositiveAtomFormulaL B ->
      IsPositiveAtomFormulaL N ->
      FLLN (OLTheoryCut nPnN n) h  B N (UP [] ) ->
      FLLS (OLTheory nPnN) B N (UP [] ) .
  Proof with sauto.
    intros. 
    apply OLCutElimAux in H1 ...
    eapply WeakTheory with (theory':= OLTheory nPnN) in H1 ...
    apply OOTheryCut0.
  Qed.     
  
End CutElimination.
