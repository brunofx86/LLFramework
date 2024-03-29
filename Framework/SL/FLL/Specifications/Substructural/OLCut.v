
(** * LL as a Meta-logical framework.  *)

(** In this file we show how the cut-elimination procedure for FLL can
be used to prove cut-elimination for object logics that are
cut-coherent in the sense of Miller & Pimentel. Roughly, a system is
cut-coherent if the encoding of the right and left rules of each
connective are dual. *)

Require Export LL.Framework.SL.FLL.Specifications.StructuralClauses. 
Require Export LL.Framework.SL.FLL.Specifications.WellHyp.
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

Hypothesis LTWell : wellFormedTheory. 
Hypothesis LTCutCo: CutCoherence cutR1.

 (** This is the case when a constant is principal in both premises *)
  Theorem ConPrincipalCase :
    forall Gamma M N C,
      (FLLS (OLTheory nPnN) Gamma M (DW (rc_lftBody (rulesC C)))) ->
      (FLLS (OLTheory nPnN) Gamma N (DW (rc_rgtBody (rulesC C)))) ->
      FLLS (OLTheory nPnN) Gamma (N ++ M) (UP []).
 Proof with sauto.     
    intros.
    apply  FLLStoFLLN in H... 
    apply FLLStoFLLN in H0...
    generalize( ctCutCo LTCutCo C);intro CutC.
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
  Theorem UnaPrincipalCase :
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

    generalize( unCutCo LTCutCo C);intro CutC.
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
  Theorem BinPrincipalCase :
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

    generalize (biCutCo LTCutCo C);intro CutC.
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
  Theorem QuaPrincipalCase :
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
    generalize ( quCutCo LTCutCo C) ;intro CutC.
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
              posAtomFormulaL M ->
                posAtomFormulaL N ->
                  posAtomFormulaL Gamma ->
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
   
 Definition ConnectiveRightNotPrincipalL conn Rule := forall n n' h1 h2 FCut M N Gamma,
  n' <= n ->
  OOCut n' (S h1 + S h2) ->
  lengthUexp FCut n' ->
  isOLFormula FCut ->
  isOLFormula conn ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  buildTheory Rule ->
  FLLN (OLTheory nPnN) (S h1) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
    FLLN (OLTheory nPnN) h2 Gamma ((⌊ FCut ⌋) :: M) (DW Rule) ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
 
  Definition ConnectiveLeftNotPrincipalL conn Rule := forall n n' h1 h2 FCut M N Gamma,
  FCut <> conn -> n' <= n ->  
  OOCut n' (S h1 + S h2) ->
  lengthUexp FCut n' ->
  isOLFormula FCut ->
  isOLFormula conn ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  buildTheory Rule ->
  FLLN (OLTheory nPnN) (S h1) Gamma ( (⌈ FCut ⌉) :: N) (UP []) ->
    FLLN (OLTheory nPnN) h2 Gamma ((⌊ FCut ⌋) :: M) (DW Rule) ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
        
Lemma ConRightNotPrincipalL C : ConnectiveRightNotPrincipalL  (t_ccon C) (makeRRuleC C). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveRightNotPrincipalL; intros.
  wellConstant LTWell H9.
  * Cases H10.
     LLPerm ((⌈ t_ccon C ⌉) :: x0++N)...
  * Cases H10.
     - PermuteLeft.
        cutOL H8 H12.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H18...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.
        cutOL H8 H14.
        LLtheory (makeRRuleC C).
        LLtensor (@nil oo) (M++N). eauto.
        apply H18...
        rewrite Permutation_assoc_comm... 
Qed.

(** Unary Left is not principal on the left branch *) 
Lemma ConLeftNotPrincipalL C : ConnectiveLeftNotPrincipalL  (t_ccon C) (makeLRuleC C). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveLeftNotPrincipalL; intros.
  wellConstant LTWell H10.
  * Cases H11.
     LLPerm ((⌊ t_ccon C ⌋) :: x0++N)...
  * Cases H11.
     - PermuteLeft.
        cutOL H9 H13.
        OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - PermuteLeft.
        cutOL H9 H15.
        LLtheory (makeLRuleC C).
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
        rewrite Permutation_assoc_comm... 
Qed.

(** Unary Right is not principal on the left branch *)    
Lemma UnaRightNotPrincipalL C F : ConnectiveRightNotPrincipalL  (t_ucon C F) (makeRRuleU C F). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveRightNotPrincipalL; intros.
  wellUnary LTWell H9.
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
Lemma UnaLeftNotPrincipalL C F : ConnectiveLeftNotPrincipalL  (t_ucon C F) (makeLRuleU C F). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveLeftNotPrincipalL; intros.
  wellUnary LTWell H10.
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
Lemma BinRightNotPrincipalL C F G: ConnectiveRightNotPrincipalL  (t_bcon C F G) (makeRRuleB C F G). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveRightNotPrincipalL; intros.
  wellBinary LTWell H9.
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
Lemma BinLeftNotPrincipalL C F G: ConnectiveLeftNotPrincipalL  (t_bcon C F G) (makeLRuleB C F G). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveLeftNotPrincipalL; intros.
  wellBinary LTWell H10.
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
 Lemma QuaRightNotPrincipalL C FX : ConnectiveRightNotPrincipalL (t_qcon C FX) (makeRRuleQ C FX). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveRightNotPrincipalL; intros.
  wellQuantifier LTWell H9.  
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
 Lemma QuaLeftNotPrincipalL C FX : ConnectiveLeftNotPrincipalL (t_qcon C FX) (makeLRuleQ C FX). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveLeftNotPrincipalL; intros.
   wellQuantifier LTWell H10.
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
        
Ltac permuteConstantL :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeRRuleC _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (ConRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeLRuleC _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (ConLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf
  end.     
 
Ltac permuteUnaryL :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeRRuleU _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (UnaRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeLRuleU _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (UnaLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
  end.     

 
Ltac permuteBinaryL :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeRRuleB _ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (BinRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
 | [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeLRuleB _ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (BinLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
  end.    
 
 Ltac permuteQuantifierL :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeRRuleQ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (QuaRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?N) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?M) (DW (makeLRuleQ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (QuaLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    

 Definition ConnectiveRightNotPrincipalR conn Rule := forall n n' h1 h2 FCut M N Gamma,
  FCut <> conn -> n' <= n ->
  OOCut n' (S h1 + S h2) ->
  lengthUexp FCut n' ->
  isOLFormula FCut ->
  isOLFormula conn ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  buildTheory Rule ->
  FLLN (OLTheory nPnN) (S h2) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) h1 Gamma ( (⌈ FCut ⌉) :: N) (DW Rule) ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
 
  Definition ConnectiveLeftNotPrincipalR conn Rule := forall n n' h1 h2 FCut M N Gamma,
  n' <= n ->  
  OOCut n' (S h1 + S h2) ->
  lengthUexp FCut n' ->
  isOLFormula FCut ->
  isOLFormula conn ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  buildTheory Rule ->
  FLLN (OLTheory nPnN) (S h2) Gamma ((⌊ FCut ⌋) :: M) (UP []) ->
  FLLN (OLTheory nPnN) h1 Gamma ( (⌈ FCut ⌉) :: N) (DW Rule) ->
  FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).
       
 Lemma ConLeftNotPrincipalR C : ConnectiveLeftNotPrincipalR  (t_ccon C) (makeLRuleC C). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveLeftNotPrincipalR; intros.
  wellConstant LTWell H9.
  * Cases H10.
     LLPerm (( ⌊ t_ccon C ⌋) :: M++x0)...
  * Cases H10.
     - PermuteLeft.
        cutOL H12 H8.
        OLSolve.
        rewrite <- Permutation_middle.
        apply H18...
        rewrite app_assoc_reverse...
     - PermuteLeft.
        cutOL H14 H8.
        LLtheory (makeLRuleC C).
        LLtensor (@nil oo) (M++N). eauto.
        apply H18...
        rewrite app_assoc_reverse...
Qed.

(** Unary Left is not principal on the left branch *) 
Lemma ConRightNotPrincipalR C : ConnectiveRightNotPrincipalR  (t_ccon C) (makeRRuleC C). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveRightNotPrincipalR; intros.
  wellConstant LTWell H10.
  * Cases H11.
     LLPerm ((⌈ t_ccon C ⌉) ::M++x0)...
  * Cases H11.
     - PermuteLeft.
        cutOL H13 H9.
        OLSolve.
        rewrite <- Permutation_middle.
        apply H19...
        rewrite app_assoc_reverse...
     - PermuteLeft.
        cutOL H15 H9.
        LLtheory (makeRRuleC C).
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
        rewrite app_assoc_reverse...
Qed.

(** Unary Right is not principal on the left branch *)    
Lemma UnaLeftNotPrincipalR C F : ConnectiveLeftNotPrincipalR  (t_ucon C F) (makeLRuleU C F). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveLeftNotPrincipalR; intros.
  wellUnary LTWell H9.
  * Cases H10.
     - PermuteLeft.
        cutOL H12 H8. 
        OLSolve. 
        rewrite  Permutation_midle.
        apply H18...
        rewrite app_assoc_reverse... 
     -  PermuteLeft.
        cutOL H14 H8.
        LLtheory (makeLRuleU C F).
        LLtensor (@nil oo) (M++N). eauto.
        apply H18...
        rewrite app_assoc_reverse...
Qed.

(** Unary Left is not principal on the left branch *) 
Lemma UnaRightNotPrincipalR C F : ConnectiveRightNotPrincipalR  (t_ucon C F) (makeRRuleU C F). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveRightNotPrincipalR; intros.
  wellUnary LTWell H10.
  * Cases H11.
     - PermuteLeft. 
        cutOL H13 H9.
        OLSolve.
        rewrite Permutation_midle. 
        apply H19...
        rewrite app_assoc_reverse...
     - PermuteLeft. 
        cutOL H15 H9.
        LLtheory (makeRRuleU C F).
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
        rewrite app_assoc_reverse...
Qed.     
        
(** Binary Right is not principal on the left branch *) 
Lemma BinLeftNotPrincipalR C F G: ConnectiveLeftNotPrincipalR  (t_bcon C F G) (makeLRuleB C F G). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveLeftNotPrincipalR; intros.
  wellBinary LTWell H9.
  * Cases H10.
     - PermuteLeft. 
        cutOL H12 H8.
        OLSolve.
        rewrite Permutation_midle. 
        apply H18...
        rewrite app_assoc_reverse... 
     - PermuteLeft. 
        cutOL H14 H8.
        LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) (M++N). eauto. 
        apply H18...
        rewrite app_assoc_reverse...
  * Cases H10.
     - PermuteLeft.
       cutOL H15 H8.
       rewrite <- H19 in H18.
       rewrite H18 in H5.
       inversion H5...
       OLSolve.
       rewrite Permutation_midle. 
       LLPerm (⌊ t_bcon C F G ⌋ :: (M ++ x6) ++ x0).
        apply H20...
        rewrite app_assoc_reverse... 
        apply FLLNtoFLLS in H16...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H16;auto using TheoryEmb1.
    -  PermuteLeft.
        cutOL H16 H8.
       rewrite <- H19 in H18.
       rewrite H18 in H5.
       inversion H5...
       OLSolve.
       rewrite Permutation_midle. 
       LLPerm (⌊ t_bcon C F G ⌋ ::x++ (M ++ x6) ).
        apply H20...
        apply FLLNtoFLLS in H15...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H15;auto using TheoryEmb1.
        rewrite app_assoc_reverse...
    -  PermuteLeft.  
        cutOL H16 H8.
       rewrite <- H19 in H5.
       OLSolve.
        LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) ((M++x5)++ x0).  eauto.
        apply H21...
         rewrite app_assoc_reverse... 
    apply FLLNtoFLLS in H17...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.
     -  PermuteLeft.  
        cutOL H17 H8.
       rewrite <- H19 in H5.
       OLSolve.
        LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) (x++(M++x5 )). eauto.
        apply H21...
          apply FLLNtoFLLS in H16...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H16;auto using TheoryEmb1.       
         rewrite app_assoc_reverse... 
* Cases H10.
     - PermuteLeft.
       cutOL H15 H8.
       rewrite H18 in H5.
        OLSolve.
        cutOL H16 H8.
       rewrite H18 in H5.
        OLSolve.
        rewrite <- Permutation_middle. 
        apply H20...
        1-2: rewrite app_assoc_reverse...
      - PermuteLeft.
        cutOL H15 H8.
        cutOL H16 H8.
        LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) (M ++ N). eauto. 
        apply H20...
        1-2: rewrite app_assoc_reverse... 
Qed.

(** Unary Left is not principal on the left branch *)  
Lemma BinRightNotPrincipalR C F G: ConnectiveRightNotPrincipalR  (t_bcon C F G) (makeRRuleB C F G). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveRightNotPrincipalR; intros.
  wellBinary LTWell H10.
  * Cases H11.
     - PermuteLeft.  
        cutOL H13 H9.
        rewrite H17 in H6.
        OLSolve.
        rewrite <- Permutation_middle.
        apply H19...
        rewrite app_assoc_reverse... 
     - PermuteLeft.  
        cutOL H15 H9.
        LLtheory (makeRRuleB C F G).
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
        rewrite app_assoc_reverse... 
  * Cases H11.
     - PermuteLeft.  
        cutOL H16 H9.
        rewrite <- H20 in H19.
        rewrite H19 in H6.
        inversion H6...
        OLSolve.
        rewrite <- Permutation_middle. 
        LLPerm (⌈ t_bcon C F G ⌉ :: (M ++ x6) ++ x0).
        apply H21...
        rewrite app_assoc_reverse...
        apply FLLNtoFLLS in H17...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.
     - PermuteLeft. 
        cutOL H17 H9.
        rewrite <- H20 in H19.
        rewrite H19 in H6.
        inversion H6...
        OLSolve.
        rewrite <- Permutation_middle.
        LLPerm(⌈ t_bcon C F G ⌉ :: x++(M ++ x6) ).
        apply H21...
        apply FLLNtoFLLS in H16...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H16;auto using TheoryEmb1.
        rewrite app_assoc_reverse...
     - PermuteLeft.
       cutOL H17 H9.
       rewrite <- H20 in H6.
       OLSolve.
       LLtheory  (makeRRuleB C F G).
       LLtensor (@nil oo) ((M++x5) ++ x0). eauto.
       apply H22...
       rewrite app_assoc_reverse...
       apply FLLNtoFLLS in H18...
       apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H18;auto using TheoryEmb1.
     - PermuteLeft.  
        cutOL H18 H9.
        rewrite <- H20 in H6.
        OLSolve.
         LLtheory  (makeRRuleB C F G).
       LLtensor (@nil oo) (x++(M++x5)). eauto.
        apply H22...
        apply FLLNtoFLLS in H17...
        apply WeakTheory with (theory' := OLTheoryCut nPnN (pred n)) in H17;auto using TheoryEmb1.
         rewrite app_assoc_reverse...
  * Cases H11.
     - PermuteLeft.  
        cutOL H16 H9.
        rewrite H19 in H6.
        OLSolve.
        cutOL H17 H9.
        rewrite H19 in H6.
        OLSolve.
        rewrite <- Permutation_middle.
        apply H21...
        1-2: rewrite app_assoc_reverse... 
     - PermuteLeft.  
        cutOL H16 H9.
        cutOL H17 H9.
         LLtheory  (makeRRuleB C F G).
       LLtensor (@nil oo) (M++N). eauto.      
        apply H21...
        1-2: rewrite app_assoc_reverse... 
 Qed.     

 (** Quantifier Right is not principal on the left branch *) 
 Lemma QuaLeftNotPrincipalR C FX : ConnectiveLeftNotPrincipalR (t_qcon C FX) (makeLRuleQ C FX). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveLeftNotPrincipalR; intros.
  wellQuantifier LTWell H9.  
 Cases H10.
     - PermuteLeft.  
        cutOL H12 H8.
        rewrite H16 in H5.
        OLSolve.
        rewrite <- Permutation_middle. 
        apply H18...
        rewrite app_assoc_reverse...
     - PermuteLeft.  
        cutOL H14 H8.
        LLtheory (makeLRuleQ C FX).
        LLtensor (@nil oo) (M++N). eauto.
        apply H18...
        rewrite app_assoc_reverse...
Qed.

 (** Quantifier Left is not principal on the left branch *) 
 Lemma QuaRightNotPrincipalR C FX : ConnectiveRightNotPrincipalR (t_qcon C FX) (makeRRuleQ C FX). 
Proof with sauto; try OLSolve.
  unfold  ConnectiveRightNotPrincipalR; intros.
   wellQuantifier LTWell H10.
  * Cases H11.
     - PermuteLeft.  
        cutOL H13 H9.
        rewrite H17 in H6.
        OLSolve.
        rewrite <- Permutation_middle.
        apply H19...
        rewrite app_assoc_reverse...
     - PermuteLeft.  
        cutOL H15 H9.
        LLtheory (makeRRuleQ C FX).
        LLtensor (@nil oo) (M++N). eauto.
        apply H19...
        rewrite app_assoc_reverse...
 Qed.       

Ltac permuteConstantR :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?M) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?N) (DW (makeLRuleC _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (ConLeftNotPrincipalR H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?M) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?N) (DW (makeRRuleC _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (ConRightNotPrincipalR _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf 
  end.    
        
Ltac permuteUnaryR :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?M) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?N) (DW (makeLRuleU _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (UnaLeftNotPrincipalR H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?M) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?N) (DW (makeRRuleU _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (UnaRightNotPrincipalR _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf 
  end.     

Ltac permuteBinaryR :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?M) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?N) (DW (makeLRuleB _ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (BinLeftNotPrincipalR H _ _ _ _ _ _ _ _ Hl Hr);sauto
 | [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?M) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?N) (DW (makeRRuleB _ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (BinRightNotPrincipalR _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
  end.    
 
 Ltac permuteQuantifierR :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?M) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?N) (DW (makeLRuleQ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
   refine (QuaLeftNotPrincipalR H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: FLLN _ _ _ (_ :: ?M) (UP []) ,
   Hr : FLLN _ _ _ (_ :: ?N) (DW (makeRRuleQ _ _))
  |-  FLLS _ _ (?M ++ ?N) (UP []) ] =>
refine (QuaRightNotPrincipalR _ H _ _ _ _ _ _ _ _ Hl Hr);
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

 Definition ConnectiveRight conn Rule := forall n n' h1 h2  FCut M N Gamma Rule',
   n' <= n ->
   isOLFormula conn ->
   isOLFormula FCut ->
   lengthUexp FCut n' ->
   posAtomFormulaL M ->
   posAtomFormulaL N ->
   posAtomFormulaL Gamma ->
   FLLN (OLTheory nPnN) (S h1) Gamma ((⌈ FCut ⌉) :: N) (UP [])  ->
   FLLN (OLTheory nPnN) (S h2) Gamma ((⌊ FCut ⌋) :: M) (UP [])  ->
   FLLN (OLTheory nPnN) h1 Gamma ((⌈ FCut ⌉) :: N) (DW Rule)  ->
   FLLN (OLTheory nPnN) h2 Gamma ((⌊ FCut ⌋) :: M) (DW Rule')  ->
   OOCut n' (S h1 + S h2) ->
   buildTheory Rule ->
   buildTheory Rule' ->
    FLLS (OLTheoryCut nPnN (pred n)) Gamma (M ++ N) (UP []).

Lemma ConstantRIGHT  C : ConnectiveRight (t_ccon C) (makeRRuleC C).
Proof with sauto.
  unfold ConnectiveRight; intros *.
   intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellConstant LTWell Hseq1'.
  * Cases H. 
     2:{ LLPerm ((⌈ t_ccon C ⌉) :: x0++M)... }
    rewrite <- H4 in H2.
    clear H4.
    inversion Hth'...
           -- permuteConstantL. 
           -- wellConstant LTWell Hseq2'.   
               Cases H0.
               2:{ rewrite <- app_comm_cons... }
               rewrite <- H7 in H5.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConPrincipalCase _ H5 H2).
               Cases H0. 
              rewrite <- H9 in H6.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConPrincipalCase _ H6 H2).
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
           -- permuteUnaryL.
           -- permuteUnaryL.
           -- permuteBinaryL.
           -- permuteBinaryL.
           -- permuteQuantifierL.
           -- permuteQuantifierL.
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
         - wellConstant LTWell Hseq2'.
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
         - wellConstant LTWell Hseq2'.
           -- Cases H2. 
               rewrite <- H11 in H9.
               rewrite <- H6 in H3.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.

               refine (ConPrincipalCase _ H9 H3).
               
               rewrite <- app_comm_cons...
           -- Cases H2. 
               rewrite <- H13 in H10.
               rewrite <- H6 in H3.
               rewrite Permutation_app_comm.
               apply WeakTheory with (theory := OLTheory nPnN ). auto using TheoryEmb1.
               refine (ConPrincipalCase _ H10 H3).
               
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
         - permuteUnaryL.
         - permuteUnaryL.
         - permuteBinaryL.
         - permuteBinaryL.
         - permuteQuantifierL.
         - permuteQuantifierL.
 Qed.        
                       

Lemma UnaryRIGHT C F : ConnectiveRight (t_ucon C F) (makeRRuleU C F).
Proof with sauto.
  unfold ConnectiveRight; intros *.
   intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellUnary LTWell Hseq1'.
  Cases H.
     2:{  PermuteLeft.
         cutOL H1 Hseq2.
         OLSolve.
         LLPerm ((⌈ t_ucon C F ⌉) ::(M++ x3))...
         apply H7...
         rewrite app_assoc_reverse... }
     2:{  PermuteLeft. 
        cutOL H3 Hseq2.
               LLtheory (makeRRuleU C F).
               LLtensor (@nil oo) (M++N). eauto.
               apply H7...
               rewrite app_assoc_reverse... }
         inversion Hth'...
         -   permuteConstantL.
         -   permuteConstantL. 
         - permuteUnaryL.
         - wellUnary LTWell Hseq2'.
            Cases H2. 
            
            rewrite <- H6 in H3. 
            rewrite <- H13 in H10. 
            rewrite Permutation_app_comm.
            refine(UnaPrincipalCase _ H3 _ _ HL')...
             PermuteLeft. 
              cutOL Hseq1 H8.
               rewrite H12 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H14...
               rewrite Permutation_assoc_comm...
              
PermuteLeft.
              cutOL Hseq1 H10.
                 LLtheory (makeLRuleU C0 F0).
             LLtensor (@nil oo) (M++N). eauto.
               apply H14...  
               rewrite Permutation_assoc_comm... 
         - permuteBinaryL.
         - permuteBinaryL.
         - permuteQuantifierL.
         - permuteQuantifierL.
  Qed.                               
    
Ltac doubleH H :=
let tH := type of H in
   let H := fresh H in assert(H:tH) by auto.

Lemma BinaryRIGHT C F G : ConnectiveRight (t_bcon C F G) (makeRRuleB C F G).
Proof with sauto.
   unfold ConnectiveRight; intros *.
    intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellBinary LTWell Hseq1'.
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
               apply H7...  rewrite app_assoc_reverse... }
         inversion Hth'...
         - permuteConstantL.
         - permuteConstantL. 
         - permuteUnaryL.
         - permuteUnaryL.
         - permuteBinaryL.
         - wellBinary LTWell Hseq2'.
           { Cases H2. 
            
            rewrite <- H13 in H10. 
            rewrite <- H6 in H3. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H3 _ _ HL')...
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
                 LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (M++N).
               apply H14...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H2. 
            
            rewrite <- H15 in H8. 
            rewrite <- H6 in H3. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H3 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H11.
            rewrite <- H15 in H14.
             rewrite H14 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bcon C0 F0 G0 ⌋) :: (x10 ++ N) ++ x4).
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
            LLPerm ( (⌊ t_bcon C0 F0 G0 ⌋) :: x3++(x10 ++ N)).
              apply H16...
              apply FLLNtoFLLS in H11...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H12. 
               rewrite <- H15 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) ( ((x9 ++ N) ++ x4)).
               apply H17...  
               rewrite Permutation_assoc_comm...
               apply FLLNtoFLLS in H13...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H13. 
               rewrite <- H15 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (x3++(x9 ++ N) ).
               apply H17...
               apply FLLNtoFLLS in H12...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
           { Cases H2. 
            
            rewrite <- H15 in H8. 
            rewrite <- H6 in H3. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H3 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H11.
             rewrite H14 in PosM.
             inversion PosM...
             OLSolve.
            cutOL Hseq1 H12.
             rewrite H14 in PosM.
             inversion PosM...
             OLSolve.
  LLPerm ( (⌊ t_bcon C0 F0 G0 ⌋) :: (x8 ++ N) ).
              apply H16...
            1-2:  rewrite Permutation_assoc_comm...
    
               PermuteLeft.
            cutOL Hseq1 H11.
            cutOL Hseq1 H12.
                LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (M++N).
               apply H16...  
               1-2: rewrite Permutation_assoc_comm... }
          - permuteQuantifierL.
         - permuteQuantifierL.
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
        -  permuteConstantL.
         -  permuteConstantL.
         - permuteUnaryL.
         - permuteUnaryL.
         - permuteBinaryL.
         - wellBinary LTWell Hseq2'.
           { Cases H3. 
            
            rewrite <- H15 in H12. 
            rewrite <- H8 in H1. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H1 _ _ HL')...
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
                 LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H3. 
            
            rewrite <- H8 in H1. 
            rewrite <- H17 in H10. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H1 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H13.
                         rewrite <- H17 in H16.
             rewrite H16 in PosM.
             inversion PosM...
             OLSolve.     
            LLPerm ( (⌊ t_bcon C0 F0 G0 ⌋) :: (x12 ++ N) ++ x6).
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
            LLPerm ( (⌊ t_bcon C0 F0 G0 ⌋) :: x5++(x12 ++ N)).
              apply H18...
              apply FLLNtoFLLS in H13...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H14. 
                          rewrite <- H17 in PosM.
             OLSolve.     
                LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) ( ((x11 ++ N) ++ x6)).
               apply H19...  
               rewrite Permutation_assoc_comm...
               apply FLLNtoFLLS in H15...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H15. 
               rewrite <- H17 in PosM.
               OLSolve.
                LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (x5++(x11 ++ N) ).
               apply H19...
               apply FLLNtoFLLS in H14...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
               
           { Cases H3. 
            
            rewrite <- H17 in H10. 
            rewrite <- H8 in H1. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H1 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H13.
            OLSolve.
            cutOL Hseq1 H14.
            OLSolve.
            LLPerm ( (⌊ t_bcon C0 F0 G0 ⌋) :: (x10 ++ N) ).
              apply H18...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H13.
            OLSolve.
            cutOL Hseq1 H14.
            OLSolve.
             LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (M ++ N).
               apply H18...
            1-2:  rewrite Permutation_assoc_comm... }
                           
          - permuteQuantifierL.
         - permuteQuantifierL.
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
         -  permuteConstantL.
         -  permuteConstantL.

         - permuteUnaryL.
         - permuteUnaryL.
         - permuteBinaryL.
         - wellBinary LTWell Hseq2'.
           { Cases H3. 
            
            rewrite <- H8 in H1. 
            rewrite <- H15 in H12. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H1 _ _ HL')...
             
             PermuteLeft.
              cutOL Hseq1 H10.
               rewrite H14 in PosM.
               OLSolve.
               rewrite <- app_comm_cons ...
               apply H16...
               rewrite Permutation_assoc_comm...
       PermuteLeft.
              cutOL Hseq1 H12.
                 LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (M++N).
               apply H16...  
               rewrite Permutation_assoc_comm... }
               
           { Cases H3. 
            
            rewrite <- H8 in H1. 
            rewrite <- H17 in H10. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H1 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H13.
             rewrite <- H17 in H16.
             rewrite H16 in PosM.
             inversion PosM...
             OLSolve.   
            LLPerm ( (⌊ t_bcon C0 F0 G0 ⌋) :: (x11 ++ N) ++ x5).
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
            LLPerm ( (⌊ t_bcon C0 F0 G0 ⌋) :: x4++(x11 ++ N)).
              apply H18...
              apply FLLNtoFLLS in H13...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
              rewrite Permutation_assoc_comm...
               
               PermuteLeft.
               cutOL Hseq1 H14. 
                rewrite <- H17 in PosM.
             OLSolve.   
                LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) ( ((x10 ++ N) ++ x5)).
               apply H19...  
               rewrite Permutation_assoc_comm...
               apply FLLNtoFLLS in H15...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                PermuteLeft.
               cutOL Hseq1 H15. 
                rewrite <- H17 in PosM.
             OLSolve.   
                LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (x4++(x10 ++ N) ).
               apply H19...
               apply FLLNtoFLLS in H14...
               apply WeakTheory with (theory := OLTheory nPnN )... auto using TheoryEmb1.
                 
               rewrite Permutation_assoc_comm... }
               
           { Cases H3. 
            
            rewrite <- H8 in H1. 
            rewrite <- H17 in H10. 
            rewrite Permutation_app_comm.
            refine(BinPrincipalCase _ H1 _ _ HL')...
            
            PermuteLeft.
            cutOL Hseq1 H13.
            OLSolve.
            cutOL Hseq1 H14.
            OLSolve.
            LLPerm ((⌊ t_bcon C0 F0 G0 ⌋) :: (x9 ++ N) ).
              apply H18...
            1-2:  rewrite Permutation_assoc_comm...
 
             PermuteLeft.
            cutOL Hseq1 H13.
            cutOL Hseq1 H14.
             LLtheory (makeLRuleB C0 F0 G0).
             LLtensor (@nil oo) (M ++ N).
               apply H18...
            1-2:  rewrite Permutation_assoc_comm... }
                           
          - permuteQuantifierL.
         - permuteQuantifierL.         
  Qed.                        
   

Lemma QuantifierRIGHT C FX : uniform FX -> ConnectiveRight (t_qcon C FX) (makeRRuleQ C FX).
Proof with sauto.
  intro Hu.
 unfold ConnectiveRight ; intros *.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellQuantifier LTWell Hseq1'.
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
           --  permuteConstantL.
           --  permuteConstantL.
           -- permuteUnaryL.
           -- permuteUnaryL.
           -- permuteBinaryL.
           -- permuteBinaryL.
           -- permuteQuantifierL.           
           -- wellQuantifier LTWell Hseq2'.
               destruct H5...
               checkPermutationCases H5.
               inversion H13...
               rewrite <- H6 in H3.
               rewrite <- H14 in H11.
               rewrite Permutation_app_comm.
               refine (QuaPrincipalCase H11 H3 _ _ _ _ _ _ HL')...   
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
            
 
 (** Main theorem showing that it is possible to fins a proof with
  the theory [ (OLTheoryCut nPnN (pred n))] *)
  Theorem OLCutElimStep :
    forall h1 h2 n N M Gamma FCut n',
      isOLFormula FCut ->
      posAtomFormulaL Gamma ->
      posAtomFormulaL N ->
      posAtomFormulaL M ->
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
       - permuteConstantR.
       - refine(UnaryRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)... 
       - permuteUnaryR. 
       - refine(BinaryRIGHT 
                           HL' 
                           H7 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)... 
       - permuteBinaryR. 
       - refine(QuantifierRIGHT 
                           H7 HL' 
                           H9 
                           HisF _ _ _ _ 
                           Hseq1 
                           Hseq2 _ _ _ _ 
                           H8)...        
       - permuteQuantifierR. 
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
      posAtomFormulaL B ->
      posAtomFormulaL N ->
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
         wellConstant LTWell H2.
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
         wellConstant LTWell H2.
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
         wellUnary LTWell H2.
         Cases H6.
         apply H14... 
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeRRuleU C F0).
         LLtensor (@nil oo) N. eauto.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
      + (* unary *)
         wellUnary LTWell H2.
         Cases H6. 
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
         LLtheory (makeLRuleU C F0).
         LLtensor (@nil oo) N.  eauto.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
      + (* binary *)
         wellBinary LTWell H2.
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
         wellBinary LTWell H2.
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
         wellQuantifier LTWell H2.
         Cases H7.
         apply H15...
         refine (H _ _ _ _ _ _ H9)...
         OLSolve.
         LLtheory (makeRRuleQ C FX).
         LLtensor (@nil oo) N.  eauto.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
      + (* quantifier *)
         wellQuantifier LTWell H2.
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
      posAtomFormulaL B ->
      posAtomFormulaL N ->
      FLLN (OLTheoryCut nPnN n) h  B N (UP [] ) ->
      FLLS (OLTheory nPnN) B N (UP [] ) .
  Proof with sauto.
    intros. 
    apply OLCutElimAux in H1 ...
    eapply WeakTheory with (theory':= OLTheory nPnN) in H1 ...
    apply OOTheryCut0.
  Qed.     
  
End CutElimination.
