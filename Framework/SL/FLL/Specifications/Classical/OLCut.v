(** * LL as a Meta-logical framework.  *)

(** In this file we show how the cut-elimination procedure for FLL can
be used to prove cut-elimination for object logics that are
cut-coherent in the sense of Miller & Pimentel. Roughly, a system is
cut-coherent if the encoding of the right and left rules of each
connective are dual. *)

Require Export LL.Framework.SL.FLL.Specifications.StructuralClauses. 
Require Export LL.Framework.SL.FLL.Specifications.OLTheory.
Require Export LL.Framework.SL.FLL.Specifications.WellHyp.
Require Export LL.Framework.OL.SyntaxResults.  

Require Import Coq.Init.Nat.
Require Import LL.Framework.SL.FLL.CutElimination.
Import LL.Misc.Permutations.
Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(** ** Cut Elimination Procedure *)
Section CutElimination .
  Context `{OLR: OORules}.

  (** As a general hypothesis, we assume that the Object logic is cut-coherent *)
  Hypothesis LTWell : wellFormedTheory.
  Hypothesis LTCutCo: CutCoherence cutR1.

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
                  FLLN (OLTheory PN) h1 (atom (up FCut)::Gamma) N (UP [] ) ->
                  FLLN (OLTheory PN) h2 (atom (down FCut)::Gamma) M (UP []) -> FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
                  
 Ltac applyOOCut := 
  match goal with
  | [ H: OOCut _ _ |- 
         FLLN ?th ?x (?FF::?BX) ?N (UP []) -> 
         FLLN ?th ?y (?GG::?BX) ?M (UP [])-> 
         FLLS ?thc ?BX (?M++?N) (UP []) ] => eapply H
  | _ => idtac end.
  
Ltac cutOL P1 P2 :=
   let tP1 := type of P1 in
   let tP2 := type of P2 in
   let H' := fresh "OLCut" in
   match tP1 with
   | FLLN ?th ?h1 (atom (up ?FC) :: ?B) ?N (UP []) => 
          match tP2 with 
          | FLLN ?th ?h2 (atom (down ?FC) :: ?B) ?M (UP []) =>  
           match goal with
           | [ H: OOCut ?n' _, Hn: ?n' <= ?n  |- _ ] =>    assert(H': tP1 -> tP2 -> FLLS (OLTheoryCut PN (pred n)) B (M++N) (UP []));applyOOCut
           end
           | _ => idtac "type of " P2 " is " tP2 end
   | _ => idtac "type of " P1 " is " tP1 end;sauto.
   

 Theorem ConstantPrincipalCase :
    forall n Gamma M N C,
      (FLLS (OLTheoryCut PN n) Gamma M (DW (rc_lftBody (rulesC C)))) ->
      (FLLS (OLTheoryCut PN n) Gamma N (DW (rc_rgtBody (rulesC C)))) ->
      FLLS (OLTheoryCut PN n) Gamma (N ++ M) (UP []).
(* begin show *)
     Proof with sauto.     
    intros.
    apply FLLStoFLLN in H... 
    apply FLLStoFLLN in H0...
    generalize(ctCutCo LTCutCo C);intro CutC.
    unfold CutCoherenceC in CutC.
    destruct CutC as [Hc CutC]. 
    apply EmptySubSet with (theory:= (OLTheoryCut PN n) ) in CutC.
    apply weakeningGen with (CC':= Gamma) in CutC .
    apply FLLStoFLLN in CutC.   destruct CutC as [h CutC].
    rewrite app_nil_r in CutC.
    assert(HCut1: FLLS (OLTheoryCut PN n) Gamma ([] ++ N)  ( UP [ dual (rc_lftBody (rulesC C))])).
    eapply @GeneralCut with  (C:=  dual (rc_rgtBody (rulesC C)));eauto. 
    rewrite <- dualInvolutive;eauto.
    (* end show *)
    
    apply FLLStoFLLN in HCut1.  destruct HCut1 as [h2 HCut1].
    eapply @GeneralCut with  (C:= dual (rc_lftBody (rulesC C)) ); eauto. 
    rewrite <- dualInvolutive;eauto.
  Qed.
  
  (** This is the case when a unary connective is principal in both premises *)
  Theorem UConnectivePrincipalCase :
    forall Gamma M N C F n n',
      (FLLS (OLTheoryCut PN (pred n)) Gamma M (DW (ru_lftBody (rulesU C) F))) ->
      (FLLS (OLTheoryCut PN (pred n)) Gamma N (DW (ru_rgtBody (rulesU C) F))) ->
      (lengthUexp (t_ucon C F) n') ->
      isOLFormula (t_ucon C F) ->
      n' <= n ->
      FLLS (OLTheoryCut PN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply FLLStoFLLN in H.     
    apply FLLStoFLLN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize( unCutCo LTCutCo  C);intro CutC.
    unfold CutCoherenceU in CutC.
    
    generalize (CutC F n1);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply FLLStoFLLN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCut PN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCut PN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCut PN n) in H0;auto using TheoryEmb1.
    assert(Cut1': FLLS (OLTheoryCut PN n) Gamma ([] ++ N) ( UP[dual (ru_lftBody (rulesU C) F)] )).
    eapply @GeneralCut with(C := dual (ru_rgtBody (rulesU C) F) ) ;eauto.
    
    rewrite <- dualInvolutive;eauto.

    apply FLLStoFLLN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:=dual (ru_lftBody (rulesU C) F)); eauto.
    rewrite <- dualInvolutive;eauto.
  Qed.
  
  (** This is the case when a binary connective is principal in both premises *)
  Theorem BinConnectivePrincipalCase :
    forall Gamma M N C F G n n',
      (FLLS (OLTheoryCut PN (pred n)) Gamma M (DW (rb_lftBody (rulesB C) F G))) ->
      (FLLS (OLTheoryCut PN (pred n)) Gamma N (DW (rb_rgtBody (rulesB C) F G))) ->
      lengthUexp (t_bcon C F G) n' ->
      isOLFormula (t_bcon C F G) ->
      n' <= n ->
      FLLS (OLTheoryCut PN (pred n)) Gamma (N ++ M) (UP []).
  Proof with sauto.
    intros.
    inversion H1;subst.
    inversion H2;subst. inversion H4.
    destruct n ;[ lia | simpl].
    apply FLLStoFLLN in H.     apply FLLStoFLLN in H0.
    destruct H as [h1 H].
    destruct H0 as [h2 H0].

    generalize (biCutCo LTCutCo  C);intro CutC.
    unfold CutCoherenceB in CutC.
    
    generalize (CutC F G n1 n2);intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply FLLStoFLLN in Cut1. destruct Cut1 as [hh  Cut1].
    apply WeakTheoryN with (theory' := OLTheoryCut PN n) in Cut1;auto using TheoryEmb2.
    apply weakeningGenN with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheoryN with (theory' := OLTheoryCut PN n) in H;auto using TheoryEmb1.
    apply WeakTheoryN with (theory' := OLTheoryCut PN n) in H0;auto using TheoryEmb1.
    
    assert(Cut1': FLLS (OLTheoryCut PN n) Gamma ([] ++ N) ( UP[dual (rb_lftBody (rulesB C) F G) ] )).
    eapply @GeneralCut with (C :=dual (rb_rgtBody (rulesB C) F G) ) ;eauto.
    rewrite <- dualInvolutive;eauto.
 
    apply FLLStoFLLN in Cut1'.  destruct Cut1' as [h3 Cut1'].
    eapply @GeneralCut with (C:= dual (rb_lftBody (rulesB C) F G)); eauto.     rewrite <- dualInvolutive;eauto.
  Qed.

(*  Axiom OLSize: forall FX t t' n, uniform FX -> proper t -> proper t' -> lengthUexp (FX t) n -> lengthUexp (FX t') n . *)

  (** This is the case when a quantifier is principal in both premises *)
  Theorem QuantifierPrincipalCase :
    forall Gamma M N C FX FX0 n n',
      (FLLS (OLTheoryCut PN (pred n)) Gamma M (DW (rq_lftBody (rulesQ C) FX0))) ->
      (FLLS (OLTheoryCut PN (pred n)) Gamma N (DW (rq_rgtBody (rulesQ C) FX))) ->
      isOLFormula (t_qcon C FX) ->
      isOLFormula (t_qcon C FX0) ->
      lengthUexp (t_qcon C FX) n' ->
      uniform FX -> uniform FX0 ->
      lbind 0%nat FX0 = lbind 0%nat FX ->
      n' <= n ->
      FLLS (OLTheoryCut PN (pred n)) Gamma (N ++ M) (UP []).
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
    generalize (quCutCo LTCutCo  C) ;intro CutC.
    assert (Hsize: lengthUexp (FX (Var 0%nat)) n0).
    { rewrite H17...  apply proper_VAR.  }
    assert(HIs: (forall t : expr Econ, proper t -> isOLFormula (FX t))).
    {intros t pt. rewrite H12... }
    unfold CutCoherenceQ in *.
    generalize (CutC FX FX0 n0); intro Cut1. clear CutC.
    apply CuteRuleNBound' with (m:= n) in Cut1...
    apply WeakTheory with (theory' := OLTheoryCut PN n) in Cut1;auto using TheoryEmb1.
    apply weakeningGen with (CC':= Gamma) in Cut1 .
    rewrite app_nil_r in Cut1.
    apply WeakTheory with (theory' := OLTheoryCut PN n) in H;auto using TheoryEmb1.
    apply WeakTheory with (theory' := OLTheoryCut PN n) in H0;auto using TheoryEmb1.
   
    apply FLLStoFLLN in H.  apply FLLStoFLLN in H0. apply FLLStoFLLN in Cut1.
    destruct H as [h1 H]. 
    destruct H0 as [h2 H0]. destruct Cut1 as [h3 Cut1].
    

    assert(Cut1': FLLS (OLTheoryCut PN n) Gamma ([] ++ N) ( UP[dual (rq_lftBody (rulesQ C) FX0)] )).
    eapply @GeneralCut with  (C :=dual (rq_rgtBody (rulesQ C) FX)) ;eauto.
    rewrite <- dualInvolutive;eauto.
    simpl in Cut1'.
    apply FLLStoFLLN in Cut1'.
    destruct Cut1' as [h4 Cut1']. 

    
    eapply @GeneralCut with (C :=dual (rq_lftBody (rulesQ C) FX0)) ;eauto.
    rewrite <- dualInvolutive;eauto.
  Qed.


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
       |[ Hr: FLLN _ ?x (( (⌊ ?F ⌋)::?G) ++ ?Y1) (?X1 ++ _) (UP []),  
       Hr': FLLN _ ?x (( (⌊ ?F ⌋)::?G) ++ ?Y2) (?X2 ++ _) (UP []),              
       Hl: FLLN ?th ?n ( (⌈ ?F ⌉) ::?G) ?N (UP []) |- _] =>
   assert(Hl': FLLN th n ( (⌈ F ⌉) ::G) N (UP []) ) by auto; 
   apply weakeningGenN_rev with (CC':= Y1) in Hl;
   apply weakeningGenN_rev with (CC':= Y2) in Hl';
    rewrite <- app_comm_cons in Hr, Hr', Hl, Hl'  
   |[ Hr: FLLN _ ?x (?G ++ ?Y1) (?X ++ _) (UP []),   
        Hr': FLLN _ ?x (?G ++ ?Y2) (?X ++ _) (UP []),             
       Hl: FLLN ?th ?n ?G ( (⌈ ?F ⌉) :: ?N) (UP []),
       Hp: Permutation ( (⌊ ?F ⌋) :: _) ?X |- _] =>
   assert(Hl': FLLN th n G ( (⌈ F ⌉) :: N) (UP [])) by auto; 
   apply weakeningGenN_rev with (CC':= Y1) in Hl;
   apply weakeningGenN_rev with (CC':= Y2) in Hl';
   rewrite <- Hp in Hr, Hr';
    rewrite <- app_comm_cons in Hr, Hr'    
       |[ Hr: FLLN _ ?x (( (⌊ ?F ⌋)::?G) ++ ?Y) (?X ++ _) (UP []),               
       Hl: FLLN _ ?n ( (⌈ ?F ⌉) ::?G) ?N (UP []) |- _] =>
       apply weakeningGenN_rev with (CC':= Y) in Hl;
       rewrite <- app_comm_cons in Hr,Hl
   |[ Hr: FLLN _ ?x (?G ++ ?Y) (?X ++ _) (UP []),               
       Hl: FLLN _ ?n ?G ( (⌈ ?F ⌉) :: ?N) (UP []) |- _] =>
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
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL Gamma ->
buildTheory (makeRRuleU C F) ->
FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M
     (DW (makeRRuleU C F)) ->
FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellUnary LTWell H9.
  * Cases H10.
     - cutOL H8 H12.
        do 2 OLSolve.
        rewrite <- app_comm_cons.
        apply H18...
        rewrite Permutation_assoc_comm...
     - inversion H12...
        cutOL H8 H14.
         OLSolve.
        LLtheory (makeRRuleU C F).
        LLtensor (@nil oo) (M++N).
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
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL Gamma ->
buildTheory (makeLRuleU C F) ->
FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M
     (DW (makeLRuleU C F)) ->
FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellUnary LTWell H10.
  * Cases H11.
     - cutOL H9 H13.
        do 2 OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - inversion H13...
        inversion H11...
        cutOL H9 H15.
        OLSolve.
        LLtheory (makeLRuleU C F).
        LLtensor (@nil oo) (M++N).
        apply H19...
        rewrite Permutation_assoc_comm...  
Qed. 

Lemma OLCutHasPos n: hasPos (OLTheoryCut PN n).
Proof with sauto.
   intro.
   intros. constructor.
   apply ooth_strpos... simpl...
Qed.
   
Lemma OLCutHasNeg n: hasNeg (OLTheoryCut PN n).
Proof with sauto.
   intro.
   intros. constructor.
   apply ooth_strneg... simpl...
Qed.
 
 Lemma OLHasPos: hasPos (OLTheory PN).
Proof with sauto.
   intro.
   intros.
   apply ooth_strpos... simpl...
Qed.
   
Lemma OLHasNeg: hasNeg (OLTheory PN).
Proof with sauto.
   intro.
   intros.
   apply ooth_strneg... simpl...
Qed.

 #[local] Hint Resolve OLCutHasPos OLCutHasNeg : core. 

Ltac clearNotFormulas :=
repeat
multimatch goal with
| [ H: _ |- posAtomFormulaL _] => 
    let tH := type of H in 
    match tH with
     | Permutation _ _ => idtac
     | posAtomFormula _ => idtac
     | posAtomFormulaL _ => idtac
     | _ => clear H
    end 
end.


(** Binary Right is not principal on the left branch *) 
Lemma BinaryRightNotPrincipalL n n' n0 n1 C FCut F G Gamma M N: 
 n' <= n ->
OOCut n' (S n0 + S n1) ->
lengthUexp FCut n' ->
isOLFormula FCut ->
isOLFormula (t_bcon C F G) ->
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL Gamma ->
buildTheory (makeRRuleB C F G) ->
FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M
     (DW (makeRRuleB C F G)) ->
FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellBinary LTWell H9.
  * Cases H10.
     - cutOL H8 H12.
        clearNotFormulas.
        do 2 OLSolve.
        rewrite <- app_comm_cons.
        apply H18...
        rewrite Permutation_assoc_comm...
     - inversion H12...
        cutOL H8 H14.
        OLSolve.
        LLtheory (makeRRuleB C F G).
        LLtensor (@nil oo) (M++N). 
        apply H18...
        rewrite Permutation_assoc_comm...
  * Cases H10.
     - cutOL H8 H15.
       clearNotFormulas.
       OLSolve.
        rewrite H14 in H4.
        inversion H4... 
        OLSolve.
        cutOL H8 H16.
        clearNotFormulas.
        OLSolve.
        rewrite H14 in H4.
        inversion H4... 
        OLSolve.
        apply ContractionLinear...
        LLPerm(( (⌈ t_bcon C F G ⌉) :: x ++ N) ++ x0 ++ N).
        apply H20...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
      - inversion H14...
        cutOL H8 H16.
        do 2 OLSolve.
        cutOL H8 H17.
        do 2 OLSolve.
        apply ContractionLinear...
        rewrite H12.
        LLPerm ((x++N)++(x0++N)).
        LLtheory (makeRRuleB C F G).
        LLtensor (@nil oo) ((x ++ N) ++ x0 ++ N). 
        apply H21...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
  * Cases H10.
     - cutOL H8 H15.
       do 2 OLSolve.
        cutOL H8 H16.
        do 2 OLSolve.
        rewrite <- app_comm_cons.
        apply H20...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
      - inversion H14...
        cutOL H8 H15.
        OLSolve.
        cutOL H8 H16.
        OLSolve.
        LLtheory (makeRRuleB C F G).
        LLtensor (@nil oo) (M ++ N). 
        apply H20...
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
posAtomFormulaL Gamma ->
buildTheory (makeLRuleB C F G) ->
FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M
     (DW (makeLRuleB C F G)) ->
FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellBinary LTWell H10.
  * Cases H11.
     - cutOL H9 H13.
        do 2 OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - inversion H13...
        inversion H11...
        cutOL H9 H15.
        OLSolve.
        LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) (M++N).
        apply H19...
        rewrite Permutation_assoc_comm...
  * Cases H11.
     -cutOL H9 H16.
       clearNotFormulas.
         OLSolve.
        rewrite H15 in H5.
        inversion H5... 
        OLSolve.
        cutOL H9 H17.
        clearNotFormulas.
         OLSolve.
        rewrite H15 in H5.
        inversion H5... 
        OLSolve. 
        apply ContractionLinear...
        LLPerm(( (⌊ t_bcon C F G ⌋) :: x ++ N) ++ x0 ++ N).
        apply H21...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
      - inversion H15...
        inversion H11...
        cutOL H9 H17.
        do 2 OLSolve.
        cutOL H9 H18.
        do 2 OLSolve.
        apply ContractionLinear...
        rewrite H13.
        LLPerm ((x++N)++(x0++N)).
        LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) ((x++N)++(x0++N)).
        apply H22...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
  * Cases H11.
     - cutOL H9 H16.
        do 2 OLSolve.
        cutOL H9 H17.
        do 2 OLSolve.
        rewrite <- app_comm_cons.
        apply H21...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm...
      - inversion H15...
        inversion H11...
        cutOL H9 H16.
        OLSolve.
        cutOL H9 H17.
        OLSolve.
        LLtheory (makeLRuleB C F G).
        LLtensor (@nil oo) ((M++N)).
        apply H21...
        rewrite Permutation_assoc_comm...
        rewrite Permutation_assoc_comm... 
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
posAtomFormulaL Gamma ->
buildTheory (makeRRuleQ C FX) ->
FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M
     (DW (makeRRuleQ C FX)) ->
FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellQuantifier LTWell H9.
  * Cases H10.
     - cutOL H8 H12.
        do 2 OLSolve.
        rewrite <- app_comm_cons.
        apply H18...
        rewrite Permutation_assoc_comm...
     - inversion H12...
        cutOL H8 H14.
        OLSolve.
        LLtheory (makeRRuleQ C FX).
        LLtensor (@nil oo) (M++N).
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
posAtomFormulaL M ->
posAtomFormulaL N ->
posAtomFormulaL Gamma ->
buildTheory (makeLRuleQ C FX) ->
FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M
     (DW (makeLRuleQ C FX)) ->
FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros.
  wellQuantifier LTWell H10.
  * Cases H11.
     - cutOL H9 H13.
        do 2 OLSolve.
        rewrite <- app_comm_cons.
        apply H19...
        rewrite Permutation_assoc_comm...
     - inversion H13...
       inversion H11...
        cutOL H9 H15.
        OLSolve.
        LLtheory (makeLRuleQ C FX).
        LLtensor (@nil oo) (M++N).
        apply H19...
        rewrite Permutation_assoc_comm...
 Qed.


Ltac permuteUnary :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ (_ :: ?G) ?N (UP []) ,
   Hr : FLLN _ _ (_ :: ?G) ?M (DW (makeRRuleU _ _))
  |-  FLLS _ ?G (?M ++ ?N) (UP []) ] =>
   refine (UnaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
      
| [H: ?n' <= ?n,
   Hl: FLLN _ _ (_ :: ?G) ?N (UP []) ,
   Hr : FLLN _ _ (_ :: ?G) ?M (DW (makeLRuleU _ _))
  |-  FLLS _ ?G (?M ++ ?N) (UP []) ] =>
refine (UnaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.     
 
       
 
Ltac permuteBinary :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ (_ :: ?G) ?N (UP []) ,
   Hr : FLLN _ _ (_ :: ?G) ?M (DW (makeRRuleB _ _ _))
  |-  FLLS _ ?G (?M ++ ?N) (UP []) ] =>
   refine (BinaryRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: FLLN _ _ (_ :: ?G) ?N (UP []) ,
   Hr : FLLN _ _ (_ :: ?G) ?M (DW (makeLRuleB _ _ _))
  |-  FLLS _ ?G (?M ++ ?N) (UP []) ] =>
refine (BinaryLeftNotPrincipalL _ H _ _ _ _ _ _ _ _ Hl Hr);
  sauto;
  intro Hf; inversion Hf  
 end.    
 
 Ltac permuteQuantifier :=
match goal with
| [H: ?n' <= ?n,
   Hl: FLLN _ _ (_ :: ?G) ?N (UP []) ,
   Hr : FLLN _ _ (_ :: ?G) ?M (DW (makeRRuleQ _ _))
  |-  FLLS _ ?G (?M ++ ?N) (UP []) ] =>
   refine (QuantifierRightNotPrincipalL H _ _ _ _ _ _ _ _ Hl Hr);sauto
| [H: ?n' <= ?n,
   Hl: FLLN _ _ (_ :: ?G) ?N (UP []) ,
   Hr : FLLN _ _ (_ :: ?G) ?M (DW (makeLRuleQ _ _))
  |-  FLLS _ ?G (?M ++ ?N) (UP []) ] =>
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
  posAtomFormulaL Gamma ->
  FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
  FLLN (OLTheory PN) (S n1) ( (⌊ FCut ⌋) :: Gamma) M (UP []) ->
  FLLN (OLTheory PN) n0 ( (⌈ FCut ⌉) :: Gamma) N (DW (makeRRuleC C)) ->
  FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleC C) ->
  buildTheory F0 ->
  FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellConstant LTWell Hseq1'.
  * Cases H. 
     + LLPerm ( (⌈ t_ccon C ⌉) :: x++M)...
     + inversion H0...
         inversion H...
         - inversion H2... 
           assert( rc_lftBody (rulesC C) = Zero).
           generalize( ctCutCo LTCutCo C).
           intro CutC.
           unfold CutCoherenceC in CutC.
           inversion CutC...
           rewrite H1 in H5.
           apply dualRev in H5...
           inversion Hth'...
           -- wellConstant LTWell Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               inversion H4...
               Cases H1. 
               cutOL Hseq1 H6.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H12...
               LLPerm ((x2 ++ x) ++ N)...
               inversion H6...
               cutOL Hseq1 H8.
               OLSolve.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H12...
               LLPerm ( (M ++ x) ++ N)...
           -- wellConstant LTWell Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               inversion H4...
               inversion H1...
               rewrite H in H7.
               inversion H7...
               Cases H1. 
               cutOL Hseq1 H6.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H12...
               LLPerm ((x2 ++ x) ++ N)...
               inversion H6...
               inversion H1...
               rewrite H in H7.
               inversion H7... inversion H6.
               cutOL Hseq1 H8.
               OLSolve.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H12...
               LLPerm ( (M ++ x) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.
           -- permuteQuantifier.
(** 1.2 ONE PREMISSE *)        
  * Cases H.
     + cutOL H1 Hseq2.
        do 2  OLSolve.
         LLPerm ( (⌈ t_ccon C ⌉) ::(M++ x2))...
         apply H7...
         rewrite app_assoc_reverse...
     + inversion H1... 
         inversion H...
         inversion Hth'...
         - wellConstant LTWell Hseq2'.
           -- Cases H1. 
               rewrite <- app_comm_cons...
               inversion H5...
           -- Cases H1. 
               rewrite <- app_comm_cons...
               cutOL Hseq1 H6.
               do 2 OLSolve.
               apply H13...
               rewrite Permutation_assoc_comm...
               inversion H6...
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               rewrite Permutation_assoc_comm...
         - wellConstant LTWell Hseq2'.
           -- Cases H1. 
               rewrite <- app_comm_cons...
               inversion H5...
               inversion H1...
               generalize( ctCutCo LTCutCo C0).
               intro CutC.
               unfold CutCoherenceC in CutC.
               inversion CutC...
               inversion H8... 
               rewrite <- H13 in H6.
               rewrite H6 in H2... 
               inversion H2...
               inversion H5.
           -- Cases H1. 
               rewrite <- app_comm_cons...
               cutOL Hseq1 H6.
               do 2 OLSolve.
               apply H13...
               rewrite Permutation_assoc_comm...
               inversion H6...
               inversion H1...
               cutOL Hseq1 H9.
               OLSolve.
               cutOL H3 Hseq2.
               OLSolve.
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rc_lftBody (rulesC C0)))).
               apply H13...
               LLPerm ((M ++ x2) ++ N)...
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rc_rgtBody (rulesC C0)))).
               apply H7...
               LLPerm (M ++ N ++ x)...
               apply ContractionLinear...
               LLPerm ((N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N)).
               refine (ConstantPrincipalCase _ H1 H6).
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               rewrite Permutation_assoc_comm...
         - permuteUnary.
         - permuteUnary.
         - permuteBinary.
         - permuteBinary.
         - permuteQuantifier.
         - permuteQuantifier.
         -    cutOL H3 Hseq2.
               OLSolve.
               LLtheory (makeRRuleC C).
               LLtensor (@nil oo) (M++N).
               apply H7...
               rewrite app_assoc_reverse...
Qed.               

Lemma UnaryRIGHT n n' n0 n1  C F FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_ucon C F) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
  FLLN (OLTheory PN) (S n1) ( (⌊ FCut ⌋) :: Gamma) M (UP []) ->
  FLLN (OLTheory PN) n0 ( (⌈ FCut ⌉) :: Gamma) N (DW (makeRRuleU C F)) ->
  FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleU C F) ->
  buildTheory F0 ->
  FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellUnary LTWell Hseq1'.
  * Cases H. 
     + cutOL H1 Hseq2.
         do 2 OLSolve.
         LLPerm ( (⌈ t_ucon C F ⌉) ::(M++ x2))...
         apply H7...
         rewrite app_assoc_reverse...
     + inversion H1... 
         inversion H...
         - inversion Hth'... 
           -- wellConstant LTWell Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H1. 
               cutOL Hseq1 H6.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ N)...
               inversion H6...
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               LLPerm ( (M ++ x2) ++ N)...
           -- wellConstant LTWell Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H1. 
               cutOL Hseq1 H6.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ N)...
               inversion H6...
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               LLPerm ( (M ++ x2) ++ N)...
           -- permuteUnary.
           -- wellUnary LTWell Hseq2'. 
               Cases H1.
               cutOL Hseq1 H6.
               do 2 OLSolve.
               LLPerm ( (⌊ t_ucon C0 F1 ⌋) :: x5++ N).
               apply H13...
               LLPerm ((x5 ++ x2) ++ N)...
               inversion H6...
               inversion H1...
               cutOL Hseq1 H9.
               OLSolve.
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (ru_lftBody (rulesU C0) F1) )).
               apply H13...
               LLPerm ((M ++ x2) ++ N)...
               
               cutOL H3 Hseq2.
               OLSolve.
               
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (ru_rgtBody (rulesU C0) F1) )).
               apply H7...
               LLPerm (M ++ N ++ x)...
               apply ContractionLinear...
               LLPerm ((N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N)).
               refine (UConnectivePrincipalCase H1 H6 _ _ HL')...
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeLRuleU C0 F1).
               LLtensor (@nil oo) (M++N).
               apply H13...
               LLPerm ( (M ++ x2) ++ N)...
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.
           -- permuteQuantifier.
         - cutOL H3 Hseq2.
            OLSolve.
            LLtheory (makeRRuleU C F).
            LLtensor (@nil oo) (M++N).
            apply H7...
            LLPerm (M++N++x)...
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
  posAtomFormulaL Gamma ->
  FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
  FLLN (OLTheory PN) (S n1) ( (⌊ FCut ⌋) :: Gamma) M (UP []) ->
  FLLN (OLTheory PN) n0 ( (⌈ FCut ⌉) :: Gamma) N (DW (makeRRuleB C F G)) ->
  FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleB C F G) ->
  buildTheory F0 ->
  FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth'.
  wellBinary LTWell Hseq1'.
  * Cases H. 
     + cutOL H1 Hseq2.
         do 2 OLSolve.
         LLPerm ( (⌈ t_bcon C F G ⌉) ::(M++ x2))...
         apply H7...
         rewrite app_assoc_reverse...
     + inversion H1... 
         inversion H...
         - inversion Hth'... 
           -- wellConstant LTWell Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H1. 
               cutOL Hseq1 H6.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ N)...
               inversion H6...
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               LLPerm ( (M ++ x2) ++ N)...
           -- wellConstant LTWell Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H1. 
               cutOL Hseq1 H6.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ N)...
               inversion H6...
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               LLPerm ( (M ++ x2) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- wellBinary LTWell Hseq2'. 
               { Cases H1.
               cutOL Hseq1 H6.
               do 2 OLSolve.
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x5++ N).
               apply H13...
               LLPerm ((x5 ++ x2) ++ N)...
               inversion H6...
               inversion H1...
               cutOL Hseq1 H9.
               OLSolve.
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               apply H13...
               LLPerm ((M ++ x2) ++ N)...
               
               cutOL H3 Hseq2.
               OLSolve.
               
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
               apply H7...
               LLPerm (M ++ N ++ x)...
               apply ContractionLinear...
               LLPerm ((N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N)).
               refine (BinConnectivePrincipalCase H1 H6 _ _ HL')...
            
              cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               LLPerm ( (M ++ x2) ++ N)... }
               { Cases H1.
               cutOL Hseq1 H10.
               clearNotFormulas.
                OLSolve.
                rewrite H9 in PosM.
               inversion PosM... 
               OLSolve.
               cutOL Hseq1 H11.
               clearNotFormulas.
                OLSolve.
                rewrite H9 in PosM.
               inversion PosM... 
               OLSolve.
               LLPerm (( (⌊  t_bcon C0 F1 G0 ⌋) :: x2 ++ x3) ++ N).
               apply ContractionLinear...
               LLPerm (( (⌊  t_bcon C0 F1 G0 ⌋) :: (N++x2) ++ (N++x3))).
               apply H15...
               LLPerm ((x2 ++ x4) ++ N)...
               LLPerm ((x3 ++ x5) ++ N)...
               inversion H9...
               inversion H1...
               cutOL Hseq1 H11.
               clearNotFormulas.
               OLSolve.
                rewrite H6 in PosM.
               OLSolve.
             cutOL Hseq1 H12.
             clearNotFormulas.
                OLSolve.
                rewrite H6 in PosM.
               OLSolve.
                cutOL H3 Hseq2.
             clearNotFormulas.
                OLSolve.
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               rewrite H6...
               LLPerm ((x2++N)++(x3++N)). 
               apply H16...
               LLPerm ((x2 ++ x4) ++ N)...
               LLPerm ((x3 ++ x5) ++ N)...
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
               apply H7...
               LLPerm(M ++ N ++ x)...
               
               apply ContractionLinear...
               rewrite app_assoc.
                apply ContractionLinear...
               LLPerm ((N++N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N++N)).
               refine (BinConnectivePrincipalCase H1 H9 _ _ HL')...
               cutOL Hseq1 H11.
               clearNotFormulas.
                OLSolve.
                rewrite H6  in PosM.
               OLSolve.
               cutOL Hseq1 H12.
               clearNotFormulas.
                OLSolve.
                rewrite H6  in PosM.
               OLSolve.

               apply ContractionLinear...
               rewrite H6...
               LLPerm ((x2++N)++(x3++N)).
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) ( (x2 ++ N) ++ x3 ++ N).
               apply H16...
               LLPerm ((x2 ++ x4) ++ N)...
               LLPerm ((x3 ++ x5) ++ N)... }
               { Cases H1.
               cutOL Hseq1 H10.
               do 2 OLSolve.
               cutOL Hseq1 H11.
               do 2 OLSolve.
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x2 ++ N).
               apply H15...
               LLPerm ((x2 ++ x3) ++ N)...
               LLPerm ((x2 ++ x4) ++ N)...
               inversion H9...
               inversion H1...
               cutOL Hseq1 H10.
                OLSolve.
               cutOL Hseq1 H11.
                OLSolve.
                cutOL H3 Hseq2.
                OLSolve.
          
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               apply H15...
               
               LLPerm ((M ++ x3) ++ N)...
               LLPerm ((M ++ x4) ++ N)...
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
               apply H7...
               LLPerm(M ++ N ++ x)...
               
               apply ContractionLinear...
                LLPerm ((N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N)).
               refine (BinConnectivePrincipalCase H1 H9 _ _ HL')...
            
              cutOL Hseq1 H10.
               OLSolve.
              cutOL Hseq1 H11.
               OLSolve.
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) ( M++ N).
               apply H15...
               LLPerm ((M ++ x3) ++ N)...
               LLPerm ((M ++ x4) ++ N)... }               
                   
           -- permuteQuantifier.
           -- permuteQuantifier.
         - cutOL H3 Hseq2.
            OLSolve.
            LLtheory (makeRRuleB C F G).
            LLtensor (@nil oo) (M++N).
            apply H7...
            LLPerm (M++N++x)...
  * Cases H. 
     + cutOL H5 Hseq2.
         clearNotFormulas.
         OLSolve.
         rewrite H3 in PosN.
         inversion PosN...
         OLSolve.
         cutOL H4 Hseq2.
         clearNotFormulas.
         OLSolve.
         rewrite H3 in PosN.
         inversion PosN...
         OLSolve.
         
         LLPerm (( (⌈ t_bcon C F G ⌉) :: x ++ x0)++M)...
         apply ContractionLinear...
          LLPerm (( (⌈ t_bcon C F G ⌉) :: (M++x) ++(M++x0)))...
         apply H9...
         rewrite app_assoc_reverse...
         rewrite app_assoc_reverse...
     + inversion H3... 
         inversion H...
         - inversion Hth'... 
           -- wellConstant LTWell Hseq2'.   
               Cases H3.
               rewrite <- app_comm_cons...
               inversion H8...
               Cases H3. 
               cutOL Hseq1 H9.
               do 2 OLSolve.
                rewrite <- app_comm_cons...
               apply H16...
               LLPerm ((x8 ++ x5) ++ N)...
               inversion H9...
               cutOL Hseq1 H12.
               OLSolve.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H16...
               LLPerm ( (M ++ x5) ++ N)...
           -- wellConstant LTWell Hseq2'.   
               Cases H3.
               rewrite <- app_comm_cons...
               inversion H8...
               Cases H3. 
               cutOL Hseq1 H9.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H16...
               LLPerm ((x8 ++ x5) ++ N)...
               inversion H9...
               cutOL Hseq1 H12.
                OLSolve.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H16...
               LLPerm ( (M ++ x5) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- wellBinary LTWell Hseq2'. 
               { Cases H3.
               cutOL Hseq1 H9.
               do 2 OLSolve.
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x8++ N).
               apply H16...
               LLPerm ((x8 ++ x5) ++ N)...
               inversion H9...
               inversion H3...
               cutOL Hseq1 H12.
               OLSolve.
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               apply H16...
               LLPerm ((M ++ x5) ++ N)...
               cutOL H5 Hseq2.
               do 2 OLSolve. 
               cutOL H6 Hseq2.
               do 2 OLSolve. 
               
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
               rewrite H1.
               LLPerm((M++x)++(M++x0)).
               apply H10...
               LLPerm (M ++ x ++ x1)...
               LLPerm (M ++ x0 ++ x2)...
               apply ContractionLinear...
               LLPerm ((N++N)++M).
               apply ContractionLinear...
               LLPerm ((N++N++M)++M).
               apply ContractionLinear...
               LLPerm((M++M++N)++(M++N)).
               refine (BinConnectivePrincipalCase H3 H9 _ _ HL')...
               cutOL Hseq1 H12.
               OLSolve.
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) (M++N).
               apply H16...
               LLPerm ( (M ++ x5) ++ N)... }
               { Cases H3.
               cutOL Hseq1 H13.
               clearNotFormulas.
               OLSolve.
               rewrite H12 in PosM.
         inversion PosM...
         OLSolve.
            cutOL Hseq1 H14.
                    clearNotFormulas.
         OLSolve.
               rewrite H12 in PosM.
         inversion PosM...
         OLSolve.
               LLPerm (( (⌊  t_bcon C0 F1 G0 ⌋) :: x5++ x6) ++ N).
               apply ContractionLinear...
               LLPerm (( (⌊  t_bcon C0 F1 G0 ⌋) :: (N++x5) ++ (N++x6))).
               apply H18...
               LLPerm ((x5 ++ x7) ++ N)...
               LLPerm ((x6 ++ x8) ++ N)...
               inversion H12...
               inversion H3...
                          
               cutOL Hseq1 H14.
               do 2 OLSolve. 
              cutOL Hseq1 H15.
               do 2 OLSolve.
                cutOL H5 Hseq2.
                do 2 OLSolve.
                cutOL H6 Hseq2.
                do 2 OLSolve.
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               rewrite H9...
               LLPerm ((x5++N)++(x6++N)). 
               apply H19...
               LLPerm ((x5 ++ x7) ++ N)...
               LLPerm ((x6 ++ x8) ++ N)...
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
                rewrite H1...
                 LLPerm ((M++x)++(M++x0)). 
               apply H10...
               LLPerm(M ++ x ++ x1)...
               LLPerm(M ++ x0 ++ x2)...
               
               apply ContractionLinear...
               rewrite app_assoc.
                apply ContractionLinear...
               LLPerm ((N++N++N)++M).
               apply ContractionLinear...
               rewrite app_assoc.
               apply ContractionLinear...
               LLPerm((M++M++N)++(M++N++N)).
               refine (BinConnectivePrincipalCase H3 H12 _ _ HL')...
               cutOL Hseq1 H14.
               do 2 OLSolve.
               cutOL Hseq1 H15.
               do 2 OLSolve.
               apply ContractionLinear...
               rewrite H9...
               LLPerm ((x5++N)++(x6++N)).
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) ( (x5 ++ N) ++ x6 ++ N).
               apply H19...
               LLPerm ((x5 ++ x7) ++ N)...
               LLPerm ((x6 ++ x8) ++ N)... }
               { Cases H3.
               cutOL Hseq1 H13.
               do 2 OLSolve.
               cutOL Hseq1 H14.
               do 2 OLSolve.
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x5 ++ N).
               apply H18...
               LLPerm ((x5 ++ x6) ++ N)...
               LLPerm ((x5 ++ x7) ++ N)...
               inversion H12...
               inversion H3...
                          
               cutOL Hseq1 H13.
               do 2 OLSolve. 
               cutOL Hseq1 H14.
               do 2 OLSolve. 
               
               cutOL H5 Hseq2.
               do 2 OLSolve.
               cutOL H6 Hseq2.
               do 2 OLSolve.
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               apply H18...
               LLPerm ((M ++ x6) ++ N)...
               LLPerm ((M ++ x7) ++ N)...
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
                rewrite H1...
                 LLPerm ((M++x)++(M++x0)). 
               apply H10...
               LLPerm(M ++ x ++ x1)...
               LLPerm(M ++ x0 ++ x2)...
               
               apply ContractionLinear...
               LLPerm ((N++N)++M).
               apply ContractionLinear...
               rewrite app_assoc.
               apply ContractionLinear...
               LLPerm((M++M++N)++(M++N)).
               refine (BinConnectivePrincipalCase H3 H12 _ _ HL')...
               cutOL Hseq1 H13.
               do 2 OLSolve.
               cutOL Hseq1 H14.
               do 2 OLSolve.
               
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) ( M++ N).
               apply H18...
               LLPerm ((M ++ x6) ++ N)...
               LLPerm ((M ++ x7) ++ N)... }               
                   
           -- permuteQuantifier.
           -- permuteQuantifier.
         -  cutOL H5 Hseq2.
            do 2 OLSolve.
            cutOL H6 Hseq2.
            do 2 OLSolve.
            rewrite Permutation_app_comm.
            apply ContractionLinear...
            rewrite H1.
            LLPerm ((M ++ x) ++ (M ++ x0))...
            LLtheory (makeRRuleB C F G).
            LLtensor (@nil oo) ((M ++ x) ++ M ++ x0).
            apply H10...
            LLPerm (M ++ x ++ x1)... 
            LLPerm (M ++ x0 ++ x2)... 
  * Cases H. 
     +  cutOL H4 Hseq2.
         do 2 OLSolve.
         cutOL H5 Hseq2.
         do 2 OLSolve.
         LLPerm ( (⌈ t_bcon C F G ⌉) :: M++x)...
          apply H9...
         rewrite app_assoc_reverse...
         rewrite app_assoc_reverse...
     + inversion H3... 
         inversion H...
         - inversion Hth'... 
           -- wellConstant LTWell Hseq2'.   
               Cases H3.
               rewrite <- app_comm_cons...
               inversion H7...
               Cases H3. 
               cutOL Hseq1 H8.
               do 2 OLSolve.
                rewrite <- app_comm_cons...
               apply H15...
               LLPerm ((x6 ++ x) ++ N)...
               inversion H8...
           
                cutOL Hseq1 H11.
               OLSolve.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H15...
               LLPerm ( (M ++ x) ++ N)...
           -- wellConstant LTWell Hseq2'.   
               Cases H3.
               rewrite <- app_comm_cons...
               inversion H7...
               Cases H3. 
               cutOL Hseq1 H8.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H15...
               LLPerm ((x6 ++ x) ++ N)...
               inversion H8...
               cutOL Hseq1 H11.
               OLSolve.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H15...
               LLPerm ( (M ++ x) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- wellBinary LTWell Hseq2'. 
               { Cases H3.
               cutOL Hseq1 H8.
               do 2 OLSolve.
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x6++ N).
               apply H15...
               LLPerm ((x6 ++ x) ++ N)...
               inversion H8...
               inversion H3...

               cutOL Hseq1 H11.
               OLSolve.
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               apply H15...
               LLPerm ((M ++ x) ++ N)...
               cutOL H4 Hseq2.
               do 2 OLSolve. 
               cutOL H5 Hseq2.
               do 2 OLSolve. 
               
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
               apply H9...
               LLPerm (M ++ N ++ x0)...
               LLPerm (M ++ N ++ x1)...
               apply ContractionLinear...
               LLPerm ((N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N)).
               refine (BinConnectivePrincipalCase H3 H8 _ _ HL')...
               cutOL Hseq1 H11.
               OLSolve.
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) (M++N).
               apply H15...
               LLPerm ( (M ++ x) ++ N)... }
               { Cases H3.
               cutOL Hseq1 H12.
                     clearNotFormulas.
           OLSolve.
         rewrite H11 in PosM.
         inversion PosM...
         OLSolve.
               cutOL Hseq1 H13.
                     clearNotFormulas.
           OLSolve.
         rewrite H11 in PosM.
         inversion PosM...
         OLSolve.
               LLPerm (( (⌊  t_bcon C0 F1 G0 ⌋) :: x ++ x4) ++ N).
               apply ContractionLinear...
               LLPerm (( (⌊  t_bcon C0 F1 G0 ⌋) :: (N++x) ++ (N++x4))).
               apply H17...
               LLPerm ((x ++ x5) ++ N)...
               LLPerm ((x4 ++ x6) ++ N)...
               inversion H11...
               inversion H3...
                          
               cutOL Hseq1 H13.
               do 2 OLSolve. 
               cutOL Hseq1 H14.
               do 2 OLSolve. 
                cutOL H4 Hseq2.
               do 2 OLSolve.
                cutOL H5 Hseq2.
               do 2 OLSolve.
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               rewrite H8...
               LLPerm ((x++N)++(x4++N)). 
               apply H18...
               LLPerm ((x ++ x5) ++ N)...
               LLPerm ((x4 ++ x6) ++ N)...
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
               apply H9...
               LLPerm(M ++ N ++ x0)...
               LLPerm(M ++ N ++ x1)...
               
               apply ContractionLinear...
               rewrite app_assoc.
                apply ContractionLinear...
               LLPerm ((N++N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N++N)).
               refine (BinConnectivePrincipalCase H3 H11 _ _ HL')...
               cutOL Hseq1 H13.
               do 2 OLSolve.
               cutOL Hseq1 H14.
               do 2 OLSolve.
               apply ContractionLinear...
               rewrite H8...
               LLPerm ((x++N)++(x4++N)).
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) ( (x ++ N) ++ x4 ++ N).
               apply H18...
               LLPerm ((x ++ x5) ++ N)...
               LLPerm ((x4 ++ x6) ++ N)... }
               { Cases H3.
               cutOL Hseq1 H12.
               do 2 OLSolve.
               cutOL Hseq1 H13.
               do 2 OLSolve.
               
               LLPerm ( (⌊  t_bcon C0 F1 G0 ⌋) :: x ++ N).
               apply H17...
               LLPerm ((x ++ x4) ++ N)...
               LLPerm ((x ++ x5) ++ N)...
               inversion H11...
               inversion H3...
               cutOL Hseq1 H12.
               do 2 OLSolve. 
               cutOL Hseq1 H13.
               do 2 OLSolve. 
                cutOL H4 Hseq2.
               do 2 OLSolve.
               cutOL H5 Hseq2.
               do 2 OLSolve.
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_lftBody (rulesB C0) F1 G0) )).
               apply H17...
               LLPerm ((M ++ x4) ++ N)...
               LLPerm ((M ++ x5) ++ N)...
               
                assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rb_rgtBody (rulesB C0) F1 G0) )).
               apply H9...
               LLPerm(M ++ N ++ x0)...
               LLPerm(M ++ N ++ x1)...
               
               apply ContractionLinear...
               LLPerm ((N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N)).
               refine (BinConnectivePrincipalCase H3 H11 _ _ HL')...
               cutOL Hseq1 H12.
               do 2 OLSolve.
               cutOL Hseq1 H13.
               do 2 OLSolve.
               LLtheory (makeLRuleB C0 F1 G0).
               LLtensor (@nil oo) ( M++ N).
               apply H17...
               LLPerm ((M ++ x4) ++ N)...
               LLPerm ((M ++ x5) ++ N)... }               
                   
           -- permuteQuantifier.
           -- permuteQuantifier.
         - cutOL H4 Hseq2.
            do 2 OLSolve.
            cutOL H5 Hseq2.
            do 2 OLSolve.
            LLtheory (makeRRuleB C F G).
            LLtensor (@nil oo) ((M ++ N)).
            apply H9...
            LLPerm (M ++ N ++ x0)... 
            LLPerm (M ++ N++ x1)...
Qed.                        

Lemma QuantifierRIGHT n n' n0 n1  C FX FCut M N Gamma F0:
  n' <= n ->
  isOLFormula (t_qcon C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  FLLN (OLTheory PN) (S n0) ( (⌈ FCut ⌉) :: Gamma) N (UP []) ->
  FLLN (OLTheory PN) (S n1) ( (⌊ FCut ⌋) :: Gamma) M (UP []) ->
  FLLN (OLTheory PN) n0 ( (⌈ FCut ⌉) :: Gamma) N (DW (makeRRuleQ C FX)) ->
  FLLN (OLTheory PN) n1 ( (⌊ FCut ⌋) :: Gamma) M (DW F0) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeRRuleQ C FX) ->
  buildTheory F0 ->
  uniform FX ->
  FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq1 Hseq2.
  intros Hseq1' Hseq2' OLCut Hth Hth' Hu.
  wellQuantifier LTWell Hseq1'.
  Cases H. 
     + cutOL H1 Hseq2.
         do 2 OLSolve.
         LLPerm ( (⌈ t_qcon C FX ⌉) ::(M++ x2))...
         apply H7...
         rewrite app_assoc_reverse...
     + inversion H1... 
         inversion H...
         - inversion Hth'... 
           -- wellConstant LTWell Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H1. 
               cutOL Hseq1 H6.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ N)...
               inversion H6...
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeRRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               LLPerm ( (M ++ x2) ++ N)...
           -- wellConstant LTWell Hseq2'.   
               Cases H1.
               rewrite <- app_comm_cons...
               inversion H5...
               Cases H1. 
               cutOL Hseq1 H6.
               do 2 OLSolve.
               rewrite <- app_comm_cons...
               apply H13...
               LLPerm ((x5 ++ x2) ++ N)...
               inversion H6...
               cutOL Hseq1 H9.
               OLSolve.
               LLtheory (makeLRuleC C0).
               LLtensor (@nil oo) (M++N).
               apply H13...
               LLPerm ( (M ++ x2) ++ N)...
           -- permuteUnary.
           -- permuteUnary.
           -- permuteBinary.
           -- permuteBinary.
           -- permuteQuantifier.           
           -- wellQuantifier LTWell Hseq2'. 
               Cases H5.
               { cutOL Hseq1 H8.
               do 2 OLSolve.
               LLPerm ( (⌊t_qcon C0 FX0 ⌋) :: x5++ N).
               apply H14...
               LLPerm ((x5 ++ x2) ++ N)... }
               inversion H8...
               { inversion H5...
               cutOL Hseq1 H10.
               OLSolve.
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rq_lftBody (rulesQ C0) FX0) )).
               apply H14...
               LLPerm ((M ++ x2) ++ N)...
               cutOL H3 Hseq2.
               OLSolve.
               
               assert(FLLS (OLTheoryCut PN (pred n)) Gamma (M++N) (DW (rq_rgtBody (rulesQ C0) FX) )).
               apply H7...
               LLPerm (M ++ N ++ x)...
               apply ContractionLinear...
               LLPerm ((N++N)++M).
               apply ContractionLinear...
               LLPerm((M++N)++(M++N)).
               refine (QuantifierPrincipalCase H12 H13 _ _ _ _ _ _ HL')... } 
              cutOL Hseq1 H10.
               OLSolve.
               LLtheory (makeLRuleQ C0 FX0).
               LLtensor (@nil oo) (M++N).
               apply H14...
               LLPerm ((M ++ x2) ++ N)...
         - cutOL H3 Hseq2.
            OLSolve.
            LLtheory (makeRRuleQ C FX).
            LLtensor (@nil oo) (M++N).
            apply H7...
            LLPerm (M++N++x)...
Qed.

                    
Lemma ConstantLEFT n n' n0 n1  C FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_ccon C) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  FLLN (OLTheory PN) (S n1) ( (⌊ FCut ⌋) :: Gamma) M (UP []) ->
  FLLN (OLTheory PN) n0 ( (⌈ FCut ⌉) :: Gamma) N (DW (makeLRuleC C)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleC C) ->
  FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellConstant LTWell Hseq1'.
  * Cases H. 
     + LLPerm ( (⌊ t_ccon C ⌋) :: x++M)...
     + inversion H0...
  * Cases H. 
     + cutOL H1 Hseq2.
         do 2 OLSolve.
         LLPerm ( (⌊ t_ccon C ⌋) ::(M++ x2)).
         apply H7...
         LLPerm(M ++ x2 ++ x)...
    +  inversion H1...
         cutOL H3 Hseq2.
         OLSolve.
         LLtheory (makeLRuleC C).
         LLtensor (@nil oo) (M++N).
         apply H7... 
         LLPerm(M ++ N ++ x)...
Qed.                  
         
 Lemma UnaryLEFT n n' n0 n1 C F FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_ucon C F) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  FLLN (OLTheory PN) (S n1) ( (⌊ FCut ⌋) :: Gamma) M (UP []) ->
  FLLN (OLTheory PN) n0 ( (⌈ FCut ⌉) :: Gamma) N (DW (makeLRuleU C F)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleU C F) ->
  FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellUnary LTWell Hseq1'.
  * Cases H. 
     + cutOL H1 Hseq2.
         do 2 OLSolve.
         LLPerm ( (⌊ t_ucon C F ⌋) ::(M++ x2)).
         apply H7...
         LLPerm(M ++ x2 ++ x)...
     + inversion H1...
         cutOL H3 Hseq2.
         OLSolve.
         LLtheory (makeLRuleU C F).
         LLtensor (@nil oo) (M++N).
         apply H7... 
         LLPerm(M ++ N ++ x)...
Qed.       

 Lemma BinaryLEFT n n' n0 n1 C F G FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_bcon C F G) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  FLLN (OLTheory PN) (S n1) ( (⌊ FCut ⌋) :: Gamma) M (UP []) ->
  FLLN (OLTheory PN) n0 ( (⌈ FCut ⌉) :: Gamma) N (DW (makeLRuleB C F G)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleB C F G) ->
  FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellBinary LTWell Hseq1'.
  * Cases H. 
     + cutOL H1 Hseq2.
         do 2 OLSolve.
         LLPerm ( (⌊t_bcon C F G ⌋) ::(M++ x2)).
         apply H7...
         LLPerm(M ++ x2 ++ x)...
     + inversion H1...
         cutOL H3 Hseq2.
         OLSolve.
         LLtheory (makeLRuleB C F G).
         LLtensor (@nil oo) (M++N).
         apply H7... 
         LLPerm(M ++ N ++ x)...
  * Cases H. 
     + cutOL H4 Hseq2.
               clearNotFormulas.
         OLSolve.
         rewrite H3 in PosN.
         inversion PosN...
         OLSolve.
         cutOL H5 Hseq2.
               clearNotFormulas.
         OLSolve.
         rewrite H3 in PosN.
         inversion PosN...
         OLSolve.
         LLPerm (( (⌊t_bcon C F G ⌋) ::x++x0)++M).
         apply ContractionLinear...
         LLPerm (( (⌊t_bcon C F G ⌋) ::(M++x)++(M++x0))).
         apply H9...
         LLPerm(M ++ x ++ x1)...
         LLPerm(M ++ x0 ++ x2)...
     + inversion H3...
         cutOL H5 Hseq2.
               clearNotFormulas.
         OLSolve.
         rewrite H1 in PosN.
         OLSolve.
         cutOL H6 Hseq2.
               clearNotFormulas.
         OLSolve.
         rewrite H1 in PosN.
         OLSolve.
         LLPerm(N++M).
         apply ContractionLinear...
         LLtheory (makeLRuleB C F G).
         LLtensor (@nil oo) (M++M++N).
         rewrite H1.
         LLPerm ((M++x)++(M++x0)).
         apply H10...
         LLPerm(M ++ x ++ x1)...
         LLPerm(M ++ x0 ++ x2)...
  * Cases H. 
     + cutOL H4 Hseq2.
               clearNotFormulas.
         OLSolve.
         rewrite H3 in PosN.
         OLSolve.
         cutOL H5 Hseq2.
               clearNotFormulas.
         OLSolve.
         rewrite H3 in PosN.
         OLSolve.
         LLPerm (( (⌊t_bcon C F G ⌋) ::(M++x))).
         apply H9...
         LLPerm(M ++ x ++ x0)...
         LLPerm(M ++ x ++ x1)...
     + inversion H3...
       cutOL H4 Hseq2.
               clearNotFormulas.
         OLSolve.
         cutOL H5 Hseq2.
               clearNotFormulas.
         OLSolve.
           LLtheory (makeLRuleB C F G).
         LLtensor (@nil oo) (M++N).
         apply H9...
         LLPerm(M ++ N ++ x0)...
         LLPerm(M ++ N  ++ x1)...         
Qed.         
         
 Lemma QuantifierLEFT n n' n0 n1 C FX FCut M N Gamma:
  n' <= n ->
  isOLFormula (t_qcon C FX) ->
  isOLFormula FCut ->
  lengthUexp FCut n' ->
  posAtomFormulaL M ->
  posAtomFormulaL N ->
  posAtomFormulaL Gamma ->
  FLLN (OLTheory PN) (S n1) ( (⌊ FCut ⌋) :: Gamma) M (UP []) ->
  FLLN (OLTheory PN) n0 ( (⌈ FCut ⌉) :: Gamma) N (DW (makeLRuleQ C FX)) ->
  OOCut n' (S n0 + S n1) ->
  buildTheory (makeLRuleQ C FX) ->
  FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP []).
Proof with sauto.
  intros HL' HisFC HisF HL PosM PosN PosG Hseq2.
  intros Hseq1' OLCut Hth.
  wellQuantifier LTWell Hseq1'.
  * Cases H. 
     + cutOL H1 Hseq2.
         do 2 OLSolve.
         LLPerm ( (⌊ t_qcon C FX ⌋) ::(M++ x2)).
         apply H7...
         LLPerm(M ++ x2 ++ x)...
     + inversion H1...
         cutOL H3 Hseq2.
         OLSolve.
         LLtheory (makeLRuleQ C FX).
         LLtensor (@nil oo) (M++N).
         apply H7... 
         LLPerm(M ++ N ++ x)...
Qed.


   (** Main theorem showing that it is possible to fins a proof with
  the theory [ (OLTheoryCut PN (pred n))] *)
  Theorem OLCutElimStep :
    forall h1 h2 n N M Gamma FCut n',
      isOLFormula FCut ->
      posAtomFormulaL Gamma ->
      posAtomFormulaL N ->
      posAtomFormulaL M ->
      FLLN (OLTheory PN) h1 (atom (up FCut)::Gamma) N (UP []) ->
      FLLN (OLTheory PN) h2 (atom (down FCut)::Gamma) M (UP []) ->
      lengthUexp FCut n' -> n'<=n ->
      (FLLS (OLTheoryCut PN (pred n)) Gamma (M ++ N) (UP [])) .
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
   (* Now we proceed by cases on the last rule applied on both derivations *)
    inversion H1;inversion H4...
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
                           Hseq2 _ _ _ _ H8 _ )...
       - refine(QuantifierLEFT 
                           HL' 
                           H9 
                           HisF _ _ _ _ 
                           Hseq2 
                           H2 _ _)...
    * apply FocusingInitRuleU in H5...
       - apply WeakeningLinear...
          rewrite H7.
          LLtheory (RINIT OO0).
          LLtensor [ (⌈ OO0 ⌉)]  [ (⌊ OO0 ⌋)].
       - inversion H10...
          inversion H5...
          LLtheory (NEG OO0).
          inversion H5. apply OLCutHasNeg...
          LLtensor [ (⌈ OO0 ⌉)] N.
          LLrelease.
          LLstorec.
          apply FLLNtoFLLS in Hseq1...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq1;auto using TheoryEmb1.
          LLExact Hseq1.
          apply WeakeningLinear...
          LLtheory (RINIT OO0).
          LLtensor [ (⌈ OO0 ⌉)] (@nil oo).
       - inversion H10...
          apply WeakeningLinear...
          LLtheory (RINIT OO0).
          LLtensor (@nil oo) [ (⌊ OO0 ⌋)].
       - inversion H9...
          inversion H7...
          inversion H10...
          LLtheory (NEG OO0).
          inversion H7. apply OLCutHasNeg...
          LLtensor (@nil oo) N.
          solveLL.
          apply FLLNtoFLLS in Hseq1...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq1;auto using TheoryEmb1.
          LLExact Hseq1.
          LLPerm ([]++N).
          apply WeakeningLinear...
          LLtheory (RINIT OO0).
          LLtensor (@nil oo) (@nil oo).
    * apply FocusingStruct in H5...
       apply weakeningGenN_rev with (CC':= [ (⌊ OO0 ⌋)]) in Hseq1. 
        rewrite <- app_comm_cons in Hseq1, H11.
        cutOL Hseq1 H11. 
        1-2: OLSolve. 
        LLtheory (POS OO0).
        LLtensor [ (⌊ OO0 ⌋)] (x0++N).
        rewrite H10...
        inversion H10...
        inversion H5...
        rewrite Permutation_app_comm in H11.
        simpl in H11.
        apply contractionN in H11...
        cutOL Hseq1 H11.
        apply weakeningGenN_rev with (CC':= [ (⌊ OO0 ⌋)]) in Hseq1. 
        rewrite <- app_comm_cons in Hseq1, H11.
        cutOL Hseq1 H11. 
        1-2: OLSolve. 
        LLtheory (POS OO0).
        LLtensor (@nil oo) (M++N).
    * apply FocusingStruct in H5...
       apply weakeningGenN_rev with (CC':= [ (⌈ OO0 ⌉)]) in Hseq1. 
        rewrite <- app_comm_cons in Hseq1, H11.
        cutOL Hseq1 H11. 
        1-2: OLSolve. 
        LLtheory (NEG OO0).
        LLtensor [ (⌈ OO0 ⌉)] (x0++N).
        rewrite H10...
        inversion H10...
        apply weakeningGenN_rev with (CC':= [ (⌈ OO0 ⌉)]) in Hseq1. 
        rewrite <- app_comm_cons in Hseq1, H11.
        cutOL Hseq1 H11. 
        1-2: OLSolve. 
        LLtheory (NEG OO0).
        LLtensor (@nil oo) (M++N).
    * apply FocusingInitRuleU in H2...
       - rewrite Permutation_app_comm. 
          apply WeakeningLinear...
          rewrite H7.
          LLtheory (RINIT OO).
          LLtensor [ (⌈ OO ⌉)]  [ (⌊ OO ⌋)].
       - inversion H10...
          rewrite Permutation_app_comm. 
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor [ (⌈ OO ⌉)] (@nil oo).
       - inversion H10...
          inversion H2...
          LLtheory (POS OO).
          inversion H2. apply OLCutHasPos...
          LLtensor  [ (⌊ OO ⌋)] M.
          solveLL.
          apply FLLNtoFLLS in Hseq2...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq2;auto using TheoryEmb1.
          LLExact Hseq2.
          rewrite Permutation_app_comm.
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor  (@nil oo) [ (⌊ OO ⌋)].
       - inversion H9...
          inversion H7...
          inversion H2...
          LLtheory (POS OO).
          inversion H2. apply OLCutHasPos...
          LLtensor (@nil oo) M.
          solveLL.
          apply FLLNtoFLLS in Hseq2...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq2;auto using TheoryEmb1.
          LLExact Hseq2.
          inversion H7...
          LLPerm ([]++M).
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor (@nil oo) (@nil oo).
    * apply FocusingInitRuleU in H2...
       - rewrite Permutation_app_comm. 
          apply WeakeningLinear...
          rewrite H7.
          LLtheory (RINIT OO).
          LLtensor [ (⌈ OO ⌉)]  [ (⌊ OO ⌋)].
       - inversion H10...
          rewrite Permutation_app_comm. 
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor [ (⌈ OO ⌉)] (@nil oo).
       - inversion H10...
          inversion H2...
          LLtheory (POS OO).
          inversion H2. apply OLCutHasPos...
          LLtensor  [ (⌊ OO ⌋)] M.
          solveLL.
          apply FLLNtoFLLS in Hseq2...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq2;auto using TheoryEmb1.
          LLExact Hseq2.
          rewrite Permutation_app_comm.
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor  (@nil oo) [ (⌊ OO ⌋)].
       - inversion H9...
          inversion H7...
          inversion H2...
          LLtheory (POS OO).
          inversion H2. apply OLCutHasPos...
          LLtensor (@nil oo) M.
          solveLL.
          apply FLLNtoFLLS in Hseq2...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq2;auto using TheoryEmb1.
          LLExact Hseq2.
          inversion H7...
          LLPerm ([]++M).
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor (@nil oo) (@nil oo).                
    * apply FocusingInitRuleU in H2...
       - rewrite Permutation_app_comm. 
          apply WeakeningLinear...
          rewrite H7.
          LLtheory (RINIT OO).
          LLtensor [ (⌈ OO ⌉)]  [ (⌊ OO ⌋)].
       - inversion H10...
          rewrite Permutation_app_comm. 
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor [ (⌈ OO ⌉)] (@nil oo).
       - inversion H10...
          inversion H2...
          LLtheory (POS OO).
          inversion H2.
          LLtensor  [ (⌊ OO ⌋)] M.
          solveLL.
          apply FLLNtoFLLS in Hseq2...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq2;auto using TheoryEmb1.
          LLExact Hseq2.
          rewrite Permutation_app_comm.
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor  (@nil oo) [ (⌊ OO ⌋)].
       - inversion H9...
          inversion H7...
          inversion H2...
          LLtheory (POS OO).
          inversion H2.
          LLtensor (@nil oo) M.
          solveLL.
          apply FLLNtoFLLS in Hseq2...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq2;auto using TheoryEmb1.
          LLExact Hseq2.
          inversion H7...
          LLPerm ([]++M).
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor (@nil oo) (@nil oo).
    * apply FocusingInitRuleU in H2...
       - rewrite Permutation_app_comm. 
          apply WeakeningLinear...
          rewrite H7.
          LLtheory (RINIT OO).
          LLtensor [ (⌈ OO ⌉)]  [ (⌊ OO ⌋)].
       - inversion H10...
          rewrite Permutation_app_comm. 
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor [ (⌈ OO ⌉)] (@nil oo).
       - inversion H10...
          inversion H2...
          LLtheory (POS OO).
          inversion H2.
          LLtensor  [ (⌊ OO ⌋)] M.
          solveLL.
          apply FLLNtoFLLS in Hseq2...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq2;auto using TheoryEmb1.
          LLExact Hseq2.
          rewrite Permutation_app_comm.
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor  (@nil oo) [ (⌊ OO ⌋)].
       - inversion H9...
          inversion H7...
          inversion H2...
          LLtheory (POS OO).
          inversion H2.
          LLtensor (@nil oo) M.
          solveLL.
          apply FLLNtoFLLS in Hseq2...
          apply WeakTheory with (theory' := OLTheoryCut PN (pred n)) in Hseq2;auto using TheoryEmb1.
          LLExact Hseq2.
          inversion H7...
          LLPerm ([]++M).
          apply WeakeningLinear...
          LLtheory (RINIT OO).
          LLtensor (@nil oo) (@nil oo).
    * apply FocusingStruct in H2...
       - LLtheory (POS OO).
          LLtensor [ (⌊ OO ⌋)] (M++x0).
          rewrite H10...
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌊ OO ⌋)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        1-2: OLSolve.
       - inversion H10... 
          LLtheory (POS OO).
          LLtensor (@nil oo) (M++N).
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌊ OO ⌋)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        OLSolve.
    * apply FocusingStruct in H2...
       - LLtheory (POS OO).
          LLtensor [ (⌊ OO ⌋)] (M++x0).
          rewrite H10...
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌊ OO ⌋)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        1-2: OLSolve.
       - inversion H10... 
          LLtheory (POS OO).
          LLtensor (@nil oo) (M++N).
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌊ OO ⌋)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        OLSolve.
    * apply FocusingStruct in H2...
       - LLtheory (POS OO).
          LLtensor [ (⌊ OO ⌋)] (M++x0).
          rewrite H10...
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌊ OO ⌋)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        1-2: OLSolve.
       - inversion H10... 
          LLtheory (POS OO).
          LLtensor (@nil oo) (M++N).
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌊ OO ⌋)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        OLSolve.
    * apply FocusingStruct in H2...
       - LLtheory (POS OO).
          LLtensor [ (⌊ OO ⌋)] (M++x0).
          rewrite H10...
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌊ OO ⌋)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        1-2: OLSolve.
       - inversion H10... 
          LLtheory (POS OO).
          LLtensor (@nil oo) (M++N).
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌊ OO ⌋)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        OLSolve.
    * apply FocusingStruct in H2...
       - LLtheory (NEG OO).
          LLtensor [ (⌈ OO ⌉)] (M++x0).
          rewrite H10...
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌈ OO ⌉)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        1-2: OLSolve.
       - inversion H10...
          inversion H2...
          rewrite Permutation_app_comm in H11.
          simpl in H11.
          apply contractionN in H11...
          cutOL H11 Hseq2.
          LLtheory (NEG OO).
          LLtensor (@nil oo) (M++N).
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌈ OO ⌉)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        OLSolve.
    * apply FocusingStruct in H2...
       - LLtheory (NEG OO).
          LLtensor [ (⌈ OO ⌉)] (M++x0).
          rewrite H10...
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌈ OO ⌉)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        1-2: OLSolve.
       - inversion H10...
          inversion H2...
          rewrite Permutation_app_comm in H11.
          simpl in H11.
          apply contractionN in H11...
          cutOL H11 Hseq2.
          LLtheory (NEG OO).
          LLtensor (@nil oo) (M++N).
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌈ OO ⌉)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        OLSolve.        
    * apply FocusingStruct in H2...
       - LLtheory (NEG OO).
          LLtensor [ (⌈ OO ⌉)] (M++x0).
          rewrite H10...
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌈ OO ⌉)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        1-2: OLSolve.
       - inversion H10...
          inversion H2...
          rewrite Permutation_app_comm in H11.
          simpl in H11.
          apply contractionN in H11...
          cutOL H11 Hseq2.
          LLtheory (NEG OO).
          LLtensor (@nil oo) (M++N).
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌈ OO ⌉)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        OLSolve.
    * apply FocusingStruct in H2...
       - LLtheory (NEG OO).
          LLtensor [ (⌈ OO ⌉)] (M++x0).
          rewrite H10...
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌈ OO ⌉)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        1-2: OLSolve.
       - inversion H10...
          inversion H2...
          rewrite Permutation_app_comm in H11.
          simpl in H11.
          apply contractionN in H11...
          cutOL H11 Hseq2.
          LLtheory (NEG OO).
          LLtensor (@nil oo) (M++N).
          solveLL.
          apply weakeningGenN_rev with (CC':= [ (⌈ OO ⌉)]) in Hseq2. 
        rewrite <- app_comm_cons in Hseq2, H11.
        cutOL H11 Hseq2.  
        OLSolve.
 Qed.     
   
  Theorem OLCutElimAux:
      forall n h B N,
      posAtomFormulaL B ->
      posAtomFormulaL N ->
      FLLN  (OLTheoryCut PN n) h  B N (UP[] ) ->
      FLLS  (OLTheoryCut PN 0) B N (UP[] ) .
  Proof with sauto.
    induction n ; induction h using lt_wf_ind; intros *;intros isFB isFN Hh.
    * eapply FLLNtoFLLS;eauto.
    * inversion Hh...
       cut(False);intros...
       refine (onlyAtomsLinear _ H0 H1)...
       cut(False);intros...
       refine (onlyAtomsClassical _ H0 H1)...
       inversion H1...
       inversion H3...
       inversion H4...
      + (* constant *)
         wellConstant LTWell H2.
         Cases H6.
         apply H10...
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         do 2 OLSolve.
         LLtheory (makeRRuleC C).
         LLtensor (@nil oo) N.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
      + (* constant *)
         wellConstant LTWell H2.
         Cases H6.
         apply H10...
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         do 2 OLSolve.
         LLtheory (makeLRuleC C).
         LLtensor (@nil oo) N.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
      + (* unary *)
         wellUnary LTWell H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         do 2 OLSolve.
         LLtheory (makeRRuleU C F0).
         LLtensor (@nil oo) N.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.         
      + (* unary *)
         wellUnary LTWell H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         do 2 OLSolve.
         LLtheory (makeLRuleU C F0).
         LLtensor (@nil oo) N.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.         
      + (* binary *)
         wellBinary LTWell H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         do 2 OLSolve.
         LLtheory (makeRRuleB C F0 G).
         LLtensor (@nil oo) N.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         clearNotFormulas.
        OLSolve.
         rewrite H10 in isFN.
         inversion isFN...
         OLSolve.
         refine (H _ _ _ _ _ _ H12)...
         clearNotFormulas.
         OLSolve.
         rewrite H10 in isFN.
         inversion isFN...
         OLSolve.
         LLtheory (makeRRuleB C F0 G).
         LLtensor (@nil oo) N.
         rewrite H8.
         apply H17...
         refine (H _ _ _ _ _ _ H12)...
         do 2 OLSolve.
         refine (H _ _ _ _ _ _ H13)...
         do 2 OLSolve.
         Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         do 2 OLSolve.
         refine (H _ _ _ _ _ _ H12)...
         do 2 OLSolve.
         LLtheory (makeRRuleB C F0 G).
         LLtensor (@nil oo) N.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         OLSolve.
         refine (H _ _ _ _ _ _ H12)...
         OLSolve.                  
      + (* binary *)
         wellBinary LTWell H2.
         Cases H6.
         apply H14...
         refine (H _ _ _ _ _ _ H8)...
         do 2 OLSolve.
         LLtheory (makeLRuleB C F0 G).
         LLtensor (@nil oo) N.
         apply H14...
         refine (H _ _ _ _ _ _ H10)...
         OLSolve.
         Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         clearNotFormulas.
        OLSolve.
         rewrite H10 in isFN.
         inversion isFN...
         OLSolve.
         refine (H _ _ _ _ _ _ H12)...
         clearNotFormulas.
         OLSolve.
         rewrite H10 in isFN.
         inversion isFN...
         OLSolve.
         LLtheory (makeLRuleB C F0 G).
         LLtensor (@nil oo) N.
         rewrite H8.
         apply H17...
         refine (H _ _ _ _ _ _ H12)...
         do 2 OLSolve.
         refine (H _ _ _ _ _ _ H13)...
         do 2 OLSolve.
         Cases H6.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         do 2 OLSolve.
         refine (H _ _ _ _ _ _ H12)...
         do 2 OLSolve.
         LLtheory (makeLRuleB C F0 G).
         LLtensor (@nil oo) N.
         apply H16...
         refine (H _ _ _ _ _ _ H11)...
         OLSolve.
         refine (H _ _ _ _ _ _ H12)...
         OLSolve.                  
      + (* quantifier *)
         wellQuantifier LTWell H2.
         Cases H7.
         apply H15...
         refine (H _ _ _ _ _ _ H9)...
         do 2 OLSolve.
         LLtheory (makeRRuleQ C FX).
         LLtensor (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
         OLSolve.         
      + (* quantifier *)
         wellQuantifier LTWell H2.
         Cases H7.
         apply H15...
         refine (H _ _ _ _ _ _ H9)...
         do 2 OLSolve.
         LLtheory (makeLRuleQ C FX).
         LLtensor (@nil oo) N.
         apply H15...
         refine (H _ _ _ _ _ _ H11)...
         OLSolve.         
      + (* init *)
         apply FocusingInitRuleU in H2...
         rewrite H5.
         LLtheory (RINIT OO).
         LLtensor [ (⌈ OO ⌉)] [ (⌊ OO ⌋)].
         LLtheory (RINIT OO).
         LLtensor [ (⌈ OO ⌉)] (@nil oo).
         LLtheory (RINIT OO).
         LLtensor (@nil oo) [ (⌊ OO ⌋)].
         LLtheory (RINIT OO).
         LLtensor.
      + (* pos *)
         apply FocusingStruct in H2...
         LLtheory (POS OO).
         LLtensor [ (⌊ OO ⌋)] x0.
         solveLL.
         refine (H _ _ _ _ _ _ H8)...
         OLSolve. OLSolve.
         LLtheory (POS OO).
         LLtensor (@nil oo) N.
         solveLL.
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.
      + (* neg *)
         apply FocusingStruct in H2...
         LLtheory (NEG OO).
         LLtensor [ (⌈ OO ⌉)] x0.
         solveLL.
         refine (H _ _ _ _ _ _ H8)...
         OLSolve. OLSolve.
         LLtheory (NEG OO).
         LLtensor (@nil oo) N.
         solveLL.
         refine (H _ _ _ _ _ _ H8)...
         OLSolve.         
      + (* cut *)
         inversion H3...
         2:{ elim f. simpl...  }
         apply FocusingTensor in H2...
         apply H in H8...
         apply H in H11...
         apply WeakTheory with (theory' := OLTheory PN) in H8;auto;try apply OOTheryCut0.
         apply WeakTheory with (theory' := OLTheory PN) in H11;auto;try apply OOTheryCut0.
         rewrite H9.
         apply WeakTheory with (theory := OLTheory PN).
         apply OOTheryCut0.
  
         destruct m. 
         generalize(LengthFormula H4 H5);intro;lia.
         assert (FLLS (OLTheoryCut PN (pred  (S (n)))) B (x0 ++ x1) (UP [])) .
         rewrite Permutation_app_comm.
         apply FLLStoFLLN in H8...
         apply FLLStoFLLN in H11...
         apply absorptionLN in H11, H8.
         refine(OLCutElimStep _ _ _ _ H8 H11 H5 _)...  
         all: OLSolve.
         apply FLLStoFLLN in H2...
         apply IHn in H2...
         apply WeakTheory with (theory' := OLTheory PN) in H2;auto;try apply  OOTheryCut0.
         all:OLSolve.
 Qed.        
        
     
  (** Cut-elimination theorem for Object Logics satisfying cut-coherence *)
  Theorem OLCutElimination :
    forall n  B N ,
      posAtomFormulaL B ->
      posAtomFormulaL N ->
      FLLS (OLTheoryCut PN n) B N (UP [] ) ->
      FLLS (OLTheory PN) B N (UP [] ) .
  Proof with sauto.
    intros.
    apply FLLStoFLLN in H1...
    apply OLCutElimAux in H1 ...
    eapply WeakTheory with (theory':= OLTheory PN) in H1 ...
    apply OOTheryCut0.
  Qed.     
  
End CutElimination.

 #[export] Hint Resolve OLHasPos OLHasNeg : core. 
#[export] Hint Resolve OLCutHasPos OLCutHasNeg : core. 