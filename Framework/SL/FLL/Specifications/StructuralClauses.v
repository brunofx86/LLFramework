
Require Export LL.Framework.SL.FLL.Specifications.OL2FLLResults.
Require Import LL.Framework.SL.FLL.Reasoning.
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

(** ⊗ Rules of the encoded proof system *)
Section OLPOSNEG.
Context `{OLS : OLSyntax}.

 (** Allowing contraction and weakening on the left side of the sequent *)
  Definition POS F := (perp (down F)) ⊗ (? (atom (down F))).
  (** Allowing contraction and weakening on the right side of the sequent *)
  Definition NEG F := (perp (up F)) ⊗ (? atom (up F)).


Definition hasPos th:= (forall OO: uexp, isOLFormula OO -> th (POS OO)).
Definition hasNeg th:= (forall OO: uexp, isOLFormula OO -> th (NEG OO)).


Lemma PosF : forall (th : oo -> Prop) F D M , 
isOLFormula F -> hasPos th ->
FLLS th (D++[(atom (down F))] ) (M) (UP []) -> 
FLLS th D ((atom (down F)) :: M) (UP []).
Proof with sauto.
  intros. 
  LLtheory (POS F ). 
  inversion H1...
  LLtensor [(atom (down F))] M.
Qed.    

Lemma PosFN : forall n (th : oo -> Prop) F D M , 
isOLFormula F -> hasPos th ->
FLLN th n ((atom (down F))::D ) (M) (UP []) -> 
FLLN th (S (S (S (S n)))) D ((atom (down F)) :: M) (UP []).
Proof with sauto.
  intros. 
  LLtheory (POS F ). 
  inversion H1...
  LLtensor [(atom (down F))] M.
Qed.    


Lemma NegF : forall (th : oo -> Prop) F D M, 
isOLFormula F -> hasNeg th ->
FLLS th (D ++ [(atom (up F))]) M (UP []) -> 
FLLS th D ((atom (up F)) :: M) (UP []).
Proof with sauto.
  intros. 
  LLtheory (NEG F ).
  inversion H1.
  LLtensor [(atom (up F))] M.
Qed. 

Lemma NegFN : forall n (th : oo -> Prop) F D M , 
isOLFormula F -> hasNeg th ->
FLLN th n ((atom (up F))::D ) (M) (UP []) -> 
FLLN th (S (S (S (S n)))) D ((atom (up F)) :: M) (UP []).
Proof with sauto.
  intros. 
  LLtheory (NEG F ). 
  inversion H1...
  LLtensor [(atom (up F))] M.
Qed.    


Lemma PosSetP L : forall (th : oo -> Prop) D M, 
isOLFormulaL L -> hasPos th ->
FLLS th (LEncode L++D ) M (UP []) -> 
FLLS th D (M++LEncode L) (UP []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  LLtheory (POS a)...
  inversion H1.
  LLtensor [(atom (down a))] (M ++ LEncode L)...
  solveLL.
  eapply IHL... 
  LLExact H0.
Qed.    

Lemma NegSetP L : forall (th : oo -> Prop) D M, 
isOLFormulaL L -> hasNeg th ->
FLLS th ((REncode L)++D ) M (UP []) -> 
FLLS th D (M++REncode L) (UP []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  LLtheory (NEG a)...
  inversion H1.
  LLtensor [(atom (up a))] (M ++ REncode L)...
  solveLL.
  eapply IHL...
  LLExact H0.
Qed.
 
Theorem PosNegSetT : forall (th:oo->Prop) D L1 L2,  
isOLFormulaL L1 -> isOLFormulaL L2 ->
hasNeg th ->
hasPos th ->
FLLS th (D ++  (LEncode L1) ++ (REncode L2)) [] (UP []) ->
FLLS th D (LEncode L1++REncode L2) (UP []).
Proof with sauto.
  intros.
  apply NegSetP...
  rewrite <- (app_nil_l (LEncode L1)).
  apply PosSetP...
  LLExact H1. 
Qed.  
 
Lemma PosNegSetT' : forall (th:oo->Prop) D L1 L2,  
hasNeg th -> hasPos th ->
posAtomFormulaL L1 -> posAtomFormulaL L2 ->
FLLS th (L1++L2 ++D) [] (UP []) ->
FLLS th D (L1++L2) (UP []).
Proof with sauto.
  intros.
  assert(posAtomFormulaL L1) by auto.
  assert(posAtomFormulaL L2) by auto.
  apply posDestruct' in H2.
  apply posDestruct' in H3...
  assert(isOLFormulaL x1).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x2).
  apply PositiveAtomREOLFormula.
  OLSolve.
  assert(isOLFormulaL x0).
  apply PositiveAtomREOLFormula.
  OLSolve. 
 
  rewrite H2.
   
  LLPerm((L2++LEncode x1) ++ REncode x2).
  apply NegSetP...
  apply PosSetP...
  
  rewrite H3.
  apply NegSetP...
  rewrite <- (app_nil_l (LEncode x)).
  apply PosSetP...
  eapply exchangeCC.
  2:{ exact H1. }
  rewrite H2.
  rewrite H3.
  rewrite !app_assoc. perm.
Qed.  

Lemma ContractionLinear: forall (th:oo->Prop) D M N,  
hasPos th -> hasNeg th -> 
posAtomFormulaL N -> 
FLLS th D (M++N++N) (UP []) ->
FLLS th D (M++N) (UP []).
Proof with sauto.
  intros.
  assert(posAtomFormulaL N) by auto.
  apply posDestruct' in H1...
  assert(isOLFormulaL x).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x0).
  apply PositiveAtomREOLFormula.
  OLSolve.
  
  rewrite H1.
  rewrite app_assoc.
  apply NegSetP...
  apply PosSetP...
  rewrite app_assoc.
  
  apply AbsorptionCSet'.
  apply AbsorptionLSet'.
  rewrite <- H1...
  rewrite app_assoc_reverse...
  Qed.

Lemma ContractionLinearPos: forall (th:oo->Prop) D M N,  
hasPos th -> isOLFormulaL N ->
FLLS th D (M++LEncode N++LEncode N) (UP []) ->
FLLS th D (M++LEncode N) (UP []).
Proof with sauto.
  intros.
  apply PosSetP...

  apply AbsorptionCSet'.
  apply AbsorptionLSet'.
  rewrite app_assoc_reverse...
  Qed.

Lemma WeakeningLinear: forall (th:oo->Prop) D M N,  
hasPos th -> hasNeg th -> 
posAtomFormulaL N -> 
FLLS th D M (UP []) ->
FLLS th D (M++N) (UP []).
Proof with sauto.
  intros.
  assert(posAtomFormulaL N) by auto.
  apply posDestruct' in H1...
  assert(isOLFormulaL x).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x0).
  apply PositiveAtomREOLFormula.
  OLSolve.
  
  rewrite H1.
  rewrite app_assoc.
  apply NegSetP...
  apply PosSetP...
  rewrite app_assoc.
  apply weakeningGen...
Qed.

Lemma WeakeningLinearPos: forall (th:oo->Prop) D M N,  
hasPos th -> 
isOLFormulaL N -> 
FLLS th D M (UP []) ->
FLLS th D (M++LEncode N) (UP []).
Proof with sauto.
  intros.
  apply PosSetP...
  apply weakeningGen...
Qed.
  
Lemma LinearToClassic: forall (th:oo->Prop) D L,  
hasPos th -> hasNeg th -> 
posAtomFormulaL L -> 
FLLS th (L++D) [] (UP []) ->
FLLS th D (L) (UP []).
Proof with sauto.
  intros.
  assert(posAtomFormulaL L) by auto.
  apply posDestruct' in H1...
  assert(isOLFormulaL x).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x0).
  apply PositiveAtomREOLFormula.
  OLSolve.
 
  rewrite H1.
  apply PosNegSetT'...
  OLSolve.
  OLSolve.
  eapply exchangeCC.
  2:{ exact H0. }
  rewrite H1.
  perm.
Qed.

End OLPOSNEG.

Tactic Notation "PosNeg" := 
  match goal with
     | [ |- FLLS _ _  ((atom (up _)) :: _) _ ] =>  eapply NegF;auto
     | [ |- FLLS _ _  ((atom (down _)) :: _) _ ] =>  eapply PosF;auto
end.

Tactic Notation "PosNegAll"  := 
  match goal with
     | [ |- FLLS _ _ _ _ ] =>  eapply LinearToClassic;auto
end.

Tactic Notation "PosNegAllE" := 
  match goal with
     | [ |- FLLS _ _ _ _ ] =>  eapply PosNegSetT ;auto
end.
