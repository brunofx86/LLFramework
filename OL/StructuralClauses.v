
Require Export LL.OL.SyntaxResults.
Require Import LL.SL.FLL.Reasoning.
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
seq th (D++[(atom (down F))] ) (M) (UP []) -> 
seq th D ((atom (down F)) :: M) (UP []).
Proof with sauto.
  intros. 
  TFocus (POS F ). 
  inversion H1...
  FLLsplit [(atom (down F))] M.
Qed.    

Lemma NegF : forall (th : oo -> Prop) F D M, 
isOLFormula F -> hasNeg th ->
seq th (D ++ [(atom (up F))]) M (UP []) -> 
seq th D ((atom (up F)) :: M) (UP []).
Proof with sauto.
  intros. 
  TFocus (NEG F ).
  inversion H1.
  FLLsplit [(atom (up F))] M.
Qed. 

Lemma PosSetP L : forall (th : oo -> Prop) D M, 
isOLFormulaL L -> hasPos th ->
seq th (LEncode L++D ) M (UP []) -> 
seq th D (M++LEncode L) (UP []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  TFocus (POS a)...
  inversion H1.
  FLLsplit [(atom (down a))] (M ++ LEncode L)...
  solveLL.
  eapply IHL... 
  LLExact H0.
Qed.    

Lemma NegSetP L : forall (th : oo -> Prop) D M, 
isOLFormulaL L -> hasNeg th ->
seq th ((REncode L)++D ) M (UP []) -> 
seq th D (M++REncode L) (UP []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  TFocus (NEG a)...
  inversion H1.
  FLLsplit [(atom (up a))] (M ++ REncode L)...
  solveLL.
  eapply IHL...
  LLExact H0.
Qed.
 
Theorem PosNegSetT : forall (th:oo->Prop) D L1 L2,  
isOLFormulaL L1 -> isOLFormulaL L2 ->
hasNeg th ->
hasPos th ->
seq th (D ++  (LEncode L1) ++ (REncode L2)) [] (UP []) ->
seq th D (LEncode L1++REncode L2) (UP []).
Proof with sauto.
  intros.
  apply NegSetP...
  rewrite <- (app_nil_l (LEncode L1)).
  apply PosSetP...
  LLExact H1. 
Qed.  
 
Lemma PosNegSetT' : forall (th:oo->Prop) D L1 L2,  
hasNeg th -> hasPos th ->
IsPositiveAtomFormulaL L1 -> IsPositiveAtomFormulaL L2 ->
seq th (L1++L2 ++D) [] (UP []) ->
seq th D (L1++L2) (UP []).
Proof with sauto.
  intros.
  assert(IsPositiveAtomFormulaL L1) by auto.
  assert(IsPositiveAtomFormulaL L2) by auto.
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
IsPositiveAtomFormulaL N -> 
seq th D (M++N++N) (UP []) ->
seq th D (M++N) (UP []).
Proof with sauto.
  intros.
  assert(IsPositiveAtomFormulaL N) by auto.
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

Lemma WeakeningLinear: forall (th:oo->Prop) D M N,  
hasPos th -> hasNeg th -> 
IsPositiveAtomFormulaL N -> 
seq th D M (UP []) ->
seq th D (M++N) (UP []).
Proof with sauto.
  intros.
  assert(IsPositiveAtomFormulaL N) by auto.
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
  
Lemma LinearToClassic: forall (th:oo->Prop) D L,  
hasPos th -> hasNeg th -> 
IsPositiveAtomFormulaL L -> 
seq th (L++D) [] (UP []) ->
seq th D (L) (UP []).
Proof with sauto.
  intros.
  assert(IsPositiveAtomFormulaL L) by auto.
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
     | [ |- seq _ _  ((atom (up _)) :: _) _ ] =>  eapply NegF;auto
     | [ |- seq _ _  ((atom (down _)) :: _) _ ] =>  eapply PosF;auto
end.

Tactic Notation "PosNegAll"  := 
  match goal with
     | [ |- seq _ _ _ _ ] =>  eapply LinearToClassic;auto
end.

Tactic Notation "PosNegAllE" := 
  match goal with
     | [ |- seq _ _ _ _ ] =>  eapply PosNegSetT ;auto
end.
