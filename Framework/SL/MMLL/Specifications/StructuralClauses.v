
Require Export LL.Framework.SL.MMLL.Specifications.OL2MLLResults.
Require Import LL.Framework.SL.MMLL.Reasoning.
Require Import LL.Framework.SL.MMLL.InvPositivePhase.

Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

(** ⊗ Rules of the encoded proof system *)
Section OLPOSNEG.
Context `{OLS : OLSyntax}.
Context `{SI : SigMMLL}.

 (** Allowing contraction and weakening on the left side of the sequent *)
  Definition POS a F := (perp (down F)) ⊗ (Quest a (atom (down F))).
  (** Allowing contraction and weakening on the right side of the sequent *)
  Definition NEG a F := (perp (up F)) ⊗ (Quest a (atom (up F))).


Definition hasPos th a:= (forall OO: uexp, isOLFormula OO -> th (POS a OO)).
Definition hasNeg th a:= (forall OO: uexp, isOLFormula OO -> th (NEG a OO)).


Lemma PosF (SIU: UNoDSigMMLL): forall (th : oo -> Prop) a F D M , 
isOLFormula F -> hasPos th a ->
MLLS th ((a,atom (down F))::D) (M) (UP []) -> 
MLLS th D ((atom (down F)) :: M) (UP []).
Proof with sauto.
  intros. 
  LLtheory (POS a F ). 
  inversion H1...
  LLtensor [(atom (down F))] M.
Qed.    

Lemma PosFN (SIU: UNoDSigMMLL): forall n (th : oo -> Prop) a F D M , 
isOLFormula F -> hasPos th a ->
MLLN th n ((a,atom (down F))::D ) (M) (UP []) -> 
MLLN th (S (S (S (S n)))) D ((atom (down F)) :: M) (UP []).
Proof with sauto.
  intros. 
  LLtheory (POS a F ). 
  inversion H1...
  LLtensor [(atom (down F))] M.
Qed.    


Lemma NegF (SIU: UNoDSigMMLL): forall (th : oo -> Prop) a F D M, 
isOLFormula F -> hasNeg th a ->
MLLS th ((a,atom (up F))::D) M (UP []) -> 
MLLS th D ((atom (up F)) :: M) (UP []).
Proof with sauto.
  intros. 
  LLtheory (NEG a F ).
  inversion H1.
  LLtensor [(atom (up F))] M.
Qed. 

Lemma NegFN (SIU: UNoDSigMMLL): forall n (th : oo -> Prop) a F D M , 
isOLFormula F -> hasNeg th a ->
MLLN th n ((a,atom (up F))::D ) (M) (UP []) -> 
MLLN th (S (S (S (S n)))) D ((atom (up F)) :: M) (UP []).
Proof with sauto.
  intros. 
  LLtheory (NEG a F ). 
  inversion H1...
  LLtensor [(atom (up F))] M.
Qed.    


Lemma PosSetP L (SIU: UNoDSigMMLL): forall (th : oo -> Prop) a D M, 
isOLFormulaL L -> hasPos th a ->
MLLS th (CEncode a (LEncode L) ++D ) M (UP []) -> 
MLLS th D (M++LEncode L) (UP []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  LLtheory (POS a0 a)...
  inversion H1.
  LLtensor [(atom (down a))] (M ++ LEncode L)...
  solveLL.
  eapply IHL with (a:=a0)... 
  LLExact H0.
Qed.    

Lemma NegSetP L (SIU: UNoDSigMMLL): forall (th : oo -> Prop) a D M, 
isOLFormulaL L -> hasNeg th a ->
MLLS th (CEncode a (REncode L)++D ) M (UP []) -> 
MLLS th D (M++REncode L) (UP []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H...
  simpl in *...
  
  LLtheory (NEG a0 a)...
  inversion H1.
  LLtensor [(atom (up a))] (M ++ REncode L)...
  solveLL.
  eapply IHL with (a:=a0)...
  LLExact H0.
Qed.
 
Theorem PosNegSetT (SIU: UNoDSigMMLL): forall (th:oo->Prop) a b D L1 L2,  
isOLFormulaL L1 -> isOLFormulaL L2 ->
hasPos th a ->
hasNeg th b ->
MLLS th (D ++  CEncode a (LEncode L1) ++ CEncode b (REncode L2)) [] (UP []) ->
MLLS th D (LEncode L1++REncode L2) (UP []).
Proof with sauto.
  intros.
  apply NegSetP with (a:=b)...
  rewrite <- (app_nil_l (LEncode L1)).
  apply PosSetP with (a:=a)...
  LLExact H1. 
Qed.  
 
(* Lemma PosNegSetT' (SIU: UNoDSigMMLL): forall (th:oo->Prop) a b D L1 L2,  
hasPos th a ->
hasNeg th b ->
IsPositiveAtomFormulaL L1 -> IsPositiveAtomFormulaL L2 ->
MLLS th (CEncode a L1++CEncode a L2 ++D) [] (UP []) ->
MLLS th D (L1++L2) (UP []).
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
  apply NegSetP with (a:=b)...
  apply PosSetP with (a:=a)...
  
  rewrite H3.
  apply NegSetP with (a:=b)...
  rewrite <- (app_nil_l (LEncode x)).
  apply PosSetP with (a:=a)...
  eapply exchangeCC.
  2:{ exact H1. }
  eapply Permutation_map with (f:= (fun x : oo => (a, x))) in H2, H3.
  rewrite H2, H3.
  rewrite CEncodeApp.
  rewrite !app_assoc. perm.
Qed.  
*)


Lemma ContractionLinear (SIU: UNoDSigMMLL): forall (th:oo->Prop) a b D M N,  
mt a  = true -> mt b =  true -> hasPos th a -> hasNeg th b -> 
IsPositiveAtomFormulaL N -> 
MLLS th D (M++N++N) (UP []) ->
MLLS th D (M++N) (UP []).
Proof with sauto.
  intros *. intros mtA mtB.
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
  apply NegSetP with (a:=b)...
  apply PosSetP with (a:=a)...
  rewrite app_assoc.
  
  apply AbsorptionCSet'...
  apply Forall_app...
  1-2:apply setTCEncode...
  apply AbsorptionLSet'...
  apply Forall_app...
  1-2:apply setTCEncode...
   rewrite !secondApp.
   rewrite !secCEncode.
   rewrite <- H1...
  rewrite app_assoc_reverse...
  Qed.

(*
Lemma ContractionLinearPos: forall (th:oo->Prop) D M N,  
hasPos th -> isOLFormulaL N ->
MLLS th D (M++LEncode N++LEncode N) (UP []) ->
MLLS th D (M++LEncode N) (UP []).
Proof with sauto.
  intros.
  apply PosSetP...

  apply AbsorptionCSet'.
  apply AbsorptionLSet'.
  rewrite app_assoc_reverse...
  Qed.
*)

Lemma WeakeningLinear (SIU: UNoDSigMMLL): forall (th:oo->Prop) a b D M N,  
hasPos th a -> hasNeg th b -> 
IsPositiveAtomFormulaL N -> 
MLLS th D M (UP []) ->
MLLS th D (M++N) (UP []).
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
  apply NegSetP with (a:=b)...
  apply PosSetP with (a:=a)...
  rewrite app_assoc.
  apply weakeningGen...
Qed.


(* Lemma WeakeningLinearPos: forall (th:oo->Prop) D M N,  
hasPos th -> 
isOLFormulaL N -> 
MLLS th D M (UP []) ->
MLLS th D (M++LEncode N) (UP []).
Proof with sauto.
  intros.
  apply PosSetP...
  apply weakeningGen...
Qed.

Lemma LinearToClassic: forall (th:oo->Prop) D L,  
hasPos th -> hasNeg th -> 
IsPositiveAtomFormulaL L -> 
MLLS th (L++D) [] (UP []) ->
MLLS th D (L) (UP []).
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
  *)

End OLPOSNEG.

Tactic Notation "PosNeg" := 
  match goal with
     | [ |- MLLS _ _  ((atom (up _)) :: _) _ ] =>  eapply NegF;auto
     | [ |- MLLS _ _  ((atom (down _)) :: _) _ ] =>  eapply PosF;auto
end.

(*
Tactic Notation "PosNegAll"  := 
  match goal with
     | [ |- MLLS _ _ _ _ ] =>  eapply LinearToClassic;auto
end.
*)

Tactic Notation "PosNegAllE" := 
  match goal with
     | [ |- MLLS _ _ _ _ ] =>  eapply PosNegSetT ;auto
end.
