Require Import LL.SL.Focused.FLLTactics.

Set Implicit Arguments.

(* Create HintDb LLBase.
 *)
Section FLLReasoning.
  Context `{OLS: OLSig}.

 Variable th : oo -> Prop.

Theorem TensorCommN: forall n F G B M,
    (seqN th n B M (DW (F ⊗ G))) -> (seqN th n B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      FLLsplit N M0... 
      rewrite H2...
 Qed.


Theorem TensorComm: forall F G B M,
    (seq th B M (DW (F ⊗ G))) -> (seq th B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      FLLsplit N M0... 
      rewrite H2...
 Qed.
 
Theorem OplusCommN: forall n F G B M,
    (seqN th n B M (DW (F ⊕ G))) -> (seqN th n B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Theorem OplusComm: forall F G B M,
    (seq th B M (DW (F ⊕ G))) -> (seq th B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.
 
Theorem WithCommN: forall n F G B M L,
    seqN th n B M (UP (F & G::L)) -> seqN th n B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Theorem WithComm: forall F G B M L,
    seq th B M (UP (F & G::L)) -> seq th B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.
   Theorem FocusingClause : forall n B D A F,
     seqN th n B D (DW ((perp A) ⊗ F)) ->
 (exists m N, n = S m /\ Permutation D ((atom A)::N) /\
                seqN th m B N  (DW F)) \/
   (exists m, n = S m /\ In (atom A) B /\
                seqN th m B D  (DW F)).
  Proof with sauto.
  intros.
  InvTriAll.
  - left.
    eexists. exists N...
  - right.
    eexists. 
    split...  HProof.
 Qed.

  Lemma FocusingInitRuleU : forall h D A A' B,
      seqN th h B D (DW ((perp A) ⊗ (perp A') ))  -> 
      Permutation D ([atom A] ++ [atom A']) \/ 
      (D = [atom A] /\ In (atom A') B) \/ 
      (D = [atom A'] /\ In (atom A) B) \/
      (In (atom A) B /\ In (atom A') B /\ D = []).
  Proof with sauto.
    intros.
    InvTriAll.
    right. right.
    right...
    Qed.
    
   Theorem FocusingStruct : forall n D B A,
   seqN th n B D (DW ((perp A) ⊗ (? (atom A)))) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((atom A)::N) /\
                seqN th m (B++[atom A]) N  (UP [] )) \/
    (exists m, n = S (S (S m))  /\ In (atom A) B /\

                seqN th m (B++[(atom A)]) D  (UP [] )).            
   Proof with sauto.
   intros.
   InvTriAll.
   left.
  exists n0. exists N...
  right.
  exists n0... 
  HProof.
 Qed.

  Theorem FocusingPar :
    forall n A B D G,
    seqN th n G D (DW ((atom A) ⅋ ( atom B))) ->
      exists m , n =  S (S(S(S m)))  /\
                 seqN th m G (atom B::atom A::D) (UP []).
  Proof with sauto.
    intros.
    InvTriAll.  
    eexists n.
    split;eauto.
  Qed.
  
  Theorem FocusingPlus:
    forall n A B D G ,
    seqN th n G D (DW ( (atom A) ⊕ (atom B))) ->
     ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (atom A ::D) (UP []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 seqN th m G (atom B::D) (UP []) ).
  Proof with sauto.
    intros.
    InvTriAll.
    left.
    eexists n0.
    split;eauto.
    right.
    eexists n0.
    split;eauto.
  Qed.
  
  Theorem FocusingWith :
    forall n A B D G,
      seqN th n G D (DW ( (atom A) & (atom B))) ->
      exists m , n = S(S(S m))  /\
                 ( (seqN th m G (atom A::D) (UP []) ) /\
                   (seqN th m G (atom B::D) (UP []) )) .
  Proof with sauto.
    intros.
    InvTriAll.
    eexists n0.
    split;eauto.
  Qed.
  
  Theorem FocusingTensor :
    forall n A B D G,
      seqN th n G D (DW ( (atom A) ⊗ (atom B))) ->
       exists m M N , n = S(S(S m))  /\ Permutation D (M++N) /\ 
                  ( seqN th m G (atom A::M) (UP [])) /\
                  ( seqN th m G (atom B::N) (UP [])).
   Proof with sauto.
    intros.
    InvTriAll.
    eexists n0.
    eexists M.
    eexists N.
    split;eauto.
   Qed. 
   
   Theorem FocusingClauseL : forall B D A F,
     seq th B D (DW F) -> seq th B  (atom A::D) (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   FLLsplit [atom A] D.
   Qed.  

 Theorem FocusingClauseL' : forall B D D' A F,
   Permutation D (atom A::D') -> seq th B D' (DW F) -> seq th B  D (DW ((perp A) ⊗ F)).
   Proof with auto using FocusingClauseL.
   intros.
   rewrite H...
  Qed. 

     
   Theorem FocusingClauseC : forall B D A F,
   In (atom A) B ->  seq th B D (DW F) -> seq th B  D (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   rewrite <- (app_nil_l D).
   FLLsplit (nil (A:=oo)) D.
   Qed.  

End FLLReasoning.
