Require Import LL.Framework.SL.SELLF.Tactics.

Set Implicit Arguments.

(* Create HintDb LLBase.
 *)
Section FLLReasoning.
  Context `{OLS: OLSig}.
  Context `{SI : SigSELL}.

 Variable th : oo -> Prop.

Tactic Notation "LLfocus1" := match goal with
    | [ |- SELLS _ _ (?P::?PL) _ ] =>  eapply @tri_dec1' with (F:= P) (L':=PL);[solvePolarity | sauto | sauto ]
    | [|- SELLN _ _ _ (?P::?PL) _] => eapply @tri_dec1 with (F:= P) (L':=PL);[solvePolarity | sauto | sauto ]
end.

Tactic Notation "LLstore" := match goal with
  | [ |- SELLS _ _ _ _ ] =>  apply tri_store';[solvePolarity | auto]
  | [|- SELLN _ _ _ _ _] => apply tri_store;[solvePolarity | auto]
  end.


 Lemma unRelease B M P: 
 SELLS th B M (DW P) -> SELLS th B M (UP [P]).
 Proof with sauto;solveLL.
  intros.
  inversion H...
 all: try LLfocus1.
 LLstore. LLfocus1. 
Qed.
 
 Lemma select B M L P: posLFormula P ->
 SELLS th B M (UP (P::L)) -> SELLS th B (P::M) (UP L).
 Proof with sauto;solvePolarity;solveLL.
  intros.
  inversion H0...
 inversion H.
Qed.

(* 
Lemma TensorCommN: forall n F G B M,
    (SELLN th n B M (DW (F ⊗ G))) -> (SELLN th n B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      LLtensor N M0... 
      rewrite H2...
 Qed.

Lemma TensorComm: forall F G B M,
    (SELLS th B M (DW (F ⊗ G))) -> (SELLS th B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      LLtensor N M0... 
      rewrite H2...
 Qed.
 
Lemma OplusCommN: forall n F G B M,
    (SELLN th n B M (DW (F ⊕ G))) -> (SELLN th n B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Lemma OplusComm: forall F G B M,
    (SELLS th B M (DW (F ⊕ G))) -> (SELLS th B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.
 
Lemma WithCommN: forall n F G B M L,
    SELLN th n B M (UP (F & G::L)) -> SELLN th n B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Lemma WithComm: forall F G B M L,
    SELLS th B M (UP (F & G::L)) -> SELLS th B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.


Lemma BangDistWith: forall F G B M,
    SELLS th B M (DW (! (F & G))) <-> SELLS th B M (DW (! F ⊗ ! G)).
 Proof with sauto;solvePolarity;solveLL.
    split;intros.
   *  inversion H...
       inversion H3...
       LLtensor.
   *  inversion H...
       inversion H5...
       inversion H6...
 Qed.

  Example Tensor3 B L F: SELLS th B L (DW (F ⊗ Zero)) <-> SELLS th B L (DW Zero).
  Proof with sauto;solvePolarity.
    split;intros;
    inversion H...
    solveLL.
  Qed.

   
Theorem weakeningGenN (CC LC : list oo) CC' X n:
   SELLN th n CC LC X -> SELLN th n (CC'++ CC) LC X.
Proof.
      intro H.
      induction CC';simpl;auto.
      apply weakeningN;auto.
Qed.

Theorem weakeningGenN_rev (CC LC : list oo) CC' X n:
   SELLN th n CC LC X -> SELLN th n (CC++ CC') LC X.
Proof.      
      intros.
      eapply exchangeCCN with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGenN;auto.
Qed.



Theorem weakening_swap (C LC : list oo) F G X:
   SELLS th (F::C) LC X -> SELLS th (F :: G:: C) LC X.
Proof with sauto;solveLL. 
     intros.
      eapply exchangeCC.
     rewrite perm_swap;eauto.
     apply weakening;auto.
 Qed.     

 
 Theorem weakening_middle (C1 C2 LC : list oo) F X:
   SELLS th (C1++ C2) LC X -> SELLS th (C1++F :: C2) LC X.
Proof. 
      intros.
     eapply exchangeCC.
     rewrite <- Permutation_middle;eauto.
     apply weakening;auto.
Qed.

 Theorem weakening_last (C LC : list oo) F X:
   SELLS th C LC X -> SELLS th (C++[F]) LC X.
Proof. 
      intros.
     eapply exchangeCC.
     rewrite <- Permutation_cons_append;eauto.
     apply weakening;auto.
Qed.
   
Theorem weakeningGen (CC LC : list oo) CC' X:
   SELLS th CC LC X -> SELLS th (CC' ++ CC) LC X.
Proof.     
     intro H.
      induction CC';simpl;auto.
      apply weakening;auto.
Qed.

Theorem weakeningGen_rev (CC LC : list oo) CC' X:
   SELLS th CC LC X -> SELLS th (CC++CC') LC X.
Proof.
      intros.
      eapply exchangeCC with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGen;auto.
Qed.

Theorem weakeningHead (C1 C2 C1' C2' LC : list oo) X:
   SELLS th (C2++C2') LC X -> SELLS th ((C1++C2) ++ (C1'++C2')) LC X.
Proof.     
     intro H.
     eapply exchangeCC with 
     (CC:=(C2++C2') ++ (C1++C1')). perm.
     apply weakeningGen_rev;auto.
Qed.


Theorem weakeningTail (C1 C2 C1' C2' LC : list oo) X:
   SELLS th (C1++C1') LC X -> SELLS th ((C1++C2) ++ (C1'++C2')) LC X.
Proof.     
     intro H.
     eapply exchangeCC with 
     (CC:=(C2++C2') ++ (C1++C1')). perm.
     apply weakeningGen;auto.
Qed.

Lemma contraction : forall CC LC  F X ,
  SELLS th  (F :: F::CC) LC X -> SELLS th (F::CC) LC X.
Proof with sauto.
intros.
  apply contract with (F:=F)...
Qed.


Lemma contraction_middle : forall C1 C2 LC  F X ,
  SELLS th  (C1++F::F::C2) LC X -> SELLS th (C1++F::C2) LC X.
Proof with sauto.
intros.
  apply contract with (F:=F)...
  apply exchangeCC with (CC:= C1 ++ F :: F :: C2)...
Qed.

Lemma AbsorptionCSet : forall n C Gamma Delta X,
  SELLN th n (C++Gamma) (Delta++ C)  X ->
      SELLN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  apply absorptionN. 
  LLPerm (C ++ Gamma ++ [a]). 
  eapply IHC.
  LLExact H...
  Qed. 
  
    Lemma AbsorptionCSet' : forall  C Gamma Delta X,
  SELLS  th (C++Gamma) (Delta++ C)  X ->
      SELLS  th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H...
  apply AbsorptionCSet in H...
  apply seqNtoSeq in H...
  Qed. 
  
 Lemma AbsorptionCSet_rev : forall C Gamma Delta X,
  SELLS  th (Gamma++C) (Delta++C)  X ->
      SELLS  th (Gamma++C) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H...
  LLPermH H1 (C++Gamma).
  eapply AbsorptionCSet in H...
  apply seqNtoSeq in H...
  LLPermH H1 (Gamma++C).
  auto.
  Qed.
  
 Lemma AbsorptionLSet : forall n C Gamma Delta X,
  SELLN th n (Gamma) (Delta++ C)  X ->
      SELLN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  rewrite app_comm_cons.
  apply absorptionLN.
  apply IHC.
  
  LLExact H...
  Qed. 
 
  Lemma AbsorptionLSet' : forall C Gamma Delta X,
  SELLS th (Gamma) (Delta++C)  X ->
      SELLS th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H...
  apply AbsorptionLSet in H...
  apply seqNtoSeq in H...
  Qed. 
    

(** Some inveribility lemmas *)

Theorem FocusAtom: forall n Gamma Delta A,
 (SELLN th n Gamma Delta (DW ((perp A ) ))) ->
    Delta = [ (atom A)] \/ (Delta = [] /\ In (atom A ) Gamma) . 
 Proof with sauto.
      intros.
      inversion H ...
      inversion H1.
 Qed.

   Theorem FocusingClause : forall n B D A F,
     SELLN th n B D (DW ((perp A) ⊗ F)) ->
 (exists m N, n = S m /\ Permutation D ((atom A)::N) /\
                SELLN th m B N  (DW F)) \/
   (exists m, n = S m /\ In (atom A) B /\
                SELLN th m B D  (DW F)).
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
      SELLN th h B D (DW ((perp A) ⊗ (perp A') ))  -> 
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
    
   Theorem FocusingStruct : forall n D B A F,
   SELLN th n B D (DW ((perp A) ⊗ (? F))) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((atom A)::N) /\
                SELLN th m (B++[F]) N  (UP [] )) \/
    (exists m, n = S (S (S m))  /\ In (atom A) B /\

                SELLN th m (B++[F]) D  (UP [] )).            
   Proof with sauto.
   intros.
   InvTriAll.
   left.
  exists n0. exists N... 
  HProof. right.
  exists n0... 
  HProof.
 Qed.

  Theorem FocusingPar :
    forall n A B D G,
    SELLN th n G D (DW ((atom A) ⅋ ( atom B))) ->
      exists m , n =  S (S(S(S m)))  /\
                 SELLN th m G (atom B::atom A::D) (UP []).
  Proof with sauto.
    intros.
    InvTriAll.  
    eexists n.
    split;eauto.
  Qed.

  Theorem FocusingParPos :
    forall n A B D G, posLFormula A -> posLFormula B ->
    SELLN th n G D (DW (A ⅋ B)) ->
      exists m , n =  S (S(S(S m)))  /\
                 SELLN th m G (B::A::D) (UP []).
  Proof with sauto.
    intros.
    InvTriAll.
    inversion H5;solvePolarity. 
    inversion H8;solvePolarity. 
    eexists n.
    split;eauto.
  Qed.
  
  Theorem FocusingPlus:
    forall n A B D G ,
    SELLN th n G D (DW ( (atom A) ⊕ (atom B))) ->
     ( exists m , n = (S(S (S m)))  /\
                 (SELLN th m G (atom A ::D) (UP []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 SELLN th m G (atom B::D) (UP []) ).
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

  Theorem FocusingPlusPos:
    forall n A B D G ,
    SELLN th n G D (DW ( Bang (atom A) ⊕ Bang (atom B))) ->
     ( exists m , n = (S(S (S m)))  /\ D = [] /\
                 (SELLN th m G [atom A] (UP []) )) \/
    ( exists m , n = (S(S (S m)))  /\  D = [] /\
                 SELLN th m G [atom B] (UP []) ).
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
      SELLN th n G D (DW ( (atom A) & (atom B))) ->
      exists m , n = S(S(S m))  /\
                 ( (SELLN th m G (atom A::D) (UP []) ) /\
                   (SELLN th m G (atom B::D) (UP []) )) .
  Proof with sauto.
    intros.
    InvTriAll.
    eexists n0.
    split;eauto.
  Qed.


  Theorem FocusingWithPos :
    forall n A B D G, posLFormula A -> posLFormula B ->
      SELLN th n G D (DW ( A & B)) ->
      exists m , n = S(S(S m))  /\
                 ( (SELLN th m G (A::D) (UP []) ) /\
                   (SELLN th m G (B::D) (UP []) )) .
  Proof with sauto.
    intros.
    InvTriAll.
    inversion H6;solvePolarity. 
    inversion H9;solvePolarity. 
    eexists n0.
    split;eauto.
  Qed.
  
  
  Theorem FocusingTensor :
    forall n A B D G,
      SELLN th n G D (DW ( (atom A) ⊗ (atom B))) ->
       exists m M N , n = S(S(S m))  /\ Permutation D (M++N) /\ 
                  ( SELLN th m G (atom A::M) (UP [])) /\
                  ( SELLN th m G (atom B::N) (UP [])).
   Proof with sauto.
    intros.
    InvTriAll.
    eexists n0.
    eexists M.
    eexists N.
    split;eauto.
   Qed. 

  Theorem FocusingTensorPos :
    forall n A B D G,
      SELLN th n G D (DW ( Bang (atom A) ⊗ (atom B))) ->
       exists m , n = S(S(S m))  /\
                  ( SELLN th m G [atom A] (UP [])) /\
                  ( SELLN th m G (atom B::D) (UP [])).
   Proof with sauto.
    intros.
    InvTriAll.
    eexists n0.
    split;eauto.
split;eauto. rewrite H2...
   Qed. 
   
   Theorem FocusingClauseL : forall B D A F,
     SELLS th B D (DW F) -> SELLS th B  (atom A::D) (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   LLtensor [atom A] D.
   Qed.  

 Theorem FocusingClauseL' : forall B D D' A F,
   Permutation D (atom A::D') -> SELLS th B D' (DW F) -> SELLS th B  D (DW ((perp A) ⊗ F)).
   Proof with auto using FocusingClauseL.
   intros.
   rewrite H...
  Qed. 

     
   Theorem FocusingClauseC : forall B D A F,
   In (atom A) B ->  SELLS th B D (DW F) -> SELLS th B  D (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   rewrite <- (app_nil_l D).
   LLtensor (nil (A:=oo)) D.
   Qed.  
*)

End FLLReasoning.
