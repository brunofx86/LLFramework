Require Import LL.Framework.SL.FLL.Tactics.

Set Implicit Arguments.

(* Create HintDb LLBase.
 *)
Section FLLReasoning.
  Context `{OLS: OLSig}.

 Variable th : oo -> Prop.

 Lemma unRelease B M P: 
 FLLS th B M (DW P) -> FLLS th B M (UP [P]).
 Proof with sauto;solveLL.
  intros.
  inversion H...
  all:LLfocus1.
Qed.
 
 Lemma select B M L P: posLFormula P ->
 FLLS th B M (UP (P::L)) -> FLLS th B (P::M) (UP L).
 Proof with sauto;solvePolarity;solveLL.
  intros.
  inversion H0...
Qed.

Lemma TensorCommN: forall n F G B M,
    (FLLN th n B M (DW (F ⊗ G))) -> (FLLN th n B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      LLtensor N M0... 
      rewrite H2...
 Qed.

Lemma TensorComm: forall F G B M,
    (FLLS th B M (DW (F ⊗ G))) -> (FLLS th B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      LLtensor N M0... 
      rewrite H2...
 Qed.
 
Lemma OplusCommN: forall n F G B M,
    (FLLN th n B M (DW (F ⊕ G))) -> (FLLN th n B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Lemma OplusComm: forall F G B M,
    (FLLS th B M (DW (F ⊕ G))) -> (FLLS th B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.
 
Lemma WithCommN: forall n F G B M L,
    FLLN th n B M (UP (F & G::L)) -> FLLN th n B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Lemma WithComm: forall F G B M L,
    FLLS th B M (UP (F & G::L)) -> FLLS th B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.


Lemma BangDistWith: forall F G B M,
    FLLS th B M (DW (! (F & G))) <-> FLLS th B M (DW (! F ⊗ ! G)).
 Proof with sauto;solvePolarity;solveLL.
    split;intros.
   *  inversion H...
       inversion H3...
       LLtensor.
   *  inversion H...
       inversion H5...
       inversion H6...
 Qed.

  Example Tensor3 B L F: FLLS th B L (DW (F ⊗ Zero)) <-> FLLS th B L (DW Zero).
  Proof with sauto;solvePolarity.
    split;intros;
    inversion H...
    solveLL.
  Qed.

   
Theorem weakeningGenN (CC LC : list oo) CC' X n:
   FLLN th n CC LC X -> FLLN th n (CC'++ CC) LC X.
Proof.
      intro H.
      induction CC';simpl;auto.
      apply weakeningN;auto.
Qed.

Theorem weakeningGenN_rev (CC LC : list oo) CC' X n:
   FLLN th n CC LC X -> FLLN th n (CC++ CC') LC X.
Proof.      
      intros.
      eapply exchangeCCN with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGenN;auto.
Qed.

Theorem weakening_swap (C LC : list oo) F G X:
   FLLS th (F::C) LC X -> FLLS th (F :: G:: C) LC X.
Proof with sauto;solveLL. 
     intros.
      eapply exchangeCC.
     rewrite perm_swap;eauto.
     apply weakening;auto.
 Qed.     

 
 Theorem weakening_middle (C1 C2 LC : list oo) F X:
   FLLS th (C1++ C2) LC X -> FLLS th (C1++F :: C2) LC X.
Proof. 
      intros.
     eapply exchangeCC.
     rewrite <- Permutation_middle;eauto.
     apply weakening;auto.
Qed.

 Theorem weakening_last (C LC : list oo) F X:
   FLLS th C LC X -> FLLS th (C++[F]) LC X.
Proof. 
      intros.
     eapply exchangeCC.
     rewrite <- Permutation_cons_append;eauto.
     apply weakening;auto.
Qed.
   
Theorem weakeningGen (CC LC : list oo) CC' X:
   FLLS th CC LC X -> FLLS th (CC' ++ CC) LC X.
Proof.     
     intro H.
      induction CC';simpl;auto.
      apply weakening;auto.
Qed.

Theorem weakeningGen_rev (CC LC : list oo) CC' X:
   FLLS th CC LC X -> FLLS th (CC++CC') LC X.
Proof.
      intros.
      eapply exchangeCC with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGen;auto.
Qed.

Theorem weakeningHead (C1 C2 C1' C2' LC : list oo) X:
   FLLS th (C2++C2') LC X -> FLLS th ((C1++C2) ++ (C1'++C2')) LC X.
Proof.     
     intro H.
     eapply exchangeCC with 
     (CC:=(C2++C2') ++ (C1++C1')). perm.
     apply weakeningGen_rev;auto.
Qed.


Theorem weakeningTail (C1 C2 C1' C2' LC : list oo) X:
   FLLS th (C1++C1') LC X -> FLLS th ((C1++C2) ++ (C1'++C2')) LC X.
Proof.     
     intro H.
     eapply exchangeCC with 
     (CC:=(C2++C2') ++ (C1++C1')). perm.
     apply weakeningGen;auto.
Qed.

Lemma contrac : forall CC LC  F X ,
  FLLS th  (F :: F::CC) LC X -> FLLS th (F::CC) LC X.
Proof with sauto.
intros.
  apply contraction with (F:=F)...
Qed.


Lemma contraction_middle : forall C1 C2 LC  F X ,
  FLLS th  (C1++F::F::C2) LC X -> FLLS th (C1++F::C2) LC X.
Proof with sauto.
intros.
  apply contraction with (F:=F)...
  apply exchangeCC with (CC:= C1 ++ F :: F :: C2)...
Qed.

Lemma AbsorptionCSet : forall n C Gamma Delta X,
  FLLN th n (C++Gamma) (Delta++ C)  X ->
      FLLN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  apply absorptionN. 
  LLPerm (C ++ Gamma ++ [a]). 
  eapply IHC.
  LLExact H...
  Qed. 
  
    Lemma AbsorptionCSet' : forall  C Gamma Delta X,
  FLLS  th (C++Gamma) (Delta++ C)  X ->
      FLLS  th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply FLLStoFLLN in H...
  apply AbsorptionCSet in H...
  apply FLLNtoFLLS in H...
  Qed. 
  
 Lemma AbsorptionCSet_rev : forall C Gamma Delta X,
  FLLS  th (Gamma++C) (Delta++C)  X ->
      FLLS  th (Gamma++C) Delta  X.
  Proof with sauto.
  intros.
  apply FLLStoFLLN in H...
  LLPermH H1 (C++Gamma).
  eapply AbsorptionCSet in H...
  apply FLLNtoFLLS in H...
  LLPermH H1 (Gamma++C).
  auto.
  Qed.
  
 Lemma AbsorptionLSet : forall n C Gamma Delta X,
  FLLN th n (Gamma) (Delta++ C)  X ->
      FLLN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  rewrite app_comm_cons.
  apply absorptionLN.
  apply IHC.
  
  LLExact H...
  Qed. 
 
  Lemma AbsorptionLSet' : forall C Gamma Delta X,
  FLLS th (Gamma) (Delta++C)  X ->
      FLLS th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply FLLStoFLLN in H...
  apply AbsorptionLSet in H...
  apply FLLNtoFLLS in H...
  Qed. 
    

(** Some inveribility lemmas *)

Theorem FocusAtom: forall n Gamma Delta A,
 (FLLN th n Gamma Delta (DW ((perp A ) ))) ->
    Delta = [ (atom A)] \/ (Delta = [] /\ In (atom A ) Gamma) . 
 Proof with sauto.
      intros.
      inversion H ...
      inversion H1.
 Qed.

   Theorem FocusingClause : forall n B D A F,
     FLLN th n B D (DW ((perp A) ⊗ F)) ->
 (exists m N, n = S m /\ Permutation D ((atom A)::N) /\
                FLLN th m B N  (DW F)) \/
   (exists m, n = S m /\ In (atom A) B /\
                FLLN th m B D  (DW F)).
  Proof with sauto.
  intros.
  InvTriAll;[left | right].
  - eexists n0, N... 
  - eexists n0... 
    HProof.
 Qed.

 
  Lemma FocusingInitRuleU : forall h D A A' B,
      FLLN th h B D (DW ((perp A) ⊗ (perp A') ))  -> 
      Permutation D ([atom A] ++ [atom A']) \/ 
      (D = [atom A] /\ In (atom A') B) \/ 
      (D = [atom A'] /\ In (atom A) B) \/
      (In (atom A) B /\ In (atom A') B /\ D = []).
  Proof with sauto.
    intros.
    InvTriAll.
    repeat right...
    Qed.
    
   Theorem FocusingStruct : forall n D B A F,
   FLLN th n B D (DW ((perp A) ⊗ (? F))) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((atom A)::N) /\
                FLLN th m (B++[F]) N  (UP [] )) \/
    (exists m, n = S (S (S m))  /\ In (atom A) B /\

                FLLN th m (B++[F]) D  (UP [] )).            
   Proof with sauto.
   intros.
   InvTriAll; [left | right].
   -  exists n0, N...
       HProof. 
  - exists n0... 
      HProof.
 Qed.

  Theorem FocusingPar :
    forall n A B D G,
    FLLN th n G D (DW ((atom A) ⅋ ( atom B))) ->
      exists m , n =  S (S(S(S m)))  /\
                 FLLN th m G (atom B::atom A::D) (UP []).
  Proof with sauto.
    intros.
    InvTriAll.  
    eexists n...
  Qed.

  Theorem FocusingParPos :
    forall n A B D G, posLFormula A -> posLFormula B ->
    FLLN th n G D (DW (A ⅋ B)) ->
      exists m , n =  S (S(S(S m)))  /\
                 FLLN th m G (B::A::D) (UP []).
  Proof with sauto.
    intros.
    InvTriAll.
    inversion H5;solvePolarity. 
    inversion H8;solvePolarity. 
    eexists n...
  Qed.
  
  Theorem FocusingPlus:
    forall n A B D G ,
    FLLN th n G D (DW ( (atom A) ⊕ (atom B))) ->
     ( exists m , n = (S(S (S m)))  /\
                 (FLLN th m G (atom A ::D) (UP []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 FLLN th m G (atom B::D) (UP []) ).
  Proof with sauto.
    intros.
    InvTriAll;[left | right].
    - eexists n0...
    - eexists n0...
  Qed.

  Theorem FocusingPlusPos:
    forall n A B D G ,
    FLLN th n G D (DW ( Bang (atom A) ⊕ Bang (atom B))) ->
     ( exists m , n = (S(S (S m)))  /\ D = [] /\
                 (FLLN th m G [atom A] (UP []) )) \/
    ( exists m , n = (S(S (S m)))  /\  D = [] /\
                 FLLN th m G [atom B] (UP []) ).
  Proof with sauto.
    intros.
    InvTriAll;[left | right].
    - eexists n0...
    - eexists n0...
  Qed.

  Theorem FocusingWith :
    forall n A B D G,
      FLLN th n G D (DW ( (atom A) & (atom B))) ->
      exists m , n = S(S(S m))  /\
                 ( (FLLN th m G (atom A::D) (UP []) ) /\
                   (FLLN th m G (atom B::D) (UP []) )) .
  Proof with sauto.
    intros.
    InvTriAll.
    eexists n0...
  Qed.


  Theorem FocusingWithPos :
    forall n A B D G, posLFormula A -> posLFormula B ->
      FLLN th n G D (DW ( A & B)) ->
      exists m , n = S(S(S m))  /\
                 ( (FLLN th m G (A::D) (UP []) ) /\
                   (FLLN th m G (B::D) (UP []) )) .
  Proof with sauto.
    intros.
    InvTriAll.
    inversion H6;solvePolarity. 
    inversion H9;solvePolarity. 
    eexists n0...
  Qed.
  
  
  Theorem FocusingTensor :
    forall n A B D G,
      FLLN th n G D (DW ( (atom A) ⊗ (atom B))) ->
       exists m M N , n = S(S(S m))  /\ Permutation D (M++N) /\ 
                  ( FLLN th m G (atom A::M) (UP [])) /\
                  ( FLLN th m G (atom B::N) (UP [])).
   Proof with sauto.
    intros.
    InvTriAll.
    eexists n0, M, N...
   Qed. 

  Theorem FocusingTensorPos :
    forall n A B D G,
      FLLN th n G D (DW ( Bang (atom A) ⊗ (atom B))) ->
       exists m , n = S(S(S m))  /\
                  ( FLLN th m G [atom A] (UP [])) /\
                  ( FLLN th m G (atom B::D) (UP [])).
   Proof with sauto.
    intros.
    InvTriAll.
    eexists n0...
    rewrite H2...
   Qed. 
   
   Theorem FocusingClauseL : forall B D A F,
     FLLS th B D (DW F) -> FLLS th B  (atom A::D) (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   LLtensor [atom A] D.
   Qed.  

 Theorem FocusingClauseL' : forall B D D' A F,
   Permutation D (atom A::D') -> FLLS th B D' (DW F) -> FLLS th B  D (DW ((perp A) ⊗ F)).
   Proof with auto using FocusingClauseL.
   intros.
   rewrite H...
  Qed. 

     
   Theorem FocusingClauseC : forall B D A F,
   In (atom A) B ->  FLLS th B D (DW F) -> FLLS th B  D (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   rewrite <- (app_nil_l D).
   LLtensor (nil (A:=oo)) D.
   Qed.  


End FLLReasoning.
