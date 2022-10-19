Require Import LL.SL.FLL.Tactics.

Set Implicit Arguments.

(* Create HintDb LLBase.
 *)
Section FLLReasoning.
  Context `{OLS: OLSig}.

 Variable th : oo -> Prop.

 Lemma unRelease B M P: 
 seq th B M (DW P) -> seq th B M (UP [P]).
 Proof with sauto;solveLL.
  intros.
  inversion H...
  all:LFocus.
Qed.
 
 Lemma select B M L P: positiveLFormula P ->
 seq th B M (UP (P::L)) -> seq th B (P::M) (UP L).
 Proof with sauto;solvePolarity;solveLL.
  intros.
  inversion H0...
Qed.

Lemma TensorCommN: forall n F G B M,
    (seqN th n B M (DW (F ⊗ G))) -> (seqN th n B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      FLLsplit N M0... 
      rewrite H2...
 Qed.

Lemma TensorComm: forall F G B M,
    (seq th B M (DW (F ⊗ G))) -> (seq th B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      FLLsplit N M0... 
      rewrite H2...
 Qed.
 
Lemma OplusCommN: forall n F G B M,
    (seqN th n B M (DW (F ⊕ G))) -> (seqN th n B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Lemma OplusComm: forall F G B M,
    (seq th B M (DW (F ⊕ G))) -> (seq th B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.
 
Lemma WithCommN: forall n F G B M L,
    seqN th n B M (UP (F & G::L)) -> seqN th n B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Lemma WithComm: forall F G B M L,
    seq th B M (UP (F & G::L)) -> seq th B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.


Lemma BangDistWith: forall F G B M,
    seq th B M (DW (! (F & G))) <-> seq th B M (DW (! F ⊗ ! G)).
 Proof with sauto;solvePolarity;solveLL.
    split;intros.
   *  inversion H...
       inversion H3...
       FLLsplit.
   *  inversion H...
       inversion H5...
       inversion H6...
 Qed.

  Example Tensor3 B L F: seq th B L (DW (F ⊗ Zero)) <-> seq th B L (DW Zero).
  Proof with sauto;solvePolarity.
    split;intros;
    inversion H...
    solveLL.
  Qed.

   
Theorem weakeningGenN (CC LC : list oo) CC' X n:
   seqN th n CC LC X -> seqN th n (CC'++ CC) LC X.
Proof.
      intro H.
      induction CC';simpl;auto.
      apply weakeningN;auto.
Qed.

Theorem weakeningGenN_rev (CC LC : list oo) CC' X n:
   seqN th n CC LC X -> seqN th n (CC++ CC') LC X.
Proof.      
      intros.
      eapply exchangeCCN with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGenN;auto.
Qed.



Theorem weakening_swap (C LC : list oo) F G X:
   seq th (F::C) LC X -> seq th (F :: G:: C) LC X.
Proof with sauto;solveLL. 
     intros.
      eapply exchangeCC.
     rewrite perm_swap;eauto.
     apply weakening;auto.
 Qed.     

 
 Theorem weakening_middle (C1 C2 LC : list oo) F X:
   seq th (C1++ C2) LC X -> seq th (C1++F :: C2) LC X.
Proof. 
      intros.
     eapply exchangeCC.
     rewrite <- Permutation_middle;eauto.
     apply weakening;auto.
Qed.

 Theorem weakening_last (C LC : list oo) F X:
   seq th C LC X -> seq th (C++[F]) LC X.
Proof. 
      intros.
     eapply exchangeCC.
     rewrite <- Permutation_cons_append;eauto.
     apply weakening;auto.
Qed.
   
Theorem weakeningGen (CC LC : list oo) CC' X:
   seq th CC LC X -> seq th (CC' ++ CC) LC X.
Proof.     
     intro H.
      induction CC';simpl;auto.
      apply weakening;auto.
Qed.

Theorem weakeningGen_rev (CC LC : list oo) CC' X:
   seq th CC LC X -> seq th (CC++CC') LC X.
Proof.
      intros.
      eapply exchangeCC with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGen;auto.
Qed.

Theorem weakeningHead (C1 C2 C1' C2' LC : list oo) X:
   seq th (C2++C2') LC X -> seq th ((C1++C2) ++ (C1'++C2')) LC X.
Proof.     
     intro H.
     eapply exchangeCC with 
     (CC:=(C2++C2') ++ (C1++C1')). perm.
     apply weakeningGen_rev;auto.
Qed.


Theorem weakeningTail (C1 C2 C1' C2' LC : list oo) X:
   seq th (C1++C1') LC X -> seq th ((C1++C2) ++ (C1'++C2')) LC X.
Proof.     
     intro H.
     eapply exchangeCC with 
     (CC:=(C2++C2') ++ (C1++C1')). perm.
     apply weakeningGen;auto.
Qed.

Lemma contraction : forall CC LC  F X ,
  seq th  (F :: F::CC) LC X -> seq th (F::CC) LC X.
Proof with sauto.
intros.
  apply contract with (F:=F)...
Qed.


Lemma contraction_middle : forall C1 C2 LC  F X ,
  seq th  (C1++F::F::C2) LC X -> seq th (C1++F::C2) LC X.
Proof with sauto.
intros.
  apply contract with (F:=F)...
  apply exchangeCC with (CC:= C1 ++ F :: F :: C2)...
Qed.

Lemma AbsorptionCSet : forall n C Gamma Delta X,
  seqN th n (C++Gamma) (Delta++ C)  X ->
      seqN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  apply absorptionN. 
  LLPerm (C ++ Gamma ++ [a]).
  eapply IHC.
  LLExact H...
  Qed. 
  
    Lemma AbsorptionCSet' : forall  C Gamma Delta X,
  seq  th (C++Gamma) (Delta++ C)  X ->
      seq  th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H...
  apply AbsorptionCSet in H...
  apply seqNtoSeq in H...
  Qed. 
  
 Lemma AbsorptionCSet_rev : forall C Gamma Delta X,
  seq  th (Gamma++C) (Delta++C)  X ->
      seq  th (Gamma++C) Delta  X.
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
  seqN th n (Gamma) (Delta++ C)  X ->
      seqN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  rewrite app_comm_cons.
  apply absorptionLN.
  apply IHC.
  
  LLExact H...
  Qed. 
 
  Lemma AbsorptionLSet' : forall C Gamma Delta X,
  seq th (Gamma) (Delta++C)  X ->
      seq th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H...
  apply AbsorptionLSet in H...
  apply seqNtoSeq in H...
  Qed. 
    

(** Some inveribility lemmas *)

Theorem FocusAtom: forall n Gamma Delta A,
 (seqN th n Gamma Delta (DW ((perp A ) ))) ->
    Delta = [ (atom A)] \/ (Delta = [] /\ In (atom A ) Gamma) . 
 Proof with sauto.
      intros.
      inversion H ...
      inversion H1.
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
    
   Theorem FocusingStruct : forall n D B A F,
   seqN th n B D (DW ((perp A) ⊗ (? F))) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((atom A)::N) /\
                seqN th m (B++[F]) N  (UP [] )) \/
    (exists m, n = S (S (S m))  /\ In (atom A) B /\

                seqN th m (B++[F]) D  (UP [] )).            
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
