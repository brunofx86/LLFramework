Require Import LL.Framework.SL.MMLL.Tactics.
Require Import LL.Framework.SL.MMLL.InvPositivePhase.

Set Implicit Arguments.

(* Create HintDb LLBase.
 *)
Section FLLReasoning.
  Context `{OLS: OLSig}.
 Context `{SI: SigMMLL}.

 Variable th : oo -> Prop.

Lemma unRelease B M P: 
 MLLS th B M (DW P) -> MLLS th B M (UP [P]).
 Proof with sauto;solveLL.
  intros.
  inversion H...
 all: try LLfocus1.
 LLstore. LLfocus1.
 LLstore. LLfocus1.
Qed.
 
 Lemma select B M L P: posLFormula P ->
 MLLS th B M (UP (P::L)) -> MLLS th B (P::M) (UP L).
 Proof with sauto;solvePolarity;solveLL.
  intros.
  inversion H0...
Qed.

 Lemma unbInit i B A: SetU B ->
mt i = true -> In (i, atom A) B ->
MLLS th B [] (DW (perp A)).
 Proof with sauto;try solveLL.
  intros.
  apply InPermutation in H1... 
  rewrite H1 in H. 
  inversion H... 
Qed.

 Lemma InvUpPhase (SIU: UNoDSigMMLL) n B M X:
  MLLN th n B M (UP X) ->
  (exists X', X = Top::X') \/ 
  (exists X' m, X = Bot::X' /\ S m = n /\ MLLN th m B M (UP X')) \/ 
  (exists F G X' m, X = F ⅋ G::X' /\ S m = n /\ MLLN th m B M (UP (F::G::X'))) \/ 
  (exists F G X' m, X = F & G::X' /\ S m = n /\ MLLN th m B M (UP (F::X'))/\ MLLN th m B M (UP (G::X'))) \/ 
  (exists i F X' m, X = Quest i F::X' /\ S m = n /\ MLLN th m ((i,F)::B) M (UP X')) \/ 
  (exists F X' m, posLFormula F /\ X = F::X' /\ S m = n /\  MLLN th m B (F::M) (UP X')) \/ 
  (exists F L' m, posFormula F /\ Permutation (F :: L') M /\ S m = n /\  X = [] /\ MLLN th m B L' (DW F)) \/ 
  (exists i F m, ~ posAtom F /\ mt i = true /\ In (i, F) B /\ S m = n /\  X = [] /\ MLLN th m B M (DW F)) \/ 
  (exists F m, ~ posAtom F /\  th F /\ S m = n /\  X = [] /\ MLLN th m B M (DW F)) \/ 
  (exists FX X' m, X = ∀{ FX}::X' /\ uniform_oo FX /\ S m = n /\ (forall x : expr con,
     proper x ->
     MLLN th m B M (UP (FX x :: X'))))
 \/ 
  exists F X', posLFormula F /\ X = F::X' /\ MLLN th n B (F::M) (UP X').

 Proof with sauto.
  intros.
  inversion H...
  * left. exists M0...
  * right. left. exists M0, n0...
  * right. right. left. exists F, G, M0, n0...
  * right. right. right. left. exists F, G, M0, n0...
  * right. right. right. right. left. exists i, F, M0, n0...
  * right. right. right. right. right. left. exists F, M0, n0...
  * right. right. right. right. right. right. left. exists F, L', n0...
  * right. right. right. right. right. right. right. left. exists i, F, n0...
  * rewrite allU in H1... 
  * right. right. right. right. right. right. right. right. left. exists F, n0...
  * right. right. right. right. right. right. right. right. right. left. exists FX, M0, n0...
  * solveSignature1. 
Qed.

 Lemma InvDwPhase (SIU: UNoDSigMMLL) n B L F:
  MLLN th n B L (DW F) ->
  (exists A, F = perp A /\ L = [atom A]) \/
  (exists i A, F = perp A /\ L = [] /\ mt i  = true /\ In (i,atom A) B) \/
(F = One /\ L = []) \/
  (exists P Q M N m, F= (P ⊗ Q) /\ Permutation L (M ++ N) /\ S m = n /\ MLLN th m B M (DW P) /\ MLLN th m B N (DW Q)) \/
 (exists P Q m, F= (P ⊕ Q) /\ S m = n /\ MLLN th m B L (DW P)) \/
  (exists P Q m, F= (P ⊕ Q) /\ S m = n /\ MLLN th m B L (DW Q)) \/
 (exists m, negFormula F /\ S m = n /\ MLLN th m B L (UP [F])) \/
  (exists FX t m, F= ∃{ FX} /\ uniform_oo FX /\  proper t /\  S m = n /\ MLLN th m B L (DW (FX t))) \/
  (exists P m , F= Bang loc P /\  S m = n /\ L = [] /\ MLLN th m B L (UP [P]))  \/ 
  (exists P m , F= Bang loc P /\  S m = n /\ L = [] /\ MLLN th m B L (UP [P])) .
 Proof with sauto.
  intros.
  inversion H... 
  * left. exists A...
  * right. left. exists i, A... rewrite <- H6...
  * right. right. right. left. 
     apply SETXempty in H4, H5... 
     exists F0, G, M, N, n0...
     1-2: rewrite H2...
  * right. right. right. right. left. exists F0, G, n0...
  * right. right. right. right. right. left. exists F0, G, n0...
  * right. right. right. right. right. right. left. exists n0...
  * right. right. right. right. right. right. right. left. exists FX, t, n0...
  * right. right. right. right. right. right. right. right. left. exists F0, n0...
  * right. right. right. right. right. right. right. right. right. 
      finishExponential.
Abort.


(* Lemma absorptionLN : forall n i Gamma Delta F X,
   MLLN th n (Gamma) ( F::Delta)  X ->
   MLLN th n ((i,F):: Gamma) Delta  X.
Proof with sauto.
  intros.
  apply absorptionN...
  apply weakeningN...
Qed.
 *)

Lemma absorptionInN : forall n i Gamma Delta F X,
In (i,F) Gamma -> mt i = true -> u i = true ->
 MLLN th n Gamma( F::Delta)  X ->
      MLLN th n Gamma Delta  X.
Proof with sauto;try solveLL.
  intros.
  apply InPermutation in H...
  apply exchangeCCN with (CC:=(i,F)::x)...
  apply AbsorptionC...
  apply exchangeCCN with (CC:=Gamma)...
  Qed.

(*  Lemma unRelease B M P: 
 MLLS th B M (DW P) -> MLLS th B M (UP [P]).
 Proof with sauto;solveLL.
  intros.
  inversion H...
  all:try LLfocus1.
  apply tri_store'...
  LLfocus1.
  apply tri_store'...
  LLfocus1.
Qed.
 
 Lemma select B M L P: posLFormula P ->
 MLLS th B M (UP (P::L)) -> MLLS th B (P::M) (UP L).
 Proof with sauto;solvePolarity;solveLL.
  intros.
  inversion H0...
Qed.
 *)
Lemma TensorCommN: forall n F G B M,
    (MLLN th n B M (DW (F ⊗ G))) -> (MLLN th n B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;try solveLL.
      intros.
      inversion H... 
      LLtensor N M0 B0 D C.  
      rewrite H2...
      rewrite H3...
 Qed.

Lemma TensorComm: forall F G B M,
    (MLLS th B M (DW (F ⊗ G))) -> (MLLS th B M (DW (G ⊗ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
      LLtensor N M0 B0 D C.  
      rewrite H2...
rewrite H3...
 Qed.
 
Lemma OplusCommN: forall n F G B M,
    (MLLN th n B M (DW (F ⊕ G))) -> (MLLN th n B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Lemma OplusComm: forall F G B M,
    (MLLS th B M (DW (F ⊕ G))) -> (MLLS th B M (DW (G ⊕ F))).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.
 
Lemma WithCommN: forall n F G B M L,
    MLLN th n B M (UP (F & G::L)) -> MLLN th n B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.

Lemma WithComm: forall F G B M L,
    MLLS th B M (UP (F & G::L)) -> MLLS th B M (UP (G & F::L)).
 Proof with sauto;solvePolarity;solveLL.
      intros.
      inversion H... 
 Qed.


(* Lemma BangDistWith: forall F G B M,
    MLLS th B M (DW (! (F & G))) <-> MLLS th B M (DW (! F ⊗ ! G)).
 Proof with sauto;solvePolarity;solveLL.
    split;intros.
   *  inversion H...
       inversion H3...
       FLLsplit.
   *  inversion H...
       inversion H5...
       inversion H6...
 Qed.
 *)
  Example Tensor3 B L F: MLLS th B L (DW (F ⊗ Zero)) <-> MLLS th B L (DW Zero).
  Proof with sauto;solvePolarity.
    split;intros;
    inversion H...
    solveLL.
  Qed.

   
Theorem weakeningGenN CC LC CC' X n:
   SetU CC' -> MLLN th n CC LC X -> MLLN th n (CC'++ CC) LC X.
Proof with sauto.
      intros H1 H2.
      induction CC';simpl;auto.
      apply weakeningN;auto.
      1-2: inversion H1...
Qed.

Theorem weakeningGenN_rev CC LC  CC' X n:
   SetU CC' -> MLLN th n CC LC X -> MLLN th n (CC++ CC') LC X.
Proof.      
      intros H1 H2.
      eapply exchangeCCN with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGenN;auto.
Qed.

Theorem weakening_swap C LC F G X:
   u (fst G) = true -> MLLS th (F::C) LC X -> MLLS th (F :: G:: C) LC X.
Proof with sauto;solveLL. 
     intros.
      eapply exchangeCC.
     rewrite perm_swap;eauto.
     apply weakening;auto.
 Qed.     

 
 Theorem weakening_middle C1 C2 LC  F X:
 u (fst F) = true ->  MLLS th (C1++ C2) LC X -> MLLS th (C1++F :: C2) LC X.
Proof. 
      intros.
     eapply exchangeCC.
     rewrite <- Permutation_middle;eauto.
     apply weakening;auto.
Qed.

 Theorem weakening_last C LC  F X:
 u (fst F) = true ->  MLLS th C LC X -> MLLS th (C++[F]) LC X.
Proof. 
      intros.
     eapply exchangeCC.
     rewrite <- Permutation_cons_append;eauto.
     apply weakening;auto.
Qed.
   
Theorem weakeningGen CC LC  CC' X:
  SetU CC' -> MLLS th CC LC X -> MLLS th (CC' ++ CC) LC X.
Proof.     
     intros H1 H2.
      induction CC';simpl;auto.
      apply weakening;auto.
      1-2: inversion H1;sauto.
Qed.

Theorem weakeningGen_rev CC LC CC' X:
  SetU CC' -> MLLS th CC LC X -> MLLS th (CC++CC') LC X.
Proof.
      intros H1 H2.
      eapply exchangeCC with (CC := CC' ++ CC);auto.
      apply Permutation_app_comm; auto.
      apply weakeningGen;auto.
Qed.

Theorem weakeningHead C1 C2 C1' C2' LC  X:
  SetU (C1 ++ C1') ->  MLLS th (C2++C2') LC X -> MLLS th ((C1++C2) ++ (C1'++C2')) LC X.
Proof.     
     intros H1 H2.
     eapply exchangeCC with 
     (CC:=(C2++C2') ++ (C1++C1')). perm.
     apply weakeningGen_rev;auto.
Qed.


Theorem weakeningTail C1 C2 C1' C2' LC  X:
  SetU (C2 ++ C2') -> MLLS th (C1++C1') LC X -> MLLS th ((C1++C2) ++ (C1'++C2')) LC X.
Proof.     
     intros H1 H2.
     eapply exchangeCC with 
     (CC:=(C2++C2') ++ (C1++C1')). perm.
     apply weakeningGen;auto.
Qed.

Lemma Contraction : forall CC LC  F X ,
  u (fst F) = true -> MLLS th  (F :: F::CC) LC X -> MLLS th (F::CC) LC X.
Proof with sauto.
intros.
  apply contraction with (F:=F)...
Qed.


Lemma contraction_middle : forall C1 C2 LC  F X ,
u (fst F) = true  -> MLLS th  (C1++F::F::C2) LC X -> MLLS th (C1++F::C2) LC X.
Proof with sauto.
intros.
  apply contraction with (F:=F)...
  apply exchangeCC with (CC:= C1 ++ F :: F :: C2)...
Qed.

(* Lemma AbsorptionCSet : forall n C Gamma Delta X,
  MLLN th n (C++Gamma) (Delta++ second C)  X ->
      MLLN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  destruct a.
  eapply AbsorptionL. 
  LLPerm (C ++ Gamma ++ [a]). 
  eapply IHC.
  LLExact H...
  Qed. 

    Lemma AbsorptionCSet' : forall  C Gamma Delta X,
  MLLS  th (C++Gamma) (Delta++ C)  X ->
      MLLS  th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H...
  apply AbsorptionCSet in H...
  apply seqNtoSeq in H...
  Qed. 
  
 Lemma AbsorptionCSet_rev : forall C Gamma Delta X,
  MLLS  th (Gamma++C) (Delta++C)  X ->
      MLLS  th (Gamma++C) Delta  X.
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
  MLLN th n (Gamma) (Delta++ C)  X ->
      MLLN th n (C ++ Gamma) Delta  X.
  Proof with sauto.
  induction C;simpl;intros...
  rewrite app_comm_cons.
  apply absorptionLN.
  apply IHC.
  
  LLExact H...
  Qed. 
 
  Lemma AbsorptionLSet' : forall C Gamma Delta X,
  MLLS th (Gamma) (Delta++C)  X ->
      MLLS th (C ++ Gamma) Delta  X.
  Proof with sauto.
  intros.
  apply seqtoSeqN in H...
  apply AbsorptionLSet in H...
  apply seqNtoSeq in H...
  Qed. 
    
 *)  

(** Some inveribility lemmas *)

Theorem FocusAtom: forall n Gamma Delta A,
 (MLLN th n Gamma Delta (DW ((perp A ) ))) ->
    (Delta = [ (atom A)] /\ SetU Gamma) \/ 
    (Delta = [] /\ 
(exists i C, SetU C -> mt i = true -> Permutation ((i, atom A)::C) Gamma)) . 
 Proof with sauto.
      intros.
      inversion H ...
     right. split... exists i, C...
      inversion H1.
 Qed.

  Theorem FocusingClause (SIU: UNoDSigMMLL): forall n B L A F,
     MLLN th n B L (DW ((perp A) ⊗ F)) ->
 (exists m N, n = S m /\ Permutation L ((atom A)::N)  /\
                MLLN th m B N  (DW F)) \/
   (exists m i, n = S m /\  mt i = true /\  In (i, atom A) B /\
                MLLN th m B L  (DW F)).
  Proof with sauto.
  intros. 
  FLLInversion H. 
  apply SETXempty in H5, H6...
   FLLInversion H10. 
  - left.
    eexists. exists N... 
    rewrite H3... 
  - right.
    eexists.  exists x.
    split...  rewrite H3... rewrite <- H5...  HProof.
 Qed.


  Lemma FocusingInitRuleU (SIU: UNoDSigMMLL) : forall h D A A' B,
      MLLN th h B D (DW ((perp A) ⊗ (perp A') ))  -> 
      Permutation D ([atom A] ++ [atom A']) \/ 
      (exists i, D = [atom A] /\ mt i = true /\ In ((i,atom A')) B) \/ 
      (exists i,D = [atom A'] /\ mt i = true /\ In ((i,atom A)) B) \/
      (exists i j, mt i = true /\ mt j = true /\ In ((i,atom A)) B /\ In ((j,atom A')) B /\ D = []).
  Proof with sauto.
    intros.
    FLLInversion H. 
    apply SETXempty in H5, H6...
    inversion H10...
    - inversion H11... 
    right. left. exists i... rewrite H3. rewrite <- H8...
    inversion H0.
   - inversion H11... 
     right. right. left. exists i... 
     rewrite H3. rewrite <- H8...
    right. right. right.  exists i, i0...
 rewrite H3. rewrite <- H8...
     rewrite H3. rewrite <- H13...
     inversion H5.
 - inversion H0.
 
    Qed.
    
   Theorem FocusingStruct (SIU: UNoDSigMMLL) : forall n a D B A F,
   MLLN th n B D (DW ((perp A) ⊗ (Quest a F))) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((atom A)::N) /\
                MLLN th m ((a,F)::B) N  (UP [] )) \/
    (exists m i, n = S (S (S m))  /\ mt i = true /\ In ((i,atom A)) B /\

                MLLN th m ((a,F)::B) D  (UP [] )).            
   Proof with sauto.
   intros.
  FLLInversion H. 
    apply SETXempty in H5, H6...
    inversion H10...
    - FLLInversion H11. FLLInversion H7.
      left.  exists n0. exists N... 
      HProof.
  -  FLLInversion H11. FLLInversion H12.
      right.
     exists n0, i...    rewrite H3. rewrite <- H8...
     HProof.
  -
    inversion H0.
Qed.
  
Theorem FocusingPar :
    forall n A B D G,
    MLLN th n G D (DW ((atom A) ⅋ ( atom B))) ->
      exists m , n =  S (S(S(S m)))  /\
                 MLLN th m G (atom B::atom A::D) (UP []).
  Proof with sauto.
    intros.
FLLInversion H.
FLLInversion H5.
FLLInversion H4.
FLLInversion H7.
    eexists n.
    split;eauto.
  Qed.

  Theorem FocusingParPos :
    forall n A B D G, posLFormula A -> posLFormula B ->
    MLLN th n G D (DW (A ⅋ B)) ->
      exists m , n =  S (S(S(S m)))  /\
                 MLLN th m G (B::A::D) (UP []).
  Proof with sauto.
    intros.
FLLInversion H1.
FLLInversion H7.
    inversion H6;solvePolarity. 
    inversion H9;solvePolarity. 
    eexists n.
    split;eauto.
  Qed.
  
  Theorem FocusingPlus:
    forall n A B D G ,
    MLLN th n G D (DW ( (atom A) ⊕ (atom B))) ->
     ( exists m , n = (S(S (S m)))  /\
                 (MLLN th m G (atom A ::D) (UP []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 MLLN th m G (atom B::D) (UP []) ).
  Proof with sauto.
    intros.
FLLInversion H.
FLLInversion H4.
FLLInversion H5.

    left.
    eexists n0.
    split;eauto.
FLLInversion H4.
FLLInversion H5.

    right.
    eexists n0.
    split;eauto.
  Qed.

(*
  Theorem FocusingPlusPos:
    forall n a A B D G ,
    MLLN th n G D (DW ( Bang a (atom A) ⊕ Bang a (atom B))) ->
     ( exists m , n = (S(S (S m)))  /\ D = [] /\
                 (MLLN th m G [atom A] (UP []) )) \/
    ( exists m , n = (S(S (S m)))  /\  D = [] /\
                 MLLN th m G [atom B] (UP []) ).
  Proof with sauto.
    intros.
FLLInversion H.
    left.
    eexists n0.
    split;eauto.
    right.
    eexists n0.
    split;eauto.
  Qed.
*) 

  Theorem FocusingWith :
    forall n A B D G,
      MLLN th n G D (DW ( (atom A) & (atom B))) ->
      exists m , n = S(S(S m))  /\
                 ( (MLLN th m G (atom A::D) (UP []) ) /\
                   (MLLN th m G (atom B::D) (UP []) )) .
  Proof with sauto.
    intros.
FLLInversion H.
FLLInversion H5.
FLLInversion H6.
FLLInversion H8.

    eexists n0.
    split;eauto.
  Qed.

(*
  Theorem FocusingWithPos :
    forall n A B D G, posLFormula A -> posLFormula B ->
      MLLN th n G D (DW ( A & B)) ->
      exists m , n = S(S(S m))  /\
                 ( (MLLN th m G (A::D) (UP []) ) /\
                   (MLLN th m G (B::D) (UP []) )) .
  Proof with sauto.
    intros.
    InvTriAll.
    inversion H6;solvePolarity. 
    inversion H9;solvePolarity. 
    eexists n0.
    split;eauto.
  Qed.
  *)
  
  Theorem FocusingTensor  (SIU: UNoDSigMMLL) :
    forall n A B D G,
      MLLN th n G D (DW ( (atom A) ⊗ (atom B))) ->
       exists m M N , n = S(S(S m))  /\ Permutation D (M++N) /\ 
                  ( MLLN th m G (atom A::M) (UP [])) /\
                  ( MLLN th m G (atom B::N) (UP [])).
   Proof with sauto.
    intros.
FLLInversion H.
    apply SETXempty in H5, H6...

FLLInversion H10.
FLLInversion H11.
FLLInversion H7.
FLLInversion H9.
rewrite <- H3 in H12, H13.
    eexists n0.
    eexists M.
    eexists N.
    split;eauto.
   Qed. 

 (* Theorem FocusingTensorPos :
    forall n A B D G,
      MLLN th n G D (DW ( Bang (atom A) ⊗ (atom B))) ->
       exists m , n = S(S(S m))  /\
                  ( MLLN th m G [atom A] (UP [])) /\
                  ( MLLN th m G (atom B::D) (UP [])).
   Proof with sauto.
    intros.
    InvTriAll.
    eexists n0.
    split;eauto.
split;eauto. rewrite H2...
   Qed. 
   *)

   Theorem FocusingClauseL (SIU: UNoDSigMMLL): forall B D A F,
     MLLS th B D (DW F) -> MLLS th B  (atom A::D) (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   LLtensor [atom A] D.
   Qed.  

 Theorem FocusingClauseL' (SIU: UNoDSigMMLL): forall B D D' A F,
   Permutation D (atom A::D') -> MLLS th B D' (DW F) -> MLLS th B  D (DW ((perp A) ⊗ F)).
   Proof with auto using FocusingClauseL.
   intros.
   rewrite H...
  Qed. 

     
   Theorem FocusingClauseC (SIU: UNoDSigMMLL): forall i B D A F,
   mt i = true -> In ((i,atom A)) B ->  MLLS th B D (DW F) -> MLLS th B  D (DW ((perp A) ⊗ F)).
   Proof with sauto.
   intros.
   rewrite <- (app_nil_l D).
   LLtensor (nil (A:=oo)) D.
   apply InPermutation in H0...
   solveLL.
   Qed.  


End FLLReasoning.

Global Hint Resolve unbInit: core.

