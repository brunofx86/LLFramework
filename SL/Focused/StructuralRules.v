(** * Structural Rules

This file proves some structural properties as exchange (for the
classical and linear context) as well as weakening and contraction in
the classical context. *)

Require Export LL.Misc.Utils. 
Require Export LL.SL.Focused.TacticsPre.
Require Import Coq.Program.Equality.
Set Implicit Arguments.


Section FLLBasicTheory.
  Context `{OLS: OLSig}.
  Variable th : oo -> Prop.

Section StructuralPropertiesN.

(**  Exchange Rule: Classical Context *)
Theorem exchangeCCN : forall n  CC CC' LC  (X: Arrow) ,
   Permutation CC CC' ->
   seqN th n CC LC X -> seqN th n CC' LC X.
Proof with sauto;solveLL.
      induction n using strongind;intros...
      + inversion H0...
          eauto using Permutation_in.
      + inversion H1... 
        eauto using Permutation_in.
        all: eauto using Permutation_in.
        eapply H with (CC:=CC++[F])...
        rewrite H0...
Qed.

(** Exchange Rule: Linear Context *)
Theorem exchangeLCN : forall n CC LC LC'  (X: Arrow),
   Permutation LC LC' ->
   seqN th n CC LC X -> seqN th n CC LC' X.
Proof with sauto;solveLL.
      induction n using strongind;intros.
      + inversion H0 ...
      + inversion H1...
        7:FLLsplit M N. 
        all: eauto.
        LFocus F L'.
Qed.

(**  Weakening on the classical context *)
Theorem weakeningN : forall n CC LC  F X ,
   seqN th n CC LC X -> seqN th n (F :: CC) LC X.
Proof with sauto;solveLL.
    induction n using strongind;intros.
    * inversion H...
    * inversion H0...
      FLLsplit M N.
      rewrite <- app_comm_cons...
      FLLexists t.
       LFocus F0 L'. 
      CFocus F0.
      TFocus F0. 
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

(** Contraction on the classical context *)
Theorem contractionN  : forall n CC LC  F X ,
   seqN th n (F :: CC) LC X -> In F CC -> seqN th n CC LC X.
Proof with CleanContext;solveLL.
  induction n using strongind;intros.
  * inversion H...
    inversion H1...
  * inversion H0...
     inversion H2...
     1-9:eauto.
     rewrite <- app_comm_cons in H3.
     apply H in H3...
     1-5:eauto.
     inversion H4...
     all:eauto.
Qed.

End StructuralPropertiesN.

Section StructuralProperties.

(**  Exchange Rule: Classical Context *)
Theorem exchangeCC (CC CC' LC : list oo) (X: Arrow):
   Permutation CC CC' ->
   seq th CC LC X -> seq th CC' LC X.
Proof with sauto.
      intros Hp Hseq.
      generalize dependent CC'.
      induction Hseq;intros;eauto using Permutation_in.
      FLLstorec.
      eapply IHHseq... 
       rewrite Hp...
Qed.

(** Exchange Rule: Linear Context *)
Theorem exchangeLC LC : forall CC LC'  (X: Arrow),
   Permutation LC LC' ->
   seq th CC LC X -> seq th CC LC' X.
Proof with sauto;solveLL.
    intros.
    revert dependent LC'.
    induction H0;intros...
    FLLsplit M N. 
    FLLexists t.
    LFocus F L'.  
    CFocus F.
    TFocus F.
    
Qed.  

(**  Weakening on the classical context *)
Theorem weakening (CC LC : list oo) F X:
   seq th CC LC X -> seq th (F :: CC) LC X.
Proof with sauto;solveLL. 
      intros.
    revert dependent F.
    induction H;intros...
    FLLsplit M N.  
    rewrite <- app_comm_cons...
    FLLexists t.
    LFocus F L'. 
    CFocus F.
    TFocus F.     
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


Lemma contract : forall CC LC  F X ,
  seq th  (F :: CC) LC X -> In F CC -> seq th CC LC X.
Proof with sauto.
intros.
dependent induction H...
- inversion H... 
- FLLleft. 
  eapply IHseq... 
- FLLright.
  eapply IHseq... 
- FLLwith.
  eapply IHseq1... 
  eapply IHseq2...
- FLLbot.
  eapply IHseq...
- FLLpar. 
  eapply IHseq... 
-  FLLsplit M N. 
  eapply IHseq1...
  eapply IHseq2... 
- FLLstorec.
  rewrite <- app_comm_cons in IHseq.
  eapply IHseq...
- FLLbang.  
  eapply IHseq...
 - FLLexists t. 
  eapply IHseq...
 - FLLforall.
  eapply H1...
- FLLrelease. 
  eapply IHseq...
- FLLstore. 
  eapply IHseq...
- LFocus F0 L'.
 eapply IHseq...
- inversion H0... 
  CFocus F0.
  eapply IHseq...
 CFocus F0.
  eapply IHseq...
  -
TFocus F0.
  eapply IHseq...
  
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

End StructuralProperties.
 
  
Global Instance seq_morphismN  n:
  Proper ((@Permutation oo) ==> (@Permutation oo) ==> eq ==> iff)
              (seqN th n).
Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeCCN H _);auto.
         refine (exchangeLCN H0 _);auto.
      + apply Permutation_sym in H.
        apply Permutation_sym in H0.
        refine (exchangeCCN H _);auto.
        refine (exchangeLCN H0 _);auto.
Qed.
   
Global Instance seq_morphism  :
   Proper ((@Permutation oo) ==> (@Permutation oo) ==> eq ==> iff)
              (seq th).
Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeCC H _);auto.
         refine (exchangeLC H0 _);auto.
      + apply Permutation_sym in H.
        apply Permutation_sym in H0.
        refine (exchangeCC H _);auto.
        refine (exchangeLC H0 _);auto.
Qed.

 (**  Weakening on the theory [theory] *)
  Section WeakeningTheory. 
  
    Variable theory theory' : oo ->Prop .
    
    Theorem WeakTheoryN : forall n CC LC X ,
        (forall F, theory F -> theory' F) ->
        seqN theory n CC LC X -> seqN theory' n CC LC X.
   Proof.     
      induction n using strongind;intros.
      + inversion H0;eauto.
      + inversion H1;subst;eauto.
    Qed.
    
    Theorem WeakTheory : forall CC LC X,
        (forall F, theory F -> theory' F) ->
        seq theory CC LC X -> seq theory'  CC LC X.
    Proof.    
      intros.
      induction H0;eauto.
    Qed.

  End WeakeningTheory.

  Definition EmptyTheory (F :oo) := False.
  Lemma EmptySubSetN : forall (theory : oo-> Prop) CC LC X n,
      seqN EmptyTheory n CC LC X -> seqN theory n CC LC X.
  Proof.    
    intros.
    apply WeakTheoryN with (theory:= EmptyTheory);auto.
    intros.
    inversion H0.
  Qed.
  
  Lemma EmptySubSet : forall (theory : oo-> Prop) CC LC X,
      seq EmptyTheory CC LC X -> seq theory CC LC X.
  Proof.
    intros.
    apply WeakTheory with (theory:= EmptyTheory);auto.
    intros.
    inversion H0.
  Qed.
  
Section GeneralResults.
    
(** Measure of derivations *)
Theorem HeightGeq : forall n Gamma Delta X,
  seqN th n Gamma Delta X ->
        forall m, m>=n -> seqN th m Gamma Delta X.
Proof with sauto.
      induction n;intros ...
      + inversion H ...
      + inversion H;subst; try mgt0;intuition.
        (* FLLsplit *)
        FLLsplit M N;eapply IHn;try lia ...
        (* exists*)
        FLLexists t;eapply IHn;try lia...
        
        (* dec *)
        LFocus F L';eapply IHn;try lia...
        CFocus F;eapply IHn;try lia...
        TFocus F;eapply IHn;try lia...
Qed.

 (** HeightGeq with Exchange Classic Context *)
Theorem HeightGeqCEx : forall n CC LC CC' X, 
  Permutation CC' CC ->
  seqN th n CC LC X ->
        forall m, m>=n -> (seqN th m CC' LC X).
Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto...
      symmetry in H.
      eapply exchangeCCN;eauto.
Qed.

(** HeightGeq with Exchange Linear Context *)
Theorem HeightGeqLEx : forall n CC LC LC' X, 
  Permutation LC LC' ->
  seqN th n CC LC' X ->
        forall m, m>=n -> (seqN th m CC LC X).
Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto.
      symmetry in H.
      eapply exchangeLCN;eauto.
Qed.
    
Theorem HeightGeqEx : forall n CC CC' LC LC' X, 
  Permutation CC CC' ->
  Permutation LC LC' ->
  seqN th n CC' LC' X ->
        forall m, m>=n -> (seqN th m CC LC X).
Proof with eauto.
      intros.
      eapply HeightGeq with (n:=n);auto...
      symmetry in H.
      symmetry in H0.
      eapply exchangeLCN;eauto.
      eapply exchangeCCN;eauto.
Qed.  
 
End GeneralResults.

  (** Adequacy relating the system with and without inductive meassures *)
  
Section Adequacy.
 
Theorem seqNtoSeq : forall n Gamma Delta X ,  (seqN th n Gamma Delta X) -> seq  th Gamma Delta X.
Proof.
      induction n using strongind;intros;eauto.
      + inversion H;subst;eauto.
      + inversion H0;subst;eauto.
Qed.

Axiom seqtoSeqN : forall Gamma Delta X ,
   seq th Gamma Delta X ->  exists n, (seqN th n Gamma Delta X).

End Adequacy.

End FLLBasicTheory.
