(** * Structural Rules

This file proves some structural properties as exchange (for the
classical and linear context) as well as weakening and contraction in
the classical context. *)

Require Export LL.Misc.Utils. 
Require Export LL.SL.FLL.PreTactics.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

Section FLLBasicTheory.
  Context `{OLS: OLSig}.
  Variable th th': oo -> Prop.

(** Adequacy relating the system with and without inductive meassures *)
  
Section Adequacy.


 
Theorem seqNtoSeq : forall n Gamma Delta X , 
seqN th n Gamma Delta X -> seq  th Gamma Delta X.
Proof.
  induction n using strongind;intros;eauto.
  * inversion H;subst;eauto.
  * inversion H0;subst;eauto.
Qed.

Axiom seqtoSeqN : forall Gamma Delta X ,
   seq th Gamma Delta X -> exists n, seqN th n Gamma Delta X.

End Adequacy.

Section StructuralPropertiesN.

(**  Exchange Rule: Classical Context *)
Theorem exchangeCCN: forall n CC CC' LC X,
   Permutation CC CC' ->
   seqN th n CC LC X -> seqN th n CC' LC X.
Proof with sauto;solveLL.
  induction n using strongind;intros...
  * inversion H0...
     eauto using Permutation_in.
  * inversion H1... 
     eauto using Permutation_in.
     all: eauto using Permutation_in.
     eapply H with (CC:=CC++[F])...
     rewrite H0...
Qed.

(** Exchange Rule: Linear Context *)
Theorem exchangeLCN: forall n CC LC LC' X,
   Permutation LC LC' ->
   seqN th n CC LC X -> seqN th n CC LC' X.
Proof with sauto;solveLL.
  induction n using strongind;intros. 
  * inversion H0 ...
  * inversion H1...
     all: eauto.
     LFocus F L'.
Qed.

(**  Weakening on the classical context *)
Theorem weakeningN: forall n CC LC F X,
   seqN th n CC LC X -> seqN th n (F :: CC) LC X.
Proof with sauto;solveLL.
  induction n using strongind;intros.
  * inversion H...
  * inversion H0...
     all: eauto.
     CFocus F0. 
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
     all:eauto.
     rewrite <- app_comm_cons in H3.
     apply H in H3...
     inversion H4...
     all:eauto.
Qed.

Lemma absorptionN : forall n Gamma Delta F X,
 seqN th n (F :: Gamma) ( F::Delta)  X ->
      seqN th n (F :: Gamma) Delta  X.
Proof with sauto;solveLL.
  intro.
  induction n using strongind ;intros. 
  * inversion H...
  * inversion H0...
     all: eauto.
    + apply PermutationInCons in H2 as H2'.
        apply in_app_or in H2'.
        destruct H2'.
      { apply InPermutation in H1;
         destruct H1.
         rewrite H1 in H2;simpl in H2.
         apply Permutation_cons_inv in H2.
         FLLsplit x N .
         apply H...
         eapply exchangeLCN.
         rewrite <- H1...
         auto. } 
      { apply InPermutation in H1;
         destruct H1.
         rewrite H1 in H2;simpl in H2.
         rewrite <- perm_takeit_2 in H2.
         apply Permutation_cons_inv in H2.
         FLLsplit M x.
         eapply exchangeLCN in H4.
         2: rewrite H1... 
         auto. } 
    + apply H... 
        eapply exchangeLCN.
        2: exact H3.
        perm.
    + checkPermutationCases H3. 
        CFocus F. 
        inversion H1;inversion H2...
        eapply exchangeLCN  with (LC:=L')...
        eapply exchangeLCN with (LC:=(F0 :: x))...
        LFocus.
        apply H...
        eapply exchangeLCN with (LC:=L')...
Qed.

Lemma absorptionLN : forall n Gamma Delta F X,
   seqN th n (Gamma) ( F::Delta)  X ->
   seqN th n (F:: Gamma) Delta  X.
Proof with sauto.
  intros.
  apply absorptionN...
  apply weakeningN...
Qed.

Lemma absorptionInN : forall n Gamma Delta F X,
In F Gamma ->
 seqN th n Gamma( F::Delta)  X ->
      seqN th n Gamma Delta  X.
Proof with sauto;solveLL.
  intros.
  apply InPermutation in H...
  apply exchangeCCN with (CC:=F::x)...
  apply absorptionN.
  apply exchangeCCN with (CC:=Gamma)...
  Qed.
 
End StructuralPropertiesN.

Section StructuralProperties.

(**  Exchange Rule: Classical Context *)
Theorem exchangeCC (CC CC' LC : list oo) (X: Arrow):
   Permutation CC CC' ->
   seq th CC LC X -> seq th CC' LC X.
Proof with solveLL.
  intros Hp Hseq.
  generalize dependent CC'.
  induction Hseq;intros;eauto using Permutation_in...
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
  all: eauto.
  LFocus F L'.  
Qed.  

(**  Weakening on the classical context *)
Theorem weakening (CC LC : list oo) F X:
   seq th CC LC X -> seq th (F :: CC) LC X.
Proof with sauto;solveLL. 
  intros.
  revert dependent F.
  induction H;intros...
  all: eauto.
  CFocus F.
Qed.     

Lemma contract : forall CC LC  F X ,
  seq th  (F :: CC) LC X -> In F CC -> seq th CC LC X.
Proof with sauto;solveLL.
  intros.
  dependent induction H...
  all: eauto.
  * inversion H... 
  * rewrite <- app_comm_cons in IHseq.
     eapply IHseq...
  * inversion H0...
     all: eauto. 
Qed.

Lemma absorption : forall Gamma Delta F X,
 seq th (F::Gamma) (F::Delta)  X ->
      seq th  (F::Gamma) Delta  X.
Proof with sauto;solveLL.
 Abort.

End StructuralProperties.
 
  
Global Instance seq_morphismN  n:
  Proper ((@Permutation oo) ==> (@Permutation oo) ==> eq ==> iff)
              (seqN th n).
Proof.
  unfold Proper; unfold respectful.
  intros.
  split; intro;subst.
  * refine (exchangeCCN H _);auto.
     refine (exchangeLCN H0 _);auto.
  * apply Permutation_sym in H.
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
  * refine (exchangeCC H _);auto.
     refine (exchangeLC H0 _);auto.
  * apply Permutation_sym in H.
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
  * inversion H0;eauto.
  * inversion H1;subst;eauto.
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
  * inversion H ...
  * inversion H;subst; try mgt0;intuition.
     FLLsplit M N;eapply IHn;try lia ...
     FLLexists t;eapply IHn;try lia...
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

End FLLBasicTheory.
