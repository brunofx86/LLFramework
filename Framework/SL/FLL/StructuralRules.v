

(** * Structural Rules

This file proves some structural properties as exchange (for the
classical and linear context) as well as weakening and contraction in
the classical context. *)

Require Export LL.Misc.Utils. 
Require Export LL.Framework.SL.FLL.PreTactics.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

Section FLLBasicTheory.
  Context `{OLS: OLSig}.
  Variable th th': oo -> Prop.

Section StructuralPropertiesN.

(**  Exchange Rule: Classical Context *)
Theorem exchangeCCN: forall n CC CC' LC X,
   Permutation CC CC' ->
   flln th n CC LC X -> flln th n CC' LC X.
Proof with sauto;solveLL.
  induction n using strongind;intros...
  * inversion H0...
     eauto using Permutation_in.
  * inversion H1... 
     eauto using Permutation_in.
     all: eauto using Permutation_in.
Qed.

(** Exchange Rule: Linear Context *)
Theorem exchangeLCN: forall n CC LC LC' X,
   Permutation LC LC' ->
   flln th n CC LC X -> flln th n CC LC' X.
Proof with sauto;solveLL.
  induction n using strongind;intros. 
  * inversion H0 ...
  * inversion H1...
     all: eauto.
     LFocus F L'.
Qed.

(**  Weakening on the classical context *)
Theorem weakeningN: forall n CC LC F X,
   flln th n CC LC X -> flln th n (F :: CC) LC X.
Proof with sauto;solveLL.
  induction n using strongind;intros.
  * inversion H...
  * inversion H0...
     all: eauto.
     refine (exchangeCCN (perm_swap F0  F CC) _)... 
     CFocus F0. 
Qed.    
  
(** Contraction on the classical context *)
Theorem contractionN  : forall n CC LC  F X ,
   flln th n (F :: CC) LC X -> In F CC -> flln th n CC LC X.
Proof with CleanContext;solveLL.
  induction n using strongind;intros.
  * inversion H...
     inversion H1...
  * inversion H0...
     inversion H2...
     all:eauto.
     pose proof (exchangeCCN (perm_swap F  F0 CC) H3)... 
     apply H in H2...
     inversion H4...
     all:eauto.
Qed.

Lemma absorptionN : forall n Gamma Delta F X,
 flln th n (F :: Gamma) ( F::Delta)  X ->
      flln th n (F :: Gamma) Delta  X.
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
    + refine (exchangeCCN (perm_swap F0 F Gamma) _)...  apply H...
       refine (exchangeCCN (perm_swap F F0 Gamma) _)...
    +  apply H...
       refine (exchangeLCN (perm_swap F F0 Delta) _)...
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
   flln th n (Gamma) ( F::Delta)  X ->
   flln th n (F:: Gamma) Delta  X.
Proof with sauto.
  intros.
  apply absorptionN...
  apply weakeningN...
Qed.

Lemma absorptionInN : forall n Gamma Delta F X,
In F Gamma ->
 flln th n Gamma( F::Delta)  X ->
      flln th n Gamma Delta  X.
Proof with sauto;solveLL.
  intros.
  apply InPermutation in H...
  apply exchangeCCN with (CC:=F::x)...
  apply absorptionN.
  apply exchangeCCN with (CC:=Gamma)...
  Qed.
 
End StructuralPropertiesN.

(** Adequacy relating the system with and without inductive meassures *)
  
Section Adequacy.


 
Theorem seqNtoSeq : forall n Gamma Delta X , 
flln th n Gamma Delta X -> flls  th Gamma Delta X.
Proof.
  induction n using strongind;intros;eauto.
  * inversion H;subst;eauto.
  * inversion H0;subst;eauto.
    pose proof (exchangeCCN (Permutation_cons_append Gamma F) H2);eauto... 
Qed.

Axiom seqtoSeqN : forall Gamma Delta X ,
   flls th Gamma Delta X -> exists n, flln th n Gamma Delta X.

End Adequacy.
Section StructuralProperties.

(**  Exchange Rule: Classical Context *)
Theorem exchangeCC (CC CC' LC : list oo) (X: Arrow):
   Permutation CC CC' ->
   flls th CC LC X -> flls th CC' LC X.
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
   flls th CC LC X -> flls th CC LC' X.
Proof with sauto;solveLL.
  intros.
  revert dependent LC'.
  induction H0;intros...
  all: eauto.
  LFocus F L'.  
Qed.  

(**  Weakening on the classical context *)
Theorem weakening (CC LC : list oo) F X:
   flls th CC LC X -> flls th (F :: CC) LC X.
Proof with sauto;solveLL. 
  intros.
  revert dependent F.
  induction H;intros...
  all: eauto.
  CFocus F.
Qed.     

Lemma contract : forall CC LC  F X ,
  flls th  (F :: CC) LC X -> In F CC -> flls th CC LC X.
Proof with sauto;solveLL.
  intros.
  dependent induction H...
  all: eauto.
  * inversion H... 
  * rewrite <- app_comm_cons in IHflls. 
     eapply IHflls...
  * inversion H0...
     all: eauto. 
Qed.

Lemma absorption : forall Gamma Delta F X,
 flls th (Gamma++[F]) (F::Delta)  X ->
      flls th  (Gamma++[F]) Delta  X.
Proof with sauto;solveLL.
 Abort.

End StructuralProperties.
 
  
Global Instance seq_morphismN  n:
  Proper ((@Permutation oo) ==> (@Permutation oo) ==> eq ==> iff)
              (flln th n).
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
              (flls th).
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
        flln theory n CC LC X -> flln theory' n CC LC X.
Proof.     
  induction n using strongind;intros.
  * inversion H0;eauto.
  * inversion H1;subst;eauto.
Qed.
    
Theorem WeakTheory : forall CC LC X,
        (forall F, theory F -> theory' F) ->
        flls theory CC LC X -> flls theory'  CC LC X.
Proof.    
  intros.
  induction H0;eauto.
Qed.

End WeakeningTheory.

Definition EmptyTheory (F :oo) := False.

Lemma EmptySubSetN : forall (theory : oo-> Prop) CC LC X n,
      flln EmptyTheory n CC LC X -> flln theory n CC LC X.
Proof.    
  intros.
  apply WeakTheoryN with (theory:= EmptyTheory);auto.
  intros.
  inversion H0.
Qed.
  
Lemma EmptySubSet : forall (theory : oo-> Prop) CC LC X,
      flls EmptyTheory CC LC X -> flls theory CC LC X.
Proof.
  intros.
  apply WeakTheory with (theory:= EmptyTheory);auto.
  intros.
  inversion H0.
Qed.
 
Section GeneralResults.
    
(** Measure of derivations *)
Theorem HeightGeq : forall n Gamma Delta X,
  flln th n Gamma Delta X ->
        forall m, m>=n -> flln th m Gamma Delta X.
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
  flln th n CC LC X ->
        forall m, m>=n -> (flln th m CC' LC X).
Proof with eauto.
  intros.
  eapply HeightGeq with (n:=n);auto...
  symmetry in H.
  eapply exchangeCCN;eauto.
Qed.

(** HeightGeq with Exchange Linear Context *)
Theorem HeightGeqLEx : forall n CC LC LC' X, 
  Permutation LC LC' ->
  flln th n CC LC' X ->
        forall m, m>=n -> (flln th m CC LC X).
Proof with eauto.
  intros.
  eapply HeightGeq with (n:=n);auto.
  symmetry in H.
  eapply exchangeLCN;eauto.
Qed.
    
Theorem HeightGeqEx : forall n CC CC' LC LC' X, 
  Permutation CC CC' ->
  Permutation LC LC' ->
  flln th n CC' LC' X ->
        forall m, m>=n -> (flln th m CC LC X).
Proof with eauto.
  intros.
  eapply HeightGeq with (n:=n);auto...
  symmetry in H.
  symmetry in H0.
  eapply exchangeLCN;eauto.
  eapply exchangeCCN;eauto.
Qed.  
 
Theorem BangCon: forall n F Gamma Delta X , positiveLFormula F ->
flln th n Gamma (Bang F::Delta) X -> flls  th Gamma (F::Delta) X.
Proof with sauto.
  induction n using strongind;intros;eauto.
  * inversion H0;subst;eauto.
  * inversion H1;subst;eauto.
   + checkPermutationCases H3.
     FLLsplit (F::x) N.
     rewrite <- H6...
     eapply H with (m:=n)...
     rewrite <- H3...
     apply seqNtoSeq in H5...
     FLLsplit M (F::x).
     rewrite <- H6...
     apply seqNtoSeq in H4...    
     eapply H with (m:=n)...
     rewrite <- H3...
 + apply H in H3... solveLL. 
     rewrite <- Permutation_cons_append...
   + rewrite perm_swap in H4...
     FLLstore.
     rewrite perm_swap...
     eapply H with (m:=n)...
   + checkPermutationCases H4.
     - inversion H5...
       2:{ inversion H4... }
       apply seqNtoSeq in H9.
       inversion H9;inversion H0...
     - LFocus F0 (F::x).
       rewrite H4...
       eapply H with (m:=n)...
       rewrite <- H6...
 Qed.      

Theorem BangConN: forall n F Gamma Delta X , positiveLFormula F -> 
flln th n Gamma (Bang F::Delta) X -> flln  th n Gamma (F::Delta) X.
Proof with sauto.
  induction n using strongind;intros;eauto.
  * inversion H0;subst;eauto.
  * inversion H1;subst;eauto.
   + checkPermutationCases H3.
      rewrite H3 in H4.
      apply H in H4...
     FLLsplit (F::x) N.
     rewrite <- H6...
      rewrite H3 in H5.
      apply H in H5...
     FLLsplit M (F::x).
     rewrite <- H6...
     + rewrite perm_swap in H4...
        apply H in H4...
     FLLstore.
     rewrite perm_swap...
   + checkPermutationCases H4.
     - inversion H5...
       2:{ inversion H4... }
       inversion H9; solvePolarity. 
      eapply HeightGeq. exact H11.
       lia.
     - rewrite H6 in H5. 
       apply H in H5... 
      LFocus F0 (F::x).
            rewrite H4...
 Qed.      

End GeneralResults.

End FLLBasicTheory.
