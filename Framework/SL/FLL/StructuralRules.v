

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
   FLLN th n CC LC X -> FLLN th n CC' LC X.
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
   FLLN th n CC LC X -> FLLN th n CC LC' X.
Proof with sauto;solveLL.
  induction n using strongind;intros. 
  * inversion H0 ...
  * inversion H1...
     all: eauto.
     LLfocus1 F L'.
Qed.

(**  Weakening on the classical context *)
Theorem weakeningN: forall n CC LC F X,
   FLLN th n CC LC X -> FLLN th n (F :: CC) LC X.
Proof with sauto;solveLL.
  induction n using strongind;intros.
  * inversion H...
  * inversion H0...
     all: eauto.
     refine (exchangeCCN (perm_swap F0  F CC) _)... 
     LLfocus2 F0. 
Qed.    
  
(** Contraction on the classical context *)
Theorem contractionN  : forall n CC LC  F X ,
   FLLN th n (F :: CC) LC X -> In F CC -> FLLN th n CC LC X.
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
 FLLN th n (F :: Gamma) ( F::Delta)  X ->
      FLLN th n (F :: Gamma) Delta  X.
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
         LLtensor x N .
         apply H...
         eapply exchangeLCN.
         rewrite <- H1...
         auto. } 
      { apply InPermutation in H1;
         destruct H1.
         rewrite H1 in H2;simpl in H2.
         rewrite <- perm_takeit_2 in H2.
         apply Permutation_cons_inv in H2.
         LLtensor M x.
         eapply exchangeLCN in H4.
         2: rewrite H1... 
         auto. } 
    + refine (exchangeCCN (perm_swap F0 F Gamma) _)...  apply H...
       refine (exchangeCCN (perm_swap F F0 Gamma) _)...
    +  apply H...
       refine (exchangeLCN (perm_swap F F0 Delta) _)...
    + checkPermutationCases H3. 
        LLfocus2 F. 
        inversion H1;inversion H2...
        eapply exchangeLCN  with (LC:=L')...
        eapply exchangeLCN with (LC:=(F0 :: x))...
        LLfocus1.
        apply H...
        eapply exchangeLCN with (LC:=L')...
Qed.

Lemma absorptionLN : forall n Gamma Delta F X,
   FLLN th n (Gamma) ( F::Delta)  X ->
   FLLN th n (F:: Gamma) Delta  X.
Proof with sauto.
  intros.
  apply absorptionN...
  apply weakeningN...
Qed.

Lemma absorptionInN : forall n Gamma Delta F X,
In F Gamma ->
 FLLN th n Gamma( F::Delta)  X ->
      FLLN th n Gamma Delta  X.
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


 
Theorem FLLNtoFLLS : forall n Gamma Delta X , 
FLLN th n Gamma Delta X -> FLLS  th Gamma Delta X.
Proof.
  induction n using strongind;intros;eauto.
  * inversion H;subst;eauto.
  * inversion H0;subst;eauto.
    pose proof (exchangeCCN (Permutation_cons_append Gamma F) H2);eauto... 
Qed.

Axiom FLLStoFLLN : forall Gamma Delta X ,
   FLLS th Gamma Delta X -> exists n, FLLN th n Gamma Delta X.

End Adequacy.
Section StructuralProperties.

(**  Exchange Rule: Classical Context *)
Theorem exchangeCC (CC CC' LC : list oo) (X: Arrow):
   Permutation CC CC' ->
   FLLS th CC LC X -> FLLS th CC' LC X.
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
   FLLS th CC LC X -> FLLS th CC LC' X.
Proof with sauto;solveLL.
  intros.
  revert dependent LC'.
  induction H0;intros...
  all: eauto.
  LLfocus1 F L'.  
Qed.  

(**  Weakening on the classical context *)
Theorem weakening (CC LC : list oo) F X:
   FLLS th CC LC X -> FLLS th (F :: CC) LC X.
Proof with sauto;solveLL. 
  intros.
  revert dependent F.
  induction H;intros...
  all: eauto.
  LLfocus2 F.
Qed.     

Lemma contraction : forall CC LC  F X ,
  FLLS th  (F :: CC) LC X -> In F CC -> FLLS th CC LC X.
Proof with sauto;solveLL.
  intros.
  dependent induction H...
  all: eauto.
  * inversion H... 
  * rewrite <- app_comm_cons in IHFLLS. 
     eapply IHFLLS...
  * inversion H0...
     all: eauto. 
Qed.

Lemma absorption : forall Gamma Delta F X,
 FLLS th (Gamma++[F]) (F::Delta)  X ->
      FLLS th  (Gamma++[F]) Delta  X.
Proof with sauto;solveLL.
 Abort.

End StructuralProperties.
 
  
Global Instance seq_morphismN  n:
  Proper ((@Permutation oo) ==> (@Permutation oo) ==> eq ==> iff)
              (FLLN th n).
Proof.
  unfold Proper; unfold respectful.
  intros B1 L1 HP1 B2 L2 HP2.
  split; intro;subst.
  * refine (exchangeCCN HP1 _);auto.
     refine (exchangeLCN HP2 _);auto.
  * refine (exchangeCCN (symmetry HP1) _);auto.
     refine (exchangeLCN (symmetry HP2) _);auto.
Qed.
   
Global Instance seq_morphism  :
   Proper ((@Permutation oo) ==> (@Permutation oo) ==> eq ==> iff)
              (FLLS th).
Proof.
  unfold Proper; unfold respectful.
  intros B1 L1 HP1 B2 L2 HP2.
  split; intro;subst.
  * refine (exchangeCC HP1 _);auto.
     refine (exchangeLC HP2 _);auto.
  * refine (exchangeCC (symmetry HP1) _);auto.
     refine (exchangeLC (symmetry HP2) _);auto.
Qed.

 (**  Weakening on the theory [theory] *)
Section WeakeningTheory. 
  
Variable theory theory' : oo ->Prop .
    
Theorem WeakTheoryN : forall n CC LC X ,
        (forall F, theory F -> theory' F) ->
        FLLN theory n CC LC X -> FLLN theory' n CC LC X.
Proof.     
  induction n using strongind;intros.
  * inversion H0;eauto.
  * inversion H1;subst;eauto.
Qed.
    
Theorem WeakTheory : forall CC LC X,
        (forall F, theory F -> theory' F) ->
        FLLS theory CC LC X -> FLLS theory'  CC LC X.
Proof.    
  intros.
  induction H0;eauto.
Qed.

End WeakeningTheory.

Definition EmptyTheory (F :oo) := False.

Lemma EmptySubSetN : forall (theory : oo-> Prop) CC LC X n,
      FLLN EmptyTheory n CC LC X -> FLLN theory n CC LC X.
Proof.    
  intros.
  apply WeakTheoryN with (theory:= EmptyTheory);auto.
  intros F HeT.
  inversion HeT.
Qed.
  
Lemma EmptySubSet : forall (theory : oo-> Prop) CC LC X,
      FLLS EmptyTheory CC LC X -> FLLS theory CC LC X.
Proof.
  intros.
  apply WeakTheory with (theory:= EmptyTheory);auto.
  intros F HeT.
  inversion HeT.
Qed.
 
Section GeneralResults.
    
(** Measure of derivations *)
Theorem heightGeqFLLN : forall n Gamma Delta X,
  FLLN th n Gamma Delta X ->
        forall m, m>=n -> FLLN th m Gamma Delta X.
Proof with sauto.
  induction n;intros ...
  * inversion H ...
  * inversion H;subst; try mgt0;intuition.
     LLtensor M N;eapply IHn;try lia ...
     LLexists t;eapply IHn;try lia...
     LLfocus1 F L';eapply IHn;try lia...
     LLfocus2 F;eapply IHn;try lia...
     LLtheory F;eapply IHn;try lia...
Qed.

 (** heightGeqFLLN with Exchange Classic Context *)
Theorem heightGeqFLLNCEx : forall n CC LC CC' X, 
  Permutation CC' CC ->
  FLLN th n CC LC X ->
        forall m, m>=n -> (FLLN th m CC' LC X).
Proof with eauto.
  intros.
  eapply heightGeqFLLN with (n:=n);auto...
  symmetry in H.
  eapply exchangeCCN;eauto.
Qed.

(** heightGeqFLLN with Exchange Linear Context *)
Theorem heightGeqFLLNLEx : forall n CC LC LC' X, 
  Permutation LC LC' ->
  FLLN th n CC LC' X ->
        forall m, m>=n -> (FLLN th m CC LC X).
Proof with eauto.
  intros.
  eapply heightGeqFLLN with (n:=n);auto.
  symmetry in H.
  eapply exchangeLCN;eauto.
Qed.
    
Theorem heightGeqFLLNEx : forall n CC CC' LC LC' X, 
  Permutation CC CC' ->
  Permutation LC LC' ->
  FLLN th n CC' LC' X ->
        forall m, m>=n -> (FLLN th m CC LC X).
Proof with eauto.
  intros.
  eapply heightGeqFLLN with (n:=n);auto...
  symmetry in H.
  symmetry in H0.
  eapply exchangeLCN;eauto.
  eapply exchangeCCN;eauto.
Qed.  
 
Theorem BangCon: forall n F Gamma Delta X , posLFormula F ->
FLLN th n Gamma (Bang F::Delta) X -> FLLS  th Gamma (F::Delta) X.
Proof with sauto.
  induction n using strongind;intros;eauto.
  * inversion H0;subst;eauto.
  * inversion H1;subst;eauto.
   + checkPermutationCases H3.
     LLtensor (F::x) N.
     rewrite <- H6...
     eapply H with (m:=n)...
     rewrite <- H3...
     apply FLLNtoFLLS in H5...
     LLtensor M (F::x).
     rewrite <- H6...
     apply FLLNtoFLLS in H4...    
     eapply H with (m:=n)...
     rewrite <- H3...
 + apply H in H3... solveLL. 
     rewrite <- Permutation_cons_append...
   + rewrite perm_swap in H4...
     LLstore.
     rewrite perm_swap...
     eapply H with (m:=n)...
   + checkPermutationCases H4.
     - inversion H5...
       2:{ inversion H4... }
       apply FLLNtoFLLS in H9.
       inversion H9;inversion H0...
     - LLfocus1 F0 (F::x).
       rewrite H4...
       eapply H with (m:=n)...
       rewrite <- H6...
 Qed.      

Theorem BangConN: forall n F Gamma Delta X , posLFormula F -> 
FLLN th n Gamma (Bang F::Delta) X -> FLLN  th n Gamma (F::Delta) X.
Proof with sauto.
  induction n using strongind;intros;eauto.
  * inversion H0;subst;eauto.
  * inversion H1;subst;eauto.
   + checkPermutationCases H3.
      rewrite H3 in H4.
      apply H in H4...
     LLtensor (F::x) N.
     rewrite <- H6...
      rewrite H3 in H5.
      apply H in H5...
     LLtensor M (F::x).
     rewrite <- H6...
     + rewrite perm_swap in H4...
        apply H in H4...
     LLstore.
     rewrite perm_swap...
   + checkPermutationCases H4.
     - inversion H5...
       2:{ inversion H4... }
       inversion H9; solvePolarity. 
      eapply heightGeqFLLN. exact H11.
       lia.
     - rewrite H6 in H5. 
       apply H in H5... 
      LLfocus1 F0 (F::x).
            rewrite H4...
 Qed.      

End GeneralResults.

End FLLBasicTheory.
