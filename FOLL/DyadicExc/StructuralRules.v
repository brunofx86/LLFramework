Require Export LL.FOLL.DyadicExc.PreTactics.
Require Import Coq.Program.Equality.

Export LLNotations.
Import DyadicExcTactics.

Set Implicit Arguments.

Section LL3BasicTheory.
  Context `{OLS: OLSig}.
  
 Section StructuralProperties.
    
 Theorem exchangeLL3N : forall n B1 B2 L,
        Permutation B1 B2 ->
        LL3N n B1 L -> LL3N n B2 L.
   Proof.     
      induction n using strongind;intros.
      + inversion H0;subst;eauto.
      + inversion H1;subst;eauto.
        eapply @ll3_abs with (F:=F).
        rewrite <- H0;auto. 
        eapply H with (B1:=B1);auto.
    Qed.

  Global Instance seq_morphismN  n:
      Proper ((@Permutation oo) ==> eq ==> iff)
             (LL3N n).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (exchangeLL3N H _);auto.
      + apply Permutation_sym in H.
        refine (exchangeLL3N H _);auto.
    Qed.
 
   Theorem exchangeLL3S : forall B1 B2 L,
      Permutation B1 B2 ->
    LL3S B1 L -> LL3S B2 L.
   Proof. 
      intros *.
      intros Hp Hseq.
      generalize dependent B2.
      induction Hseq;intros;eauto using Permutation_in.
    Qed.
 
  Global Instance seq_morphism :
      Proper ((@Permutation oo) ==> (@Permutation oo) ==> iff)
             (LL3S).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      + refine (exchangeLL3S H _);auto.
        LL3exchangeL x0.
      + apply Permutation_sym in H.
        refine (exchangeLL3S H _);auto.
        apply Permutation_sym in H0.
         LL3exchangeL y0. 
    Qed.
 
    Theorem weakeningLL3N : forall n F B L,
        LL3N n B L -> LL3N n (F::B) L.
     Proof with sauto.
    induction n using strongind;intros.
    * inversion H...
    * inversion H0...
      LLstore.
      rewrite perm_swap...
      LLexists t.
      LLcopy F0.
      firstorder.
      LL3exchangeL M.
   Qed.    
 
    Theorem weakeningLL3S F B L:
    LL3S B L -> LL3S (F::B) L.
   Proof with sauto. 
      intros.
    revert dependent F.
    induction H;intros...
    LLstore.
    rewrite perm_swap...
    LLexists t.
    LLcopy F.
    firstorder.
    LL3exchangeL M. 
 Qed.     

Theorem contractionLL3N  : forall n F B L,
   In F B ->  LL3N n (F::B) L -> LL3N n B L.
  Proof with sauto.
  do 2 intro.
  induction n;intros... 
  * inversion H0...
  * inversion H0...
    LLstore.
    rewrite perm_swap in H2... 
    apply IHn in H2...
    LLexists t.
    LLcopy F0.
    inversion H2...
    LL3exchangeL M. 
Qed.

Theorem contractionLL3S  : forall F B L,
    LL3S (B++[F]) L -> In F B -> LL3S B L.
  Proof with sauto.
  intros.
  dependent induction H generalizing B...
  LLstore. 
  apply IHLL3S...
  LLexists t.
  apply in_app_or in H...
  LLcopy F0.
  inversion H2...
  LLcopy F0.
  rewrite <- H...
Qed.
   
End StructuralProperties.
 
 (** Adequacy relating the system with and without inductive meassures *)
  Section Adequacy.
 
    Theorem LL3NtoLL3S : forall n B L, 
    LL3N n B L -> LL3S B L.
    Proof.
        induction n using strongind;intros;eauto.
      + inversion H;subst;eauto.
      + inversion H0;subst;eauto.
    Qed.

    Axiom LL3StoLL3N : forall B L,
        LL3S B L ->  exists n, LL3N n B L.

  End Adequacy.

  Section GeneralResults.

    (** Measure of derivations *)
    Theorem heightGeqLL3N : forall n B L,
        (LL3N n B L) ->
        forall m, m>=n -> LL3N m B L.
    Proof with sauto.
      induction n;intros ...
      + inversion H ...
      + inversion H;subst; try mgt0;intuition.
        LLexists t;eauto;eapply IHn;try lia ...
        LLcopy F;eauto;eapply IHn;try lia ...
        LL3exchangeL M;eauto;eapply IHn;try lia ...
      Qed.

 End GeneralResults.
 End LL3BasicTheory.
 
 Global Hint Resolve weakeningLL3N : core.