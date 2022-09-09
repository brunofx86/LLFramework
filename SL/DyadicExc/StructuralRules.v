Require Export LL.SL.DyadicExc.TacticsPre.
Require Import Coq.Program.Equality.

Set Implicit Arguments.


Section LL3BasicTheory.
  Context `{OLS: OLSig}.
  
 Section StructuralProperties.
    
 Theorem LL3exchangeNC : forall n CC CC' LC,
        Permutation CC CC' ->
        LL3N n CC LC -> LL3N n CC' LC.
   Proof.     
      induction n using strongind;intros.
      + inversion H0;subst;eauto.
      + inversion H1;subst;eauto.
        eapply @ll3_abs with (F:=F).
        rewrite <- H0;auto. 
        eapply H with (CC:=CC);auto.
    Qed.


   Theorem LL3exchangeC (CC CC' LC : multiset oo):
      Permutation CC CC' ->
    LL3S CC LC-> LL3S CC' LC.
   Proof. 
      intros Hp Hseq.
      generalize dependent CC'.
      induction Hseq;intros;eauto using Permutation_in.
    Qed.

   Global Instance seq_morphismN  n:
      Proper ((@Permutation oo) ==> eq ==> iff)
             (LL3N n).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      +  refine (LL3exchangeNC H _);auto.
      + apply Permutation_sym in H.
        refine (LL3exchangeNC H _);auto.
    Qed.
  
  Global Instance seq_morphism :
      Proper ((@Permutation oo) ==> (@Permutation oo) ==> iff)
             (LL3S).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      split; intro;subst.
      + refine (LL3exchangeC H _);auto.
        LL3exchangeL x0.
      + apply Permutation_sym in H.
        refine (LL3exchangeC H _);auto.
        apply Permutation_sym in H0.
         LL3exchangeL y0. 
    Qed.
 
    Theorem LL3weakeningN : forall n CC LC  F ,
        (LL3N n CC LC) -> LL3N n (F :: CC) LC.
     Proof with sauto.
    induction n using strongind;intros.
    * inversion H...
    * inversion H0...
      LL3store.
      rewrite perm_swap...
      LL3exist t.
      LL3copy F0.
      firstorder.
      LL3exchangeL M.
   Qed.    
 
    Theorem weakening (CC LC : multiset oo) F:
    LL3S CC LC -> LL3S (F :: CC) LC.
   Proof with sauto. 
      intros.
    revert dependent F.
    induction H;intros...
    LL3store.
    rewrite perm_swap...
    LL3exist t.
    LL3copy F.
    firstorder.
    LL3exchangeL M. 
 Qed.     

Theorem LL3contractionN  : forall n F CC LC,
    LL3N n (F :: CC) LC -> In F CC -> LL3N n CC LC.
  Proof with sauto.
  do 2 intro.
  induction n;intros... 
  * inversion H...
  * inversion H...
    LL3store.
    rewrite perm_swap in H2... 
    apply IHn in H2...
    LL3exist t.
    LL3copy F0.
    inversion H2...
    LL3exchangeL M.
Qed.

Theorem LL3contraction  : forall F CC LC,
    LL3S (CC++[F]) LC -> In F CC -> LL3S CC LC.
  Proof with sauto.
  intros.
  dependent induction H generalizing CC...
  LL3store. 
  apply IHLL3S...
  LL3exist t.
  apply in_app_or in H...
  LL3copy F0.
  inversion H2...
  LL3copy F0.
  rewrite <- H...
Qed.

   
End StructuralProperties.
 
  Section GeneralResults.
    (** Measure of derivations *)
    Theorem HeightGeq : forall n Gamma Delta,
        (LL3N n Gamma Delta) ->
        forall m, m>=n -> LL3N m Gamma Delta.
    Proof with sauto.
      induction n;intros ...
      + inversion H ...
      + inversion H;subst; try mgt0;intuition.
        LL3exist t;eauto;eapply IHn;try lia ...
        LL3copy F;eauto;eapply IHn;try lia ...
        LL3exchangeL M;eauto;eapply IHn;try lia ...
      Qed.

  End GeneralResults.

  (** Adequacy relating the system with and without inductive meassures *)
  Section Adequacy.
 
    Theorem LL3NtoLL3S : forall n Gamma Delta , 
    (LL3N n Gamma Delta) -> LL3S Gamma Delta.
      induction n using strongind;intros;eauto.
      + inversion H;subst;eauto.
      + inversion H0;subst;eauto.
    Qed.

    Axiom LL3StoLL3N : forall Gamma Delta,
        (LL3S Gamma Delta) ->  exists n, (LL3N n Gamma Delta).

    
  End Adequacy.


 End LL3BasicTheory.
 
 Global Hint Resolve LL3weakeningN : core.
 
 
