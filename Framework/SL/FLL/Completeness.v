  Require Import LL.FOLL.Dyadic.Tactics.
Require Import LL.Framework.SL.FLL.InvPositivePhase.


Set Implicit Arguments.

Section Adequacy.
  Context `{OLS: OLSig}.
    
Section Soundness.

  Lemma comp n : forall B L X, seqN n B L X -> LL3S B ((Arrow2LL X)++L).
  Proof with subst;auto.
    induction n;intros...
  - inversion H;simpl...
    rewrite perm_takeit_8...
    LL3copy (atom A).
  - inversion H;simpl...
    + rewrite perm_takeit_8...
    + LL3copy (atom A).
    + rewrite H1. LL3tensor. 
      apply IHn in H2...
      apply IHn in H3...
    + LL3plus1. 
      apply IHn in H1...
    + LL3plus2. 
      apply IHn in H1...
    + LL3bang. 
      apply IHn in H1...
    + apply IHn in H2...
    + LL3bot. 
      apply IHn in H1...
    + LL3par. 
      apply IHn in H1...
    + LL3with. 
      apply IHn in H1...
      apply IHn in H2...
    + LL3store. 
      apply IHn in H1...
    + apply IHn in H2...
      simpl in H2.
      rewrite Permutation_middle...
    + apply IHn in H3...
      simpl in H3.
      rewrite <- H2...
    + apply IHn in H3...
      simpl in H3.
      LL3copy F.
    + apply IHn in H3...
      simpl in H3.
      LL3exist t. 
    + LL3forall. 
      apply H2 in H0.
      apply IHn in H0...
 Qed.
  
  (** Well formedness conditions for arrows. *)
  Definition isArrow (A:Arrow) : Prop :=
    match A with
    | UP l => isFormulaL l
    | DW F => isFormula F
    end.


Lemma compInv n : forall B L,
Forall isFormula L ->
          LL3N n B L -> seq B [] (UP L).
  Proof with sauto;solveLL;solveForall.
  induction n;intros...
  - inversion H0...
  - inversion H0...
    + apply IHn in H2. 
      apply IHn in H3. 
      do 2 rewrite <- (app_nil_r [F ** G]).
      rewrite app_assoc_reverse. 
      apply InvTensor.
      eapply (EquivUpArrow2 _ H2)...
      eapply (EquivUpArrow2 _ H3)...
      admit.
      admit.
    + apply IHn in H2. 
      do 2 rewrite <- (app_nil_r [F op G]).
      rewrite app_assoc_reverse. 
      apply InvPlus.
      eapply (EquivUpArrow2 _ H2)...
      admit.
    + apply IHn in H2. 
      do 2 rewrite <- (app_nil_r [F op G]).
      rewrite app_assoc_reverse. 
      apply InvPlusComm.
      eapply (EquivUpArrow2 _ H2)...
      admit.
    + apply IHn in H2.
      LFocus.
      admit.
    + apply IHn in H3. 
      eapply (EquivUpArrow2 _ H3)...
      admit.
    + apply IHn in H2...
    + apply IHn in H2...
      admit.
      admit.
    + apply IHn in H2...
      admit.
    + apply IHn in H3...
      admit.
    + apply IHn in H2...
    + apply IHn in H3...
      apply EquivUpArrow2 with (L':= L++[F]) in H3...
      apply AbsorptionClassic in H3...
      admit.
      admit.
    + apply IHn in H4...
      do 2 rewrite <- (app_nil_r [E{FX}]).
      rewrite app_assoc_reverse. 
      apply @InvEx with (t:=t)...
      eapply (EquivUpArrow2 _ H4)...
      admit.
    + apply H3 in properX.
      apply IHn in properX...
       
      admit. 
Qed.      
      
    
Lemma asas M : forall L B N, Forall positiveFormula M -> 
      |-f- B; M++N; UP L <-> |-f- B; N; UP (M++L).
Proof with subst;auto.
 split;intros.
 - revert dependent B.
 
   revert N L.
   revert dependent M.
   intro.
  induction M;intros...
inversion H...
 rewrite <- app_comm_cons.
 apply tri_store'.  
  left;auto.
  eapply IHM...
  admit.
- revert dependent B.
 
   revert N L.
   revert dependent M.
   intro.
  induction M;intros...
 rewrite <- app_comm_cons in H0.
inversion H...
inversion H0;subst; try solve [ inversion H3 ]...
  eapply IHM in H8...
  admit.
Admitted.
 
Lemma asas' M : forall L B N,  
      |-f- B; M++N; UP L <-> |-f- B; N; UP (M++L).
Proof with subst;auto.
 split;intros.
 - revert dependent B.
 
   revert N L.
   revert dependent M.
   intro.
  induction M;intros...
inversion H...
 rewrite <- app_comm_cons.
 apply tri_store'.  
  left;auto.
  eapply IHM...
  admit.
- revert dependent B.
 
   revert N L.
   revert dependent M.
   intro.
  induction M;intros...
 rewrite <- app_comm_cons in H0.
inversion H...
inversion H0;subst; try solve [ inversion H3 ]...
  eapply IHM in H8...
  admit.
Admitted.
  
  Lemma compInv' : (forall n B M L, Forall positiveFormula M ->
          LL3N n B (M++L) -> seq B M (UP L)) <->
         
          (forall n B L, LL3N n B L -> seq B [] (UP L)).
  Proof with subst;auto.
  split;intros.
  - eapply H with (n:=n);auto.
  - destruct M.
    eapply H with (n:=n);auto.
    rewrite <- app_comm_cons in H1.
    apply H in H1.
    inversion H0...
    inversion H1;subst;try solve [inversion H4]...
    apply asas in H9... 
    admit.
  Admitted.
  
Lemma compInvF : forall n B M L, Forall positiveFormula M ->
          LL3N n B (M++L) -> seq B M (UP L).
  Proof with subst;auto.
  apply compInv'.
  apply compInv.
Qed.  
  
  