(** This file defines the general requirements imposed on the syntax of OLs to prove cut-elimination. *)
Require Import LL.Misc.UtilsTactics. 
Require Export LL.Framework.OL.Syntax. 
Set Implicit Arguments.

Section OLSyntax.
Context `{OL:OLSyntax}.

(** Some results regarding the length of formulas *)

Section FormulaLength.

Lemma LengthTerm : forall F, isOLTerm F -> lengthUexp F 0.
Proof with sauto.   
  intros.
  inversion H... 
Qed.
  
Lemma LengthFormula : forall F n, isOLFormula F -> lengthUexp F n -> n > 0.
Proof with sauto.  
  intros.
  induction H;simpl.
  all: multimatch goal with
       H: lengthUexp _ _ |- _ => inversion H;sauto
   end.
    - inversion H... 
    - inversion H...   
Qed.

Lemma lengthAtom : forall id t, isOLFormula (t_atom id t)  -> lengthUexp (t_atom id t) 1.
Proof with sauto.  
  intros. 
  inversion H...
Qed.

Lemma lengthCons : forall id , isOLFormula (t_ccon id )  -> lengthUexp (t_ccon id) 1.
Proof with sauto.  
  intros.
  inversion H...
Qed.
    

Lemma lengthUnary : forall lab F n , isOLFormula (t_ucon lab F) -> lengthUexp F n -> lengthUexp (t_ucon lab F) (S n).
Proof with sauto.   
  intros... 
Qed.

      
Lemma lengthBin : forall lab F G n m, isOLFormula (t_bcon lab F  G) -> lengthUexp F n -> lengthUexp G m -> lengthUexp (t_bcon lab F G) (S (n+m)).
Proof with sauto.  
    intros... 
Qed.

  Lemma lengthAll : forall lab FX n, uniform FX -> isOLFormula (t_qcon lab FX) -> lengthUexp (FX (Var 0%nat%nat)) n -> lengthUexp  (t_qcon lab  FX) (S n).
Proof with sauto. 
  intros...
Qed.

(** [lengthUexp] is indeed a function *)
Lemma lengthFunction : forall n F , isOLFormula F -> lengthUexp F n -> forall n', lengthUexp F n' -> n = n'.
Proof with sauto.
  induction n using strongind;intros ...
  apply LengthFormula in H0...
  - inversion H0...
  - inversion H1...
    + inversion H2...
    + inversion H2...
    + inversion H2...
        cut (n = n1).
        intros... 
        eapply H with (F:= M1)...
        inversion H0...
        inversion H3...
    + inversion H2...
        cut (n1 = n0).
        intros...
        cut (n2 = n3).
        intros...
        eapply H with (F:= M2)...
        inversion H0...
        inversion H3...
        eapply H with (F:= M1)...
        inversion H0...
        inversion H3...
    + inversion H2...
        cut (n = n0).
        intros...
        apply lbindEq in H5...
        eapply H with (F:= M0 (Var 0%nat))...
        all: try rewrite H5...
        inversion H0...
        inversion H3...
        apply lbindEq in H8...
        rewrite <- H8...
        apply H11...
        all: try solve [apply proper_VAR].
Qed.        
    
Lemma lengthBinSizeL :
    forall F G C n n',
      isOLFormula F -> isOLFormula G ->
      lengthUexp (t_bcon C F G) n -> lengthUexp F n' ->
      n' < n.
Proof with sauto.
  intros.
  inversion H1... 
  generalize (lengthFunction H H7);intros.
  apply H3 in H2...
Qed.
  
Lemma lengthBinSizeR :
    forall F G C n n', isOLFormula F -> isOLFormula G ->
                       lengthUexp (t_bcon C F G) n ->
                       lengthUexp G n' ->
                       n' < n.
Proof with sauto.
  intros.
  inversion H1...
  generalize (lengthFunction H0 H8);intros.
  apply H3 in H2...
Qed.

Lemma length1 : forall F ,
        isOLFormula F -> lengthUexp F 1 ->
        isOLAtom F \/ isOLConstant F.
Proof with sauto.
  intros.
  inversion H ...
  - inversion H0...
     generalize (LengthFormula H1 H3);lia.
  - inversion H0...
     assert (n1 = 0%nat) by lia.
     generalize (LengthFormula H2 H8);intro... lia.
  -  inversion H0 ...
     generalize (lbindEq  H6  H1 H4);intro.
     assert (proper (Var 0%nat)) by constructor.
     generalize (H3 _ H5);intro. rewrite H8 in H7.
     apply H2 in H5.
     generalize (LengthFormula H5 H7 );lia.
Qed.

(** Proper conditions *)
  
Lemma isOLTermProper : forall t, isOLTerm t -> proper t.
Proof.
  intros.
  inversion H.
  unfold t_term.
  auto with hybrid.
Qed.

Lemma isOLAtomProper : forall t, isOLAtom t -> proper t.
Proof.
  intros.
  inversion H.
  unfold t_atom.
  inversion H0;subst.
  unfold t_term.
  auto with hybrid.
Qed.

Lemma isOLFormulaProper : forall F, isOLFormula F -> proper F.
Proof with repeat constructor;auto.
  intros.
  induction H.
  * inversion H ...
  * inversion H...
  * constructor; eauto with hybrid.
  * constructor; eauto with hybrid.
  * constructor; eauto with hybrid.
Qed.
  
Hint Constructors uniform_atm' : core.

(** Well Formedness Conditions *)
Lemma uniform_at : forall (FX:uexp->uexp),
      uniform FX -> uniform (fun x => FX x).
Proof.
  intros.
  auto with hybrid.
Qed.
 
End FormulaLength.

End OLSyntax.
Global Hint Resolve uniform_at : core.
