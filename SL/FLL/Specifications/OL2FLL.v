(** * Syntax for Object Ligics (OL). 

This file defines the general requirements imposed on the syntax of OLs to prove cut-elimination.

 *)

Require Export OL.Syntax.
Require Export LL.SL.FLL.Syntax. 

Set Implicit Arguments.

Section OLSyntax.

Context `{OL: OLSyntax}.

 (** Positive atoms are only [down] and [up] atoms. The linear and the classical context of the encoding must contain only formulas of this kind *)

Inductive IsPositiveAtomFormula : oo -> Prop :=
  | IsFPA_dw : forall A, isOLFormula A -> IsPositiveAtomFormula (atom (down (A)))
  | IsFPA_up : forall A, isOLFormula A -> IsPositiveAtomFormula (atom (up (A))).


Inductive IsPositiveAtomBFormula : oo -> Prop :=
  | IsFBPA_dw : forall A, isOLFormula A -> IsPositiveAtomBFormula (atom (down (A)))
 | IsFBPA_up : forall A, isOLFormula A -> IsPositiveAtomBFormula  (atom (up (A))) 
 | IsFBPA_up' : forall A, isOLFormula A -> IsPositiveAtomBFormula (Bang (atom (up (A)))).

Definition IsPositiveAtomFormulaL L : Prop := Forall IsPositiveAtomFormula L.
Definition IsPositiveAtomBFormulaL L : Prop := Forall IsPositiveAtomBFormula L.

(** Embedding OL formulas in LL formulas *)
Definition LEncode L:= 
        map (fun x =>atom (down x )) L.
Definition REncode L:= 
        map (fun x => atom (up x )) L.
Definition REncodeB L:= 
        map (fun x => Bang (atom (up x ))) L.

End OLSyntax.

Global Hint Constructors IsPositiveAtomFormula IsPositiveAtomBFormula : core.

Global Hint Unfold LEncode REncode REncodeB IsPositiveAtomFormulaL IsPositiveAtomBFormulaL: core.

Notation "⌈ A ⌉" := ( atom (up A)) (at level 10) .
Notation "⌊ A ⌋" := ( atom (down A)) (at level 10) .
Notation "⌈ A ⌉^" := ( perp (up A)) (at level 10) .
Notation "⌊ A ⌋^" := ( perp (down A)) (at level 10) .

Declare Scope encode.
Notation "⌜ L ⌝" := (REncode L) (at level 10).
Notation "⌞ L ⌟" := (LEncode L) (at level 10).
Notation "!  ⌜ L ⌝" := (REncodeB L) (at level 10).