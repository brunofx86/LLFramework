(** * Syntax for Object Ligics (OL). 

This file defines the general requirements imposed on the syntax of OLs to prove cut-elimination.

 *)

Require Export LL.Framework.OL.Syntax.
Require Export LL.Framework.SL.MMLL.Syntax. 

Set Implicit Arguments.

Section OLSyntax.

Context `{OL: OLSyntax}.
Context `{SI: SigMMLL}.

 (** Positive atoms are only [down] and [up] atoms. The linear and the classical context of the encoding must contain only formulas of this kind *)

Inductive posAtomFormula : oo -> Prop :=
  | IsFPA_dw : forall A, isOLFormula A -> posAtomFormula (atom (down (A)))
  | IsFPA_up : forall A, isOLFormula A -> posAtomFormula (atom (up (A))).


Inductive posAtomBFormula : oo -> Prop :=
  | IsFBPA_dw : forall A, isOLFormula A -> posAtomBFormula (atom (down (A)))
 | IsFBPA_up : forall A, isOLFormula A -> posAtomBFormula  (atom (up (A))) 
 | IsFBPA_up' : forall A a, isOLFormula A -> posAtomBFormula (Bang a (atom (up (A)))).

Definition posAtomFormulaL L : Prop := Forall posAtomFormula L.
Definition posAtomBFormulaL L : Prop := Forall posAtomBFormula L.

(** Embedding OL formulas in LL formulas *)
Definition LEncode L:= 
        map (fun x =>atom (down x )) L.
Definition REncode L:= 
        map (fun x => atom (up x )) L.
Definition REncodeB a L:= 
        map (fun x => Bang a (atom (up x ))) L.

Definition CEncode (i:subexp) (L:list oo) : list (subexp*oo) := 
        map (fun x => (i,x)) L.
 
End OLSyntax.

Global Hint Constructors posAtomFormula posAtomBFormula : core.

Global Hint Unfold LEncode REncode REncodeB posAtomFormulaL posAtomBFormulaL: core.

Notation "⌈ A ⌉" := ( atom (up A)) (at level 10) .
Notation "⌊ A ⌋" := ( atom (down A)) (at level 10) .
Notation "⌈ A ⌉^" := ( perp (up A)) (at level 10) .
Notation "⌊ A ⌋^" := ( perp (down A)) (at level 10) .

Declare Scope encode.
Notation "⌜ L ⌝" := (REncode L) (at level 10).
Notation "⌞ L ⌟" := (LEncode L) (at level 10).
Notation "! a  ⌜ L ⌝" := (REncodeB a L) (at level 10).