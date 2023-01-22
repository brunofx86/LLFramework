(** * Syntax for Object Ligics (OL). 

This file defines the general requirements imposed on the syntax of OLs to prove cut-elimination.

 *)

Require Export LL.Misc.Utils.
Export ListNotations.

Set Implicit Arguments.

(** ** Object Logic Signature *)

(** This signature includes the types for the Object Level quantifiers
as well as the definitions for the binary and unary connectives and the
quantifiers. We assume that these types will be filled in by a Coq
inductive Set, e.g., 

[OLType := nat], 
[Inductive connectives := cand | cor | cimp . ], and 
[Inductive quantifiers := qex | qall . 
 *)

Class OLSyntax := {
  OLType:Set;
  ccon : Set ; (* 0 ary connectives *)
  ucon : Set ; (* unary connectives *)
  bcon : Set ; (* binary connectives *)
  qcon : Set (* quantifiers *)
}.

(** ** Definition of the OL Syntax  *)

(** This module defines the [con] type needed in [Hybrid]. Such type
includes constructors for the atoms of the Object Logic, the binary
and unary connectives and also the quantifiers (of the object logic). 
Measures and constructors for those types are also provided *)

Section OLSyntax.
Context `{OL: OLSyntax}.

  
(** Syntax of the Object logic *)
Inductive Econ: Set :=
  | oo_term : OLType -> Econ    (* Coercion --terms *)
  | oo_atom : nat -> Econ (* names for atoms *)
  | oo_ccon : ccon -> Econ
  | oo_ucon : ucon -> Econ
  | oo_bcon : bcon -> Econ (* binary connectives *)
  | oo_qcon : qcon -> Econ (* quantifiers *)
.

(** Notation for Syntax *)
Definition uexp : Set := expr Econ.
Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (BND Econ).

(** Terms *)
Definition t_term (t:OLType)   :=  (CON (oo_term  t)) .  
(** Atoms  *)
Definition t_atom (id:nat) (A:uexp)  := APP (CON (oo_atom  id)) A. 

(** Constants *)
Definition t_ccon ct := CON (oo_ccon ct) .
  
(** Unary connectives *)
Definition t_ucon uc := fun F => APP (CON (oo_ucon uc)) F .

(** Binnary connectives *)
Definition t_bcon bc :=
    fun F G => APP (APP (CON (oo_bcon bc)) F) G.
(** Quantifiers *)
Definition t_qcon qc :=
    fun F => (APP (CON (oo_qcon qc)) (lambda F)).
  
(** *** Well-formedness conditions *)
Inductive isOLTerm : uexp -> Prop :=
  | isOLTermT  : forall t, isOLTerm (t_term  t).

Inductive isOLAtom : uexp -> Prop :=
  | isOLAtomAt : forall t id , isOLTerm t -> isOLAtom (t_atom id t).

Inductive isOLConstant : uexp -> Prop :=
  | isOLCons : forall id , isOLConstant (t_ccon id)
  .  
Inductive isOLFormula : uexp -> Prop :=
  | isFAtom : forall t id , isOLTerm t -> isOLFormula (t_atom id t)
  | isFCons : forall id, isOLConstant id -> isOLFormula id
  | isFUn : forall uc F, isOLFormula F ->  isOLFormula (t_ucon uc F)
  | isFBin : forall bc F G, isOLFormula F -> isOLFormula G -> isOLFormula (t_bcon bc F G)
  | isFQ : forall qc (FX : uexp -> uexp),
      uniform FX -> (forall (t:uexp), proper t -> isOLFormula (FX t)) ->
      isOLFormula (t_qcon qc FX) .
 
(** Well formendness conditions for lists of formulas and list of judgments *)

Definition isOLFormulaL  L : Prop := Forall isOLFormula L.
  
   (** We count the number of constructors (CON) in the
  expression. Note that the measure of a formula is independent of the
  terms in the atoms *)

Inductive lengthUexp : uexp -> nat -> Prop :=
  | l_Var : forall (v:var), lengthUexp (Var v) 0
  | l_t_term : forall (t:OLType), lengthUexp (t_term t) 0
  | l_t_atomU : forall (id:nat) (A:uexp), lengthUexp (t_atom id A) 1
  | l_ccon : forall id, lengthUexp (t_ccon id) 1
  | l_ucon : forall uc (M1:uexp) (n1:nat),
      lengthUexp M1 n1 ->  lengthUexp (t_ucon uc M1) (S n1)
  | l_tbin : forall bc (M1 M2:uexp) (n1 n2:nat),
      lengthUexp M1 n1 -> lengthUexp M2 n2 ->
      lengthUexp (t_bcon bc M1 M2) (S (n1 + n2))
  | l_tall : forall qc (M:uexp -> uexp) (n:nat),
      uniform M -> lengthUexp (M (Var 0%nat%nat)) n -> lengthUexp (t_qcon qc M) (S n).

(** ** LL predicated needed in the encoding *)

(** Predicates [up] (formulas on the right of the OL sequent) and
  [down] (formulas on the left of the OL sequent) *)
Inductive atm' : Set :=
  | up' : uexp -> atm'    (* formulas on the right *)
  | down' : uexp -> atm'  (* formulas on the left *).

(** Uniform Predicate for atoms *)
Inductive uniform_atm' : (uexp -> atm') -> Prop :=
  | uniform_up: forall FX, uniform FX -> uniform_atm' (fun x:uexp => up' (FX x))
  | uniform_down: forall FX, uniform FX -> uniform_atm' (fun x:uexp => down' (FX x)).
  
Global Instance OLSyntaxIns : OLSig := {|
  atm := atm';
  con := Econ ;
  uniform_atm := uniform_atm' |}.

Definition up : uexp -> atm := up'.
Definition down : uexp -> atm := down'.


End OLSyntax.

Global Hint Constructors isOLTerm isOLAtom isOLConstant isOLFormula : core.
Global Hint Constructors lengthUexp: core.
Global Hint Unfold isOLFormulaL: core.