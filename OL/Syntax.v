(** * Syntax for Object Ligics (OL). 

This file defines the general requirements imposed on the syntax of OLs to prove cut-elimination.

 *)

Require Export LL.Misc.Hybrid.
Require Export LL.SL.Focused.FLLTactics.
Export ListNotations.
Export LLNotations.
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
  constants : Set ; (* 0 ary connectives *)
  uconnectives : Set ; (* unary connectives *)
  connectives : Set ; (* binary connectives *)
  quantifiers : Set (* quantifiers *)
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
  | oo_cons : constants -> Econ
  | oo_un : uconnectives -> Econ
  | oo_bin : connectives -> Econ (* binary connectives *)
  | oo_q : quantifiers -> Econ (* quantifiers *)
  | oo_atom : nat -> Econ (* names for atoms *)
  | oo_term : OLType -> Econ    (* Coercion --terms *).

(** Notation for Syntax *)
Definition uexp : Set := expr Econ.
Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (BND Econ).

(** Terms *)
Definition t_term (t:OLType)   :=  (CON (oo_term  t)) .  
(** Atoms  *)
Definition t_atom (id:nat) (A:uexp)  := APP (CON (oo_atom  id)) A. 

(** Constants *)
Definition t_cons (lab :constants)  := CON (oo_cons lab) .
  
(** Unary connectives *)
Definition t_ucon (lab : uconnectives) := fun F => APP (CON (oo_un lab )) F .

(** Binnary connectives *)
Definition t_bin (lab : connectives)   :=
    fun M1 M2 => APP (APP (CON (oo_bin lab )) M1) M2.
(** Quantifiers *)
Definition t_quant (lab : quantifiers)  :=
    fun M => (APP (CON (oo_q lab)) (lambda M)).
  
(** *** Well-formedness conditions *)
Inductive isOLTerm : uexp -> Prop :=
  | isOLTermT  : forall t, isOLTerm (t_term  t).

Inductive isOLAtom : uexp -> Prop :=
  | isOLAtomAt : forall t id , isOLTerm t -> isOLAtom (t_atom id t).

Inductive isOLConstant : uexp -> Prop :=
  | isOLCons : forall id , isOLConstant (t_cons id)
  .  
Inductive isOLFormula : uexp -> Prop :=
  | isFAtom : forall t id , isOLTerm t -> isOLFormula (t_atom id t)
  | isFCons : forall id , isOLConstant id -> isOLFormula id
  | isFUn : forall (lab : uconnectives) F ,
      isOLFormula F ->  isOLFormula ( t_ucon lab F)
  | isFBin : forall (lab : connectives) F G,
      isOLFormula F -> isOLFormula G -> isOLFormula ( t_bin lab F G)
  | isFQ : forall lab (FX : uexp -> uexp),
      uniform FX -> (forall (t:uexp), proper t -> isOLFormula (FX t)) ->
      isOLFormula (t_quant lab FX) .
 
(** Well formendness conditions for lists of formulas and list of judgments *)

Definition isOLFormulaL  L : Prop := Forall isOLFormula L.
  
   (** We count the number of constructors (CON) in the
  expression. Note that the measure of a formula is independent of the
  terms in the atoms *)

Inductive lengthUexp : uexp -> nat -> Prop :=
  | l_Var : forall (v:var), lengthUexp (Var v) 0
  | l_t_term : forall (t:OLType), lengthUexp (t_term t) 0
  | l_t_atomU : forall (id:nat) (A:uexp), lengthUexp (t_atom id A) 1
  | l_cons : forall id, lengthUexp (t_cons id) 1
  | l_ucon : forall (lab:uconnectives) (M1:uexp) (n1:nat),
      lengthUexp M1 n1 ->  lengthUexp (t_ucon lab M1) (S n1)
  | l_tbin : forall (lab:connectives) (M1 M2:uexp) (n1 n2:nat),
      lengthUexp M1 n1 -> lengthUexp M2 n2 ->
      lengthUexp (t_bin lab M1 M2) (S (n1 + n2))
  | l_tall : forall (lab:quantifiers) (M:uexp -> uexp) (n:nat),
      uniform M -> lengthUexp (M (Var 0%nat%nat)) n -> lengthUexp (t_quant lab M) (S n).

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

 (** Positive atoms are only [down] and [up] atoms. The linear and the classical context of the encoding must contain only formulas of this kind *)

Inductive IsPositiveAtomFormula : oo -> Prop :=
  | IsFPA_dw : forall A, isOLFormula A -> IsPositiveAtomFormula (atom (down (A)))
  | IsFPA_up : forall A, isOLFormula A -> IsPositiveAtomFormula (atom (up (A))).

Definition IsPositiveAtomFormulaL L : Prop := Forall IsPositiveAtomFormula L.

(** Embedding OL formulas in LL formulas *)
Definition LEncode L:= 
        map (fun x =>atom (down x )) L.
Definition REncode L:= 
        map (fun x => atom (up x )) L.

End OLSyntax.

Global Hint Constructors isOLTerm isOLAtom isOLConstant isOLFormula : core.

Global Hint Unfold LEncode REncode : core.

Notation "'⌈' A '⌉'" := ( (up A)) (at level 10) .
Notation "'⌊' A '⌋'" := ( (down A)) (at level 10) .

Declare Scope encode.
Notation "'⌊' L '⌋'" := (LEncode L) (at level 10) :encode.
Notation "'⌈' L '⌉'" := (REncode L) (at level 10) :encode.
