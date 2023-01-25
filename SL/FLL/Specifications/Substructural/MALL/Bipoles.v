(** * System MALL for propositional multiplicative and additive linear logic

This file encodes the inference rules of the system MALL (two sided)
of propositional multiplicative additive linear logic.
 *)


Require Import LL.SL.FLL.Specifications.Bipoles. 

 
(** ** Syntax *)
(* conjunction, disjunction and implication *)
Inductive MALLCon := TENSOR | PAR | WITH | OPLUS .

#[export]Instance MALLSyntax : OLSyntax:=
  {|
    OLType := nat;
    ccon := Empty_set ;
    ucon := Empty_set;
    bcon := MALLCon ;
    qcon := Empty_set
  |}.

(** ** Inference rules *)

(** *** Constants *)
Definition MALLrulesC (c:ccon) :=
  match c return ruleC with
  end.

(** *** Unary connectives *)
Definition MALLrulesU  (c:ucon) :=
  match c return ruleU with
  end.

(** *** Binary connectives *)
Definition MALLrulesB (c :bcon) :=
  match c with
  | TENSOR => {| rb_rgtBody := fun F G => MAnd (atom (up F)) (atom (up G) );
                 rb_lftBody  := fun F G => MOr (atom (down F) ) (atom (down G)) |}
  | PAR => {| rb_rgtBody := fun F G => MOr (atom (up F)) (atom (up G) );
              rb_lftBody  := fun F G => MAnd (atom (down F) ) (atom (down G)) |}
  | WITH => {| rb_rgtBody := fun F G => AAnd (atom (up F)) (atom (up G) );
                 rb_lftBody  := fun F G => AOr (atom (down F) ) (atom (down G)) |}
  | OPLUS => {| rb_rgtBody := fun F G => AOr (atom (up F)) (atom (up G) );
             rb_lftBody  := fun F G => AAnd (atom (down F) ) (atom (down G)) |}
  end.

(** *** Quantifiers *)
Definition MALLrulesQ (c :qcon) :=
  match c return ruleQ with
  end.

#[export] Instance MALLRules : OORules :=
  {|
    rulesC := MALLrulesC;
    rulesU := MALLrulesU ;
    rulesB := MALLrulesB;
    rulesQ := MALLrulesQ
  |}.
