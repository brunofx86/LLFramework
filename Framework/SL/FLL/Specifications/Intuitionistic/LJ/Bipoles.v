Require Import LL.Framework.SL.FLL.Specifications.Bipoles. 

 
(** ** Syntax *)
Inductive LJCon := TT | FF.
Inductive LJBin := OR | AND | IMP .
Inductive LJQu := EX | ALL .

#[export]Instance LJSyntax : OLSyntax:=
  {|
    OLType := nat;
    ccon := LJCon;
    ucon := Empty_set;
    bcon := LJBin;
    qcon := Empty_set
  |}.

(** ** Inference rules *)

(** *** Constants *)
Definition LJrulesC (c:ccon) :=
  match c return ruleC with
 | TT => {| rc_rgtBody := Top;
                  rc_lftBody  := Zero |}
 | FF => {| rc_rgtBody := Zero;
                  rc_lftBody  := Top |}
  
  end.


(** *** Unary connectives *)
Definition LJrulesU  (c:ucon) :=
  match c return ruleU with
  end.

(** *** Binary connectives *)
Definition LJrulesB (c :bcon) :=
  match c with
  | OR => {| rb_rgtBody := fun F G => AOr  (Bang (atom (up F))) (Bang (atom (up G) ));
                 rb_lftBody  := fun F G => AAnd (atom (down F) ) (atom (down G)) |}
  | AND => {| rb_rgtBody := fun F G => AAnd  (Bang (atom (up F))) (Bang (atom (up G) ));
                 rb_lftBody  := fun F G => AOr (atom (down F) ) (atom (down G)) |}
  | IMP => {| rb_rgtBody := fun F G => MOr (atom (down F)) (Bang (atom (up G)) );
                 rb_lftBody  := fun F G => MAnd (Bang (atom (up F)) ) (atom (down G)) |}
  end.


(** *** Quantifiers *)
Definition LJrulesQ (c :qcon) :=
  match c return ruleQ with
 (*  | EX => {| rq_rgtBody := fun FX => Some (fun x => atom (up (FX x)));
                 rq_lftBody  := fun FX => All (fun x => atom (down (FX x)))  |}
  | ALL => {| rq_rgtBody := fun FX => Some (fun x => atom (up (FX x))) ;
              rq_lftBody  := fun FX => All (fun x => atom (down (FX x))) |}
  *) end.

#[export] Instance LJRules : OORules :=
  {|
    rulesC := LJrulesC;
    rulesU := LJrulesU ;
    rulesB := LJrulesB;
    rulesQ := LJrulesQ
  |}.
