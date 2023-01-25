Require Import LL.SL.FLL.Specifications.Bipoles. 

 
(** ** Syntax *)
Inductive LKCon := TT | FF.
Inductive LKBin := AND | OR | IMP .
Inductive LKQu := EX | ALL .

#[export]Instance LKSyntax : OLSyntax:=
  {|
    OLType := nat;
    ccon := LKCon;
    ucon := Empty_set;
    bcon := LKBin;
    qcon := Empty_set
  |}.

(** ** Inference rules *)

(** *** Constants *)
Definition LKrulesC (c:ccon) :=
  match c return ruleC with
 | TT => {| rc_rgtBody := Top;
                  rc_lftBody  := Zero |}
 | FF => {| rc_rgtBody := Zero;
                  rc_lftBody  := Top |}
  
  end.


(** *** Unary connectives *)
Definition LKrulesU  (c:ucon) :=
  match c return ruleU with
  end.

(** *** Binary connectives *)
Definition LKrulesB (c :bcon) :=
  match c with
  | AND => {| rb_rgtBody := fun F G => AAnd  (atom (up F)) (atom (up G) );
                 rb_lftBody  := fun F G => AOr (atom (down F) ) (atom (down G)) |}
  | OR => {| rb_rgtBody := fun F G => AOr  (atom (up F)) (atom (up G) );
              rb_lftBody  := fun F G => AAnd  (atom (down F) ) (atom (down G)) |}
  | IMP => {| rb_rgtBody := fun F G => MOr (atom (down F)) (atom (up G) );
                 rb_lftBody  := fun F G =>MAnd (atom (up F) ) (atom (down G)) |}
  end.

(** *** Quantifiers *)
Definition LKrulesQ (c :qcon) :=
  match c return ruleQ with
 (*  | EX => {| rq_rgtBody := fun FX => Some (fun x => atom (up (FX x)));
                 rq_lftBody  := fun FX => All (fun x => atom (down (FX x)))  |}
  | ALL => {| rq_rgtBody := fun FX => Some (fun x => atom (up (FX x))) ;
              rq_lftBody  := fun FX => All (fun x => atom (down (FX x))) |}
  *) end.

#[export] Instance LKRules : OORules :=
  {|
    rulesC := LKrulesC;
    rulesU := LKrulesU ;
    rulesB := LKrulesB;
    rulesQ := LKrulesQ
  |}.
