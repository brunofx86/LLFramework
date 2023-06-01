Require Import LL.Framework.SL.FLL.Specifications.Bipoles. 

 
(** ** Syntax *)
Inductive LMCon := TT | FF.
Inductive LMBin := OR | AND | IMP .
Inductive LMQu := EX | ALL .

#[export]Instance LMSyntax : OLSyntax:=
  {|
    OLType := nat;
    ccon := LMCon;
    ucon := Empty_set;
    bcon := LMBin;
    qcon := Empty_set
  |}.

(** ** Inference rules *)

(** *** Constants *)
Definition LMrulesC (c:ccon) :=
  match c return ruleC with
 | TT => {| rc_rgtBody := Top;
                  rc_lftBody  := Zero |}
 | FF => {| rc_rgtBody := Zero;
                  rc_lftBody  := Top |}
  
  end.


(** *** Unary connectives *)
Definition LMrulesU  (c:ucon) :=
  match c return ruleU with
  end.

(** *** Binary connectives *)
Definition LMrulesB (c :bcon) :=
  match c with
  | OR => {| rb_rgtBody := fun F G => AOr  (Bang (atom (up F))) (Bang (atom (up G) ));
                 rb_lftBody  := fun F G => AAnd (atom (down F) ) (atom (down G)) |}
  | AND => {| rb_rgtBody := fun F G => AAnd  (Bang (atom (up F))) (Bang (atom (up G) ));
                 rb_lftBody  := fun F G => AOr (atom (down F) ) (atom (down G)) |}
  | IMP => {| rb_rgtBody := fun F G => MOr (atom (down F)) (Bang (atom (up G)) );
                 rb_lftBody  := fun F G => MAnd (Bang (atom (up F)) ) (atom (down G)) |}
  end.


(** *** Quantifiers *)
Definition LMrulesQ (c :qcon) :=
  match c return ruleQ with
 (*  | EX => {| rq_rgtBody := fun FX => Some (fun x => atom (up (FX x)));
                 rq_lftBody  := fun FX => All (fun x => atom (down (FX x)))  |}
  | ALL => {| rq_rgtBody := fun FX => Some (fun x => atom (up (FX x))) ;
              rq_lftBody  := fun FX => All (fun x => atom (down (FX x))) |}
  *) end.

#[export] Instance LMRules : OORules :=
  {|
    rulesC := LMrulesC;
    rulesU := LMrulesU ;
    rulesB := LMrulesB;
    rulesQ := LMrulesQ
  |}.
