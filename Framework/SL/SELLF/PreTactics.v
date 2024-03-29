  (** * Tactics for the focused system

The tactics defined in this module solves some of the repetitive goals
generated when the system is used. In particular those related
   to well-formedness conditions on formulas
 *)
Require Export LL.Misc.Utils.
Require Export LL.Framework.SL.SELLF.Sequent.
Require Import LL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(* Section FLL. *)

(** Solves some efficiency problems related to rewriting with setoids *)
(* Remove Hints Equivalence.pointwise_equivalence : typeclass_instances. *)
#[global] Existing Instance Equivalence.pointwise_equivalence | 11.


Ltac solveIsFormula1 := auto;try
  match goal with
(*   | [ H1: isFormulaL (second ?L), H2: In (_,?P) ?L  |- isFormula ?P ] => apply isFormulaInS1 in H2;auto
 *) (*  | [ H1: isFormulaL (second ?L), H2: In (_,_ ?A _) ?L  |- isFormula ?A ] => apply isFormulaInS1 in H2;solveIsFormula1
  | [ H1: isFormulaL (second ?L), H2: In (_,_ _ ?A) ?L  |- isFormula ?A ] => apply isFormulaInS1 in H2;solveIsFormula1
  | [ H1: isFormulaL (second ?L), H2: In (_,_ ?A) ?L  |- isFormula (?A _) ] => apply isFormulaInS1 in H2;solveIsFormula1
  *)
 (*  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,?P)::_)  |- isFormula ?P ] => apply isFormulaInS2 in H2;auto
  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ ?A _)::_)  |- isFormula ?A ] => apply isFormulaInS2 in H2;solveIsFormula1
  *)(*  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ _ ?A)::_)  |- isFormula ?A ] => apply isFormulaInS2 in H2;solveIsFormula1
  *)(*  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ ?A)::_)  |- isFormula (?A _) ] => apply isFormulaInS2 in H2;solveIsFormula1
 *)
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th ?P  |- isFormula ?P ] => apply H1 in H2;auto
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ ?A _)  |- isFormula ?A ] => apply H1 in H2;solveIsFormula1
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ _ ?A)  |- isFormula ?A ] => apply H1 in H2;solveIsFormula1
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ ?A)  |- isFormula (?A _) ] => apply H1 in H2;solveIsFormula1
 
  | [ H: isFormula (_ ?A _) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormula (_ _ ?A) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormula (_ ?A) |- isFormula (?A _) ] => inversion H;subst;eauto
  
  | [ H: isFormulaL ((_ ?A _)::_) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormulaL ((_ _ ?A)::_) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormulaL ((_ ?A)::_) |- isFormula (?A _) ] => inversion H;subst;eauto
end.

Ltac solveIsFormula2 := auto;try
  match goal with
  | [  |- isFormulaL (second (getU _)) ] => try solve [apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (getL _)) ] => try solve [apply isFormulaL_getL;auto]
  
  | [ H1: Permutation (getL ?mBD) (getL ?mB ++ getL ?mD), 
      H2: Permutation (getU ?mBD) (getU ?mD),
      H3: isFormulaL (second ?mBD)
      |- isFormulaL (second ?mD)] => eapply @isFormulaSecondSplit2 with (X:=nil) (Y:=nil) (BD:=mBD) (B:=mB);sauto
  | [ H1: Permutation (getL ?mBD) (getL ?Bm ++ getL ?mD), 
      H2: Permutation (getU ?mBD) (getU ?mB),
      H3: isFormulaL (second ?mBD)
      |- isFormulaL (second ?mB)] => eapply @isFormulaSecondSplit1 with (X:=nil) (Y:=nil) (BD:=mBD) (D:=mD);sauto
end.


Ltac SLFormulaSolve := auto; try solve[solveIsFormula1];
match goal with
 | [ |- isFormulaL ?K] => simpl;isFormula;solveIsFormula1
end.

Ltac SLSolve := try
 match goal with
 | |- isFormulaL (second ?K) => solveIsFormula2;SLFormulaSolve
 | |- isFormulaL ?K => SLFormulaSolve
    end.
 
Ltac solveUniform :=
  auto;
  repeat 
    match goal with
    | [|- uniform_oo _] =>  constructor 
    | [|- uniform _ ] => eauto 10  using uniform_id, uniform_con, uniform_app, proper_uniform, abstr_lambda
    | [|- uniform_atm _ ] => constructor
    | [|- proper _ ] => constructor
    | [|- level _ _ ] => constructor
    end.

Ltac clearPolarity :=
 repeat
 match goal with
 | [H: negFormula Top  |- _] => clear H
 | [H: negFormula Bot  |- _] => clear H
 | [H: negFormula (MOr _ _)  |- _] => clear H
 | [H: negFormula (atom _)  |- _] => clear H
 | [H: negFormula (All _)  |- _] => clear H
 | [H: negFormula (AAnd _ _)  |- _] => clear H
 | [H: negFormula (Quest _)  |- _] => clear H
 
 | [H: posFormula (perp _)  |- _] => clear H
 | [H: posFormula Zero  |- _] => clear H
 | [H: posFormula One  |- _] => clear H
 | [H: posFormula (MAnd _ _)  |- _] => clear H
 | [H: posFormula (Some _)  |- _] => clear H
 | [H: posFormula (AOr _ _)  |- _] => clear H
 | [H: posFormula (Bang _ )  |- _] => clear H 

 | [H: posLFormula (atom _)  |- _] => clear H
 | [H: posLFormula (perp _)  |- _] => clear H
 | [H: posLFormula Zero  |- _] => clear H
 | [H: posLFormula One  |- _] => clear H
 | [H: posLFormula (MAnd _ _)  |- _] => clear H
 | [H: posLFormula (Some _)  |- _] => clear H
 | [H: posLFormula (AOr _ _)  |- _] => clear H
 | [H: posLFormula (Bang _ )  |- _] => clear H 

 | [H : ~ posAtom (perp _ ) |- _ ] => clear H 
 | [H : ~ posAtom (MOr _ _ ) |- _ ] => clear H 
 | [H : ~ posAtom (MAnd _ _) |- _ ] => clear H   
 | [H : ~ posAtom (AAnd _ _ ) |- _ ] => clear H 
 | [H : ~ posAtom (AOr _ _) |- _ ] => clear H 
 | [H : ~ posAtom (Bang _ ) |- _ ] => clear H    
 | [H : ~ posAtom (Quest _ ) |- _ ] => clear H 
 | [H : ~ posAtom (All _ ) |- _ ] => clear H 
 | [H : ~ posAtom (Some _ ) |- _ ] => clear H 
 | [H : ~ posAtom Top |- _ ] => clear H    
 | [H : ~ posAtom Bot |- _ ] => clear H 
 | [H : ~ posAtom One |- _ ] => clear H 
 | [H : ~ posAtom Zero |- _ ] => clear H  
 end.
      
(** Proving goals about polarity *)

Ltac solvePolarity :=
  sauto;
  let H := fresh "H" in
    match goal with
    | [|- ~ negFormula _] => intro H; solvePolarity 
    | [|- ~ posFormula _] => intro H; solvePolarity
    | [|- ~ posLFormula _] => intro H; solvePolarity
    | [|- ~ posAtom _ ] => intro H; solvePolarity
    | [|- ~ negAtom _ ] => intro H; solvePolarity
    
    | [H: negFormula ?F  |- _] =>
      match F with
      | perp _ => inversion H      
      | MAnd _ _ => inversion H
      | AOr _ _ => inversion H
      | Some _ => inversion H
      | Bang _ => inversion H
      | Zero => inversion H
      | One => inversion H
      end
    | [H : posFormula ?F |- _ ] =>
      match F with
      | atom _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H      
      | All _ => inversion H
      | Quest _ => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : posLFormula ?F |- _ ] =>
      match F with
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | All _ => inversion H
      | Quest _ => inversion H
      | Bot => inversion H
      | Top => inversion H
    end
    | [H : posAtom ?F |- _ ] =>
      match F with
      | MAnd _ _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | AOr _ _ => inversion H
      | Bang _ => inversion H
      | Quest _ => inversion H
      | perp _ => inversion H
      | Some _ => inversion H
      | All _ => inversion H
      | Zero => inversion H
      | One => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : negAtom ?F |- _ ] =>
      match F with
      | MAnd _ _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | AOr _ _ => inversion H
      | Bang _ => inversion H
      | Quest _ => inversion H
      | atom _ => inversion H
      | Some _ => inversion H
      | All _ => inversion H
      | Zero => inversion H
      | One => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : ~ posAtom _ |- _ ] => try solve[contradict H;auto]
    | [H : ~ posLFormula _ |- _ ] => try solve[contradict H;auto]
    | [H : ~ posFormula _ |- _ ] => try solve[contradict H;auto]
     | [H : ~ negFormula _ |- _ ] => try solve[contradict H;auto] 
    | _  => idtac
    end;auto.
 
   
Ltac cleanF :=
 repeat
 match goal with
  | [H: negFormula Top  |- _] => clear H
 | [H: negFormula Bot  |- _] => clear H
 | [H: negFormula (MOr _ _)  |- _] => clear H
 | [H: negFormula (atom _)  |- _] => clear H
 | [H: negFormula (All _)  |- _] => clear H
 | [H: negFormula (AAnd _ _)  |- _] => clear H
 | [H: negFormula (Quest _ _)  |- _] => clear H
 
 | [H: posFormula (perp _)  |- _] => clear H
 | [H: posFormula Zero  |- _] => clear H
 | [H: posFormula One  |- _] => clear H
 | [H: posFormula (MAnd _ _)  |- _] => clear H
 | [H: posFormula (Some _)  |- _] => clear H
 | [H: posFormula (AOr _ _)  |- _] => clear H
 | [H: posFormula (Bang _ _ )  |- _] => clear H 

 | [H: posLFormula (atom _)  |- _] => clear H
 | [H: posLFormula (perp _)  |- _] => clear H
 | [H: posLFormula Zero  |- _] => clear H
 | [H: posLFormula One  |- _] => clear H
 | [H: posLFormula (MAnd _ _)  |- _] => clear H
 | [H: posLFormula (Some _)  |- _] => clear H
 | [H: posLFormula (AOr _ _)  |- _] => clear H
 | [H: posLFormula (Bang _ _)  |- _] => clear H 
 
 
 | [H : ~ posAtom (perp _ ) |- _ ] => clear H 
 | [H : ~ posAtom (MOr _ _ ) |- _ ] => clear H 
 | [H : ~ posAtom (MAnd _ _) |- _ ] => clear H   
 | [H : ~ posAtom (AAnd _ _ ) |- _ ] => clear H 
 | [H : ~ posAtom (AOr _ _) |- _ ] => clear H 
 | [H : ~ posAtom (Bang _ _) |- _ ] => clear H    
 | [H : ~ posAtom (Quest _ _) |- _ ] => clear H 
 | [H : ~ posAtom (All _ ) |- _ ] => clear H 
 | [H : ~ posAtom (Some _ ) |- _ ] => clear H 
 | [H : ~ posAtom Top |- _ ] => clear H    
 | [H : ~ posAtom Bot |- _ ] => clear H 
 | [H : ~ posAtom One |- _ ] => clear H 
 | [H : ~ posAtom Zero |- _ ] => clear H  
    
    | [H : SetU [] |- _ ] => clear H
    | [H : SetL [] |- _ ] => clear H   
  | [H : LtX ?a [] |- _ ] => clear H
  | [H : lt ?a ?a |- _ ] => clear H
  
 end.
 
(** This tactic solves most of the irrelevant goals in a focused
  proof (e.g., proving whether a formula is positive or not) *)
Ltac solveF :=
  sauto;
  let H := fresh "H" in
    match goal with
    | [|- ~ negFormula _] => intro H; solveF 
    | [|- ~ posFormula _] => intro H; solveF
    | [|- ~ posLFormula _] => intro H; solveF
    | [|- ~ posAtom _ ] => intro H; solveF
    | [|- ~ negAtom _ ] => intro H; solveF
    
    | [H: negFormula ?F  |- _] =>
      match F with
      | perp _ => inversion H      
      | MAnd _ _ => inversion H
      | AOr _ _ => inversion H
      | Some _ => inversion H
      | Bang _ _ => inversion H
      | Zero => inversion H
      | One => inversion H
      end
    | [H : posFormula ?F |- _ ] =>
      match F with
      | atom _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H      
      | All _ => inversion H
      | Quest _ _ => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : posLFormula ?F |- _ ] =>
      match F with
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | All _ => inversion H
      | Quest _ _ => inversion H
      | Bot => inversion H
      | Top => inversion H
    end
    | [H : posAtom ?F |- _ ] =>
      match F with
      | MAnd _ _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | AOr _ _ => inversion H
      | Bang _ => inversion H
      | Quest _ _ => inversion H
      | perp _ => inversion H
      | Some _ => inversion H
      | All _ => inversion H
      | Zero => inversion H
      | One => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : negAtom ?F |- _ ] =>
      match F with
      | MAnd _ _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | AOr _ _ => inversion H
      | Bang _ _ => inversion H
      | Quest _ _ => inversion H
      | atom _ => inversion H
      | Some _ => inversion H
      | All _ => inversion H
      | Zero => inversion H
      | One => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : ~ posAtom (atom _ ) |- _ ] => contradict H;auto
    | [H : ~ posLFormula (atom _ ) |- _ ] => contradict H;auto
    | [H : ~ posLFormula (perp _ ) |- _ ] => contradict H;auto
  
    | _  => idtac
    end;auto.

(** Splits the linear context L into L1 ++ L2 where L1 contains the first n elements of L *)
Ltac SplitContext n :=
  match goal with
  | [ |- SELLN _ _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.

Ltac SplitContext' n :=
  match goal with
  | [ |- SELLS _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.


(** Notation for forward reasoning on  sequents *)

(* Focusing on positive formulas *)
Tactic Notation "LFocus" := match goal with
    | [ |- SELLS _ _ (?P::?PL) _ ] =>  eapply @tri_dec1' with (F:= P) (L':=PL);[solveF | sauto | sauto ]
    | [|- SELLN _ _ _ (?P::?PL) _] => eapply @tri_dec1 with (F:= P) (L':=PL);[solveF | sauto | sauto ]
end.

Tactic Notation "LFocus"  constr(R) := match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R);[solveF | sauto | sauto ]
    | [|- SELLN _ _ _ _ _] => eapply @tri_dec1 with (F:= R);[solveF | sauto | sauto]
end.

Tactic Notation "LFocus"  constr(R) constr(T) := match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R) (L':=T);[solveF | sauto | sauto ]
    | [|- SELLN _ _ _ _ _] => eapply @tri_dec1 with (F:= R) (L':=T);[solveF | sauto | sauto]
end.

(* Focusing on unbounded formulas *)
Tactic Notation "UFocus" := match goal with
    | [ |- SELLS _ ((?a,?P)::_) _ _ ] =>  eapply @tri_dec2u' with (F:= P) (i:=a);[sauto |  solveF | sauto | sauto ]
    | [|- SELLN _ _ ((?a,?P)::_) _ _] => eapply @tri_dec2u with (F:= P) (i:=a);[sauto  | solveF | sauto | sauto ]
end.
                                                                     
Tactic Notation "UFocus"  constr(a) constr(S) := match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_dec2u' with (F:= S) (i:=a);[sauto | solveF | sauto | sauto ]
    | [|- SELLN _ _ _ _ _] => eapply @tri_dec2u with (F:= S) (i:=a);[sauto | solveF | sauto | sauto ]
end.

(* Focusing on bounded formulas *)
Tactic Notation "BFocus" := match goal with
    | [ |- SELLS _ ((?a,?P)::_) _ _ ] =>  eapply @tri_dec2l' with (F:= P) (i:=a);[sauto |  solveF | sauto | sauto ]
    | [|- SELLN _ _ ((?a,?P)::_) _ _] => eapply @tri_dec2l with (F:= P) (i:=a);[sauto | solveF | sauto | sauto ]
end.

Tactic Notation "BFocus"  constr(a) constr(S) := match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_dec2l' with (F:= S) (i:=a);[sauto | solveF | sauto | sauto ]
    | [|- SELLN _ _ _ _ _] => eapply @tri_dec2l with (F:= S) (i:=a);[sauto | solveF | sauto | sauto ]
end.
                                                                     
Tactic Notation "BFocus"  constr(a) constr(S) constr(T):= match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_dec2l' with (F:= S) (i:=a) (B':= T);[sauto |  solveF | sauto | sauto ]
    | [|- SELLN _ _ _ _ _] => eapply @tri_dec2l with (F:= S) (i:=a) (B':= T);[sauto | solveF | sauto | sauto ]
end.

(* Focusing on formulas in theory *)
Tactic Notation "TFocus"  constr(S) := match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_dec3' with (F:= S);[sauto | solveF | sauto]
    | [|- SELLN _ _ _ _ _] => eapply @tri_dec3 with (F:= S);[ sauto | solveF | sauto]
end.

(* Multiplicative conjuction with bounded formulas *)
Tactic Notation "LLTensor"  constr(Ctx1) constr(Ctx2) constr(Ctx3) constr(Ctx4) constr(Ctx5) := match goal with
                                                       | [ |- SELLS _ _ _ _ ] =>  eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2) (B:=Ctx3) (C:=Ctx4) (D:=Ctx5);solveF
                                                       | [|- SELLN _ _ _ _ _] => eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2) (B:=Ctx3) (C:=Ctx4) (D:=Ctx5);solveF
                                                       end.


(* Multiplicative conjuction with no bounded formulas *)
 Tactic Notation "LLTensor"  constr(Ctx1) constr(Ctx2) := match goal with
               | [ |- SELLS _ ?X _ _ ] =>  eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2) (B:=X)(C:=nil) (D:=nil);solveF
               | [|- SELLN _ _ ?X _ _] => eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2) (B:=X) (C:=nil) (D:=nil);solveF
                 end. 

Tactic Notation "LLTensor"  := match goal with
               | [ |- SELLS _ ?X [] _ ] =>  eapply @tri_tensor' with (M:=nil) (N:=nil) (B:=X)  (C:=nil) (D:=nil);solveF
               | [|- SELLN _ _ ?X [] _] => eapply @tri_tensor with (M:=nil) (N:=nil) (B:=X) (C:=nil) (D:=nil);solveF
                 end.

Lemma allSeTLEmpty (OLS: OLSig) (SE: SigSELL) (SI: USigSELL) (B : list location) : getL B = (@nil location).
Proof with auto.
 rewrite (SetU_then_empty _ );auto.
Qed.

Lemma permSeTL (OLS: OLSig)(SE: SigSELL) (SI: USigSELL)  (B : list location) : Permutation (getL B) (getL B ++ getL B).
Proof with auto.
 erewrite allSeTLEmpty...
Qed.


Global Hint Resolve  permSeTL : core. 

 Lemma tensorU (OLS: OLSig) (SE: SigSELL) (SIU: USigSELL) n th B MN M N F G:          
  Permutation MN (M ++ N) ->
  SELLN th n B M (DW F) ->
  SELLN th n B N (DW G) -> SELLN th (S n) B MN (DW (MAnd F  G)).
  Proof.   
  intros.
  LLTensor M N.
  Qed.

 Lemma tensorU' (OLS: OLSig) (SI : SigSELL) (SIU : USigSELL) th B MN M N F G:    SetU B ->    
  Permutation MN (M ++ N) ->
  SELLS th B M (DW F) ->
  SELLS th B N (DW G) -> SELLS th B MN (DW (MAnd F G)).
  Proof.   
  intros.
  LLTensor M N.
  Qed.

(* Additive conjuction *)
Tactic Notation "LLWith" := match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_with';sauto
    | [|- SELLN _ _ _ _ _] => eapply @tri_with;sauto
end.

(* Additive disjuction *)
Tactic Notation "LLPlusL" := match goal with
                           | [ |- SELLS _ _ _ _ ] =>   apply tri_plus1';sauto
                           | [|- SELLN _ _ _ _ _] =>  apply tri_plus1;sauto
                            end.

Tactic Notation "LLPlusR" := match goal with
   | [ |- SELLS _ _ _ _ ] =>   apply tri_plus2';sauto
   | [|- SELLN _ _ _ _ _] =>  apply tri_plus2;sauto
end.

(* Multiplicative disjuction *)
Tactic Notation "LLPar" := match goal with
                         | [ |- SELLS _ _ _ _ ] =>  apply tri_par';sauto
                         | [|- SELLN _ _ _ _ _] => apply tri_par;sauto
                         end.

(* Quantifiers *)
Tactic Notation "LLExists" constr(tt) :=  match goal with
   | [ |- SELLS _ _ _ _ ] => eapply @tri_ex' with (t:=tt);try solveUniform;sauto
   | [|- SELLN _ _ _ _ _] => eapply @tri_ex with (t:=tt);try solveUniform;sauto
end.

Tactic Notation "LLForall" := match goal with
   | [ |- SELLS _ _ _ _ ] => eapply @tri_fx'; intros;sauto
   | [|- SELLN _ _ _ _ _] => eapply @tri_fx; intros;sauto
end.

(* Storing formulas *)
Tactic Notation "LLStore" := match goal with
       | [ |- SELLS _ _ _ _ ] =>  apply tri_store';[solveF | auto]
       | [|- SELLN _ _ _ _ _] => apply tri_store;[solveF | auto]
                           end. 

Tactic Notation "LLStoreC" := match goal with
       | [ |- SELLS _ _ _ _ ] =>  apply tri_quest';sauto
       | [|- SELLN _ _ _ _ _] => apply tri_quest;sauto
                           end.

(* Changing to the negative phase *)
Tactic Notation "LLRelease" := match goal with
                         | [ |- SELLS _ _ _ _ ] =>  apply tri_rel';[solveF | auto]
                         | [|- SELLN _ _ _ _ _] => apply tri_rel;[solveF | auto]
                         end. 

(* Axioms *)   
Tactic Notation "init1"  := match goal with
     | [ |- SELLS _ _ _ _ ] =>  apply tri_init1';try SLSolve;auto
     | [|- SELLN _ _ _ _ _] => apply tri_init1;try SLSolve;auto
                          end.

Tactic Notation "init2" constr(a) constr(b) := match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_init2' with (i:=a) (C:=b);[try SLSolve | try perm ];auto
    | [|- SELLN _ _ _ _ _] => eapply @tri_init2 with (i:=a) (C:=b);[try SLSolve  | try perm ];auto
                          end.

Tactic Notation "init2" constr(a) := match goal with
    | [ |- SELLS _ _ _ _ ] =>  eapply @tri_init2' with (i:=a)
   | [|- SELLN _ _ _ _ _] => eapply @tri_init2 with (i:=a) 
                          end.
                          
Tactic Notation "init2" := match goal with
     | [ |- SELLS _ _ _ _ ] =>  eapply @tri_init2'
    | [|- SELLN _ _ _ _ _] => eapply @tri_init2
                          end.

Tactic Notation "LLOne"  := match goal with
                          | [ |- SELLS _ _ _ _ ] =>  apply tri_one';SLSolve
                          | [|- SELLN _ _ _ _ _] => apply tri_one;SLSolve
                          end.

Tactic Notation "LLTop"  := match goal with
                          | [ |- SELLS _ _ _ _ ] =>  apply tri_top'
                          | [|- SELLN _ _ _ _ _] => apply tri_top
                          end.

(* Others rules *)
Tactic Notation "LLBot"  := match goal with
                          | [ |- SELLS _ _ _ _ ] =>  apply tri_bot';sauto
                          | [|- SELLN _ _ _ _ _] => apply tri_bot;sauto
                          end.
                          
                         
Tactic Notation "LLBang"  := match goal with
                          | [ |- SELLS _ _ _ _ ] =>  apply tri_bang';sauto
                          | [|- SELLN _ _ _ _ _] => apply tri_bang;sauto
                          end.

(** This tactic applies as many positive/negative rules as
  possible. Connectives as exists and tensor are not automatically
  introduced (due to the decision on the contexts/terms ) *)
  
   Ltac negativePhaseReasoning :=
  try match goal with  
  | [ |- SELLS _ _ _ (UP  ((AAnd _ _)::_))] => LLWith 
  | [ |- SELLS _ _ _ (UP ((MOr ?F ?G)::_))] => LLPar
  | [ |- SELLS _ _ _ (UP ((Quest ?i) ?F :: _))] => LLStoreC
  | [ |- SELLS _ _ _ (UP (Bot :: _))] => LLBot
  | [ |- SELLS _ _ _ (UP ( (All _) :: _)) ] => let x:= fresh "x" in
                                              let xp := fresh "properX" in
                                              apply tri_fx' ; try solveUniform ; intros x xp

 (* Storing formulas *)
  | [H: posLFormula ?F |- SELLS _ _ _ (UP (?F :: ?M))] => LLStore
    | [|- SELLS _ _ _ (UP  (?F::_))] =>
      match F with
      | AOr _ _ => LLStore
      | MAnd _ _  => LLStore
      | Some _ =>LLStore
      | (atom _)  => LLStore
      | (perp _)  => LLStore
      | One  => LLStore
      | Zero => LLStore
      end
    end.

  Ltac negativePhaseReasoningN :=
  try match goal with  
  | [ |- SELLN _ _ _ _ (UP  ((AAnd _ _)::_))] => LLWith 
  | [ |- SELLN _ _ _ _ (UP ((MOr ?F ?G)::_))] => LLPar
  | [ |- SELLN _ _ _ _ (UP ((Quest ?i) ?F :: _))] => LLStoreC
  | [ |- SELLN _ _ _ _ (UP (Bot :: _))] => LLBot
  | [ |- SELLN _ _ _ _ (UP ( (All _) :: _)) ] => let x:= fresh "x" in
                                              let xp := fresh "properX" in
                                              apply tri_fx' ; try solveUniform ; intros x xp

 (* Storing formulas *)
  | [H: posLFormula ?F |- SELLN _ _ _ _ (UP (?F :: ?M))] => LLStore
    | [|- SELLN _ _ _ _ (UP  (?F::_))] =>
      match F with
      | AOr _ _ => LLStore
      | MAnd _ _  => LLStore
      | Some _ =>LLStore
      | (atom _)  => LLStore
      | (perp _)  => LLStore
      | One  => LLStore
      | Zero => LLStore
      end
    end.

  Ltac positivePhaseReasoning :=
  try match goal with  
  | [USI : USigSELL |- SELLS _ _ [] (DW  (MAnd _ _))] => LLTensor (@nil oo)  (@nil oo) 
  | [H: SELLS ?th ?B ?L (DW ?F) |- SELLS ?th ?B ?L (DW (AOr ?F ?G))] => LLPlusL 
  | [H: SELLS ?th ?B ?L (DW ?G) |- SELLS ?th ?B ?L (DW (AOr ?F ?G))] => LLPlusR 
  | [ |- SELLS _ _ _ (DW (Bang _ _))] => apply tri_bang';negativePhaseReasoning
 
     (* Change of polarity *)
    | [H: negFormula ?F |- SELLS _ _ _ (DW  ?F)] => LLRelease;negativePhaseReasoning
    | [|- SELLS _ _ _ (DW  ?F)] =>
      match F with
      | MOr _ _ => LLRelease;negativePhaseReasoning
      | All _ =>LLRelease;negativePhaseReasoning
      | Bot  => LLRelease;negativePhaseReasoning
      | (atom _)  => LLRelease;negativePhaseReasoning
      | Top  => LLRelease;negativePhaseReasoning
      | AAnd _ _  => LLRelease;negativePhaseReasoning
      | Quest _ _ => LLRelease;negativePhaseReasoning
      end
    end.
 
  Ltac positivePhaseReasoningN :=
  try match goal with  
  | [USI : USigSELL |- SELLN _ _ _ [] (DW  (MAnd _ _))] => LLTensor (@nil oo)  (@nil oo) 
  | [H : SetU ?B |- SELLN _ _ ?B [] (DW  (MAnd _ _))] => LLTensor (@nil oo)  (@nil oo) 

  | [H: SELLN _ ?th ?B ?L (DW ?F) |- SELLN _ ?th ?B ?L (DW (AOr ?F ?G))] => LLPlusL 
  | [H: SELLN _ ?th ?B ?L (DW ?G) |- SELLN _ ?th ?B ?L (DW (AOr ?F ?G))] => LLPlusR 
  | [ |- SELLN _ _ _ _ (DW (Bang _ _))] => apply tri_bang;negativePhaseReasoningN
 
     (* Change of polarity *)
    | [H: negFormula ?F |- SELLN _ _ _ _ (DW  ?F)] => LLRelease;negativePhaseReasoningN
    | [|- SELLN _ _ _ _ (DW  ?F)] =>
      match F with
      | MOr _ _ => LLRelease;negativePhaseReasoningN
      | All _ =>LLRelease;negativePhaseReasoningN
      | Bot  => LLRelease;negativePhaseReasoningN
      | (atom _)  => LLRelease;negativePhaseReasoningN
      | Top  => LLRelease;negativePhaseReasoningN
      | AAnd _ _  => LLRelease;negativePhaseReasoningN
      | Quest _ _ => LLRelease;negativePhaseReasoningN
      end
    end.
 
 
 
Lemma init2Cut (OLS : OLSig) (SI:SigSELL) i A L th :
SetU L -> 
In (i,atom A) L -> SELLS th L [] (DW (perp A)).
 Proof with sauto.
 intros.
 apply InPermutation in H0...
 rewrite H0 in H. 
 init2 i x. inversion H...
 Qed.

  Ltac solveAxioms :=
  try
    match goal with
   | [H: SELLS _ _ _ (DW Zero) |- _ ] => inversion H;subst;solveF
   | [ |- SELLS _ _ _ (DW One) ] => LLOne
   | [ |- SELLS _ _ [One] (UP [])] => LFocus;solveAxioms   
   | [ |- SELLS _ _ [] (UP [One]) ] => LLStore;LFocus;solveAxioms
  
   | [ |- SELLS _ _ [Top] (UP [])] => LFocus;LLRelease;solveAxioms   
   | [ |- SELLS _ _ _ (UP (Top :: ?M))] => LLTop
  (* initial rules *)
   | [ |- SELLS _ _ [atom ?A] (DW (perp ?A))] => init1
   | [ |- SELLS _ _ [perp ?A; atom ?A] (UP [])] => LFocus;solveAxioms   
   | [ |- SELLS _ _ [atom ?A; perp ?A] (UP [])] => LFocus (perp A) [atom A];solveAxioms   

   | [ |- SELLS _ ((?a,atom ?A)::?B) [] (DW (perp ?A))] => init2 a B
    | [ |- SELLS _ (?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => init2 a B
    | [  |- SELLS _ (?X::?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => init2 a (X::B)
    | [  |- SELLS _ (?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => init2 a (B++E)   
    | [  |- SELLS _ (?X::?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => init2 a (X::B++E)   
  
    | [ H: Permutation ((?a,atom _)::?B) ?D |- SELLS  _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation (?B++[(?a,atom ?A)]) ?D |- SELLS _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation (?B++(?a,atom ?A)::?E) ?D |- SELLS _ ?D [] (DW (perp ?A))] => init2 a (B++E)

    | [ H: Permutation ?D ((?a,atom ?A)::?B)  |- SELLS _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation ?D (?B++[(?a,atom ?A)])  |- SELLS _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation ?D (?B++(?a,atom ?A)::?E)  |- SELLS _ ?D [] (DW (perp ?A))] => init2 a (B++E)
 
    | [ H: SetU ?L,  HIn: In (?i,atom ?A) ?L |- SELLS _ ?L [] (DW (perp ?A))] =>  try solve [refine (init2Cut i _ _ _ _ _);auto]
  
  end.

 Ltac solveAxiomsN :=
  try
    match goal with
 
   | [ |- SELLN _ _ _ _ (DW One) ] => LLOne
   | [ |- SELLN _ _ _  [One] (UP [])] => LFocus;solveAxiomsN   
   | [ |- SELLN _ _ _ _ (UP (Top :: ?M))] => LLTop
 
     | [H: SELLN _ _ _ _ (DW Zero) |- _ ] => inversion H;subst;solveF

    (* initial rules *)
   | [ |- SELLN _ _ _ [atom ?A] (DW (perp ?A))] => init1
   | [ |- SELLN _ _ _ [perp ?A; atom ?A] (UP [])] => LFocus;solveAxiomsN   
   | [ |- SELLN _ _ _ [atom ?A; perp ?A] (UP [])] => LFocus (perp A) [atom A];solveAxiomsN   

   | [  |- SELLN _ _ ((?a,atom ?A)::?B) [] (DW (perp ?A))] => init2 a B
    | [  |- SELLN _ _ (?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => init2 a B
    | [  |- SELLN _ _ (?X::?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => init2 a (X::B)
    | [  |- SELLN _ _ (?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => init2 a (B++E)   
    | [  |- SELLN _ _ (?X::?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => init2 a (X::B++E)   
  
    | [ H: Permutation ((?a,atom _)::?B) ?D |- SELLN _  _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation (?B++[(?a,atom ?A)]) ?D |- SELLN _ _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation (?B++(?a,atom ?A)::?E) ?D |- SELLN _ _ ?D [] (DW (perp ?A))] => init2 a (B++E)

    | [ H: Permutation ?D ((?a,atom ?A)::?B)  |- SELLN _ _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation ?D (?B++[(?a,atom ?A)])  |- SELLN _ _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation ?D (?B++(?a,atom ?A)::?E)  |- SELLN _ _ ?D [] (DW (perp ?A))] => init2 a (B++E)
 
    | [H: SELLN _ 0 _ _ (UP ( ?F::_)) |- _ ] =>
    match F with
      | Top => idtac
      | _ => inversion H
    end
   
    | [H: SELLN _ 0 _ _ (DW ?F) |- _ ] =>
    match F with
      | One => idtac
      | perp _ => idtac
      | _ => inversion H
    end
 
   end.

 Ltac solvell :=
   match goal with
   | [ |- SELLN _ _ _ _ (UP _) ] =>  negativePhaseReasoningN
   | [ |- SELLN _ _ _ _ (DW _) ] =>  positivePhaseReasoningN
   end;solveAxiomsN.
 
 Ltac solvell' :=
   match goal with
   | [ |- SELLS _ _ _ (UP _) ] =>  negativePhaseReasoning
   | [ |- SELLS _ _ _ (DW _) ] =>  positivePhaseReasoning
   end;solveAxioms.
 
 Ltac solveLL :=
   match goal with
   | [ |- SELLS _ _ _ _ ] =>  solvell'
   | [ |- SELLN _ _ _ _ _ ] =>  solvell
   end;auto.


(** Erasing some of the (unimportant) hypotheses added by the [solveF] and [solveLL] procedures *)

Ltac CleanContext :=
  sauto;cleanF;solveF;sauto.

