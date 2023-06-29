  (** * Tactics for the focused system

The tactics defined in this module solves some of the repetitive goals
generated when the system is used. In particular those related
   to well-formedness conditions on formulas
 *)
Require Export LL.Misc.Utils.
Require Export LL.Framework.SL.MMLL.Sequent.
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

  | [  |- isFormulaL (second (PlusT (getU _))) ] => try solve [apply isFormulaL_PlusT;apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (PlusT (getL _))) ] => try solve [apply isFormulaL_PlusT;apply isFormulaL_getL;auto]
  | [  |- isFormulaL (second (Loc (getU _))) ] => try solve [apply isFormulaL_Loc;apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (Loc (getL _))) ] => try solve [apply isFormulaL_Loc;apply isFormulaL_getL;auto]
  | [  |- isFormulaL (second (PlusT _)) ] => try solve [apply isFormulaL_PlusT;auto]
  | [  |- isFormulaL (second (Loc _)) ] => try solve [apply isFormulaL_Loc;auto]
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


Ltac SLFormulaSolve := auto; try solve[solveIsFormula1]. 

(* ;
match goal with
 | [ |- isFormulaL ?K] => simpl isFormula;solveIsFormula1
end.
 *) 
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

   
Ltac cleanF :=
 repeat
 match goal with
  | [H: UNoDSigMMLL , H: SetU _ |- _] => clear H  
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
    
    | [H : SetK [] |- _ ] => clear H
    | [H : SetK4 [] |- _ ] => clear H
    | [H : SetT [] |- _ ] => clear H
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

(** Cleaning irrelevant hypothesis *)

Ltac clearPolarity :=
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
 | [H: posFormula (Bang _ _)  |- _] => clear H 

 | [H: posLFormula (atom _)  |- _] => clear H
 | [H: posLFormula (perp _)  |- _] => clear H
 | [H: posLFormula Zero  |- _] => clear H
 | [H: posLFormula One  |- _] => clear H
 | [H: posLFormula (MAnd _ _)  |- _] => clear H
 | [H: posLFormula (Some _)  |- _] => clear H
 | [H: posLFormula (AOr _ _)  |- _] => clear H
 | [H: posLFormula (Bang _ _ )  |- _] => clear H 

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
      | Bang _ _ => inversion H
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
    | [H : ~ posAtom _ |- _ ] => try solve[contradict H;auto]
    | [H : ~ posLFormula _ |- _ ] => try solve[contradict H;auto]
    | [H : ~ posFormula _ |- _ ] => try solve[contradict H;auto]
     | [H : ~ negFormula _ |- _ ] => try solve[contradict H;auto] 
    | _  => idtac
    end;auto.

(** Splits the linear context L into L1 ++ L2 where L1 contains the first n elements of L *)
Ltac SplitContext n :=
  match goal with
  | [ |- MLLN _ _ _ ?L _ ] =>
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
  | [ |- MLLS _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.


(** Notation for forward reasoning on  MLLSuents *)

(* Focusing on positive formulas *)
Tactic Notation "LLfocus1" := match goal with
    | [ |- MLLS _ _ (?P::?PL) _ ] =>  eapply @mll_dec1' with (F:= P) (L':=PL);[solveF | sauto | sauto ]
    | [|- MLLN _ _ _ (?P::?PL) _] => eapply @mll_dec1 with (F:= P) (L':=PL);[solveF | sauto | sauto ]
end.

Tactic Notation "LLfocus1"  constr(R) := match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_dec1' with (F:= R);[solveF | sauto | sauto ]
    | [|- MLLN _ _ _ _ _] => eapply @mll_dec1 with (F:= R);[solveF | sauto | sauto]
end.

Tactic Notation "LLfocus1"  constr(R) constr(T) := match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_dec1' with (F:= R) (L':=T);[solveF | sauto | sauto ]
    | [|- MLLN _ _ _ _ _] => eapply @mll_dec1 with (F:= R) (L':=T);[solveF | sauto | sauto]
end.

(* Focusing on unbounded formulas *)
Tactic Notation "LLfocus2" := match goal with
    | [ |- MLLS _ ((?a,?P)::_) _ _ ] =>  eapply @mll_dec2u' with (F:= P) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
    | [|- MLLN _ _ ((?a,?P)::_) _ _] => eapply @mll_dec2u with (F:= P) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
end.
                                                                     
Tactic Notation "LLfocus2"  constr(a) constr(S) := match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_dec2u' with (F:= S) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
    | [|- MLLN _ _ _ _ _] => eapply @mll_dec2u with (F:= S) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
end.

(* Focusing on bounded formulas *)
Tactic Notation "LLfocus3" := match goal with
    | [ |- MLLS _ ((?a,?P)::_) _ _ ] =>  eapply @mll_dec2l' with (F:= P) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
    | [|- MLLN _ _ ((?a,?P)::_) _ _] => eapply @mll_dec2l with (F:= P) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
end.

Tactic Notation "LLfocus3"  constr(a) constr(S) := match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_dec2l' with (F:= S) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
    | [|- MLLN _ _ _ _ _] => eapply @mll_dec2l with (F:= S) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
end.
                                                                     
Tactic Notation "LLfocus3"  constr(a) constr(S) constr(T):= match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_dec2l' with (F:= S) (i:=a) (B':= T);[sauto | sauto | solveF | sauto | sauto ]
    | [|- MLLN _ _ _ _ _] => eapply @mll_dec2l with (F:= S) (i:=a) (B':= T);[sauto | sauto | solveF | sauto | sauto ]
end.

(* Focusing on formulas in theory *)
Tactic Notation "LLtheory"  constr(S) := match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_dec3' with (F:= S);[sauto | solveF | sauto]
    | [|- MLLN _ _ _ _ _] => eapply @mll_dec3 with (F:= S);[ sauto | solveF | sauto]
end.

(* Multiplicative conjuction with bounded formulas *)
Tactic Notation "LLtensor"  constr(Ctx1) constr(Ctx2) constr(Ctx3) constr(Ctx4) constr(Ctx5) := match goal with
                                                       | [ |- MLLS _ _ _ _ ] =>  eapply @mll_tensor' with (M:=Ctx1) (N:=Ctx2) (B:=Ctx3) (C:=Ctx4) (D:=Ctx5);solveF
                                                       | [|- MLLN _ _ _ _ _] => eapply @mll_tensor with (M:=Ctx1) (N:=Ctx2) (B:=Ctx3) (C:=Ctx4) (D:=Ctx5);solveF
                                                       end.


(* Multiplicative conjuction with no bounded formulas *)
Tactic Notation "LLtensor"  constr(Ctx1) constr(Ctx2) := match goal with
               | [ |- MLLS _ ?BC _ _ ] =>  eapply @mll_tensor' with (M:=Ctx1) (N:=Ctx2) (B:=BC) (C:=nil) (D:=nil);solveF
               | [|- MLLN _ _ ?BC _ _] => eapply @mll_tensor with (M:=Ctx1) (N:=Ctx2) (B:=BC) (C:=nil) (D:=nil);solveF
                 end.

Tactic Notation "LLtensor"  := match goal with
               | [ |- MLLS _ ?BC [] _ ] =>  eapply @mll_tensor' with (M:=nil) (N:=nil) (B:=BC) (C:=nil) (D:=nil);solveF
               | [|- MLLN _ _ ?BC [] _] => eapply @mll_tensor with (M:=nil) (N:=nil) (B:=BC) (C:=nil) (D:=nil);solveF
                 end.

Lemma allSeTU (OLS: OLSig) (SI: SigMMLL) (SIU: UNoDSigMMLL) B : SetU B.
Proof with auto.
 induction B...
Qed.

Lemma allSeTLEmpty (OLS: OLSig) (SI: SigMMLL) (SIU: UNoDSigMMLL) (B : list location) : getL B = (@nil location).
Proof with auto.
 rewrite (SetU_then_empty _ (allSeTU SIU B));auto.
Qed.

Lemma permSeTL (OLS: OLSig) (SI: SigMMLL) (SIU: UNoDSigMMLL) (B : list location) : Permutation (getL B) (getL B ++ getL B).
Proof with auto.
 erewrite allSeTLEmpty...
Qed.

Lemma permSeTL' (OLS: OLSig) (SI: SigMMLL)  (B : list location) : SetU B -> Permutation (getL B) (getL B ++ getL B).
Proof with auto.
  intros.
  simplEmpty...
Qed.

Global Hint Resolve allSeTU permSeTL permSeTL': core. 

 Lemma tensorU (OLS: OLSig) (SI: SigMMLL) (SIU: UNoDSigMMLL) n th B MN M N F G:          
  Permutation MN (M ++ N) ->
  MLLN th n B M (DW F) ->
  MLLN th n B N (DW G) -> MLLN th (S n) B MN (DW (MAnd F  G)).
  Proof.   
  intros.
  LLtensor M N.   Qed.

 Lemma tensorU' (OLS: OLSig) (SI : SigMMLL) th B MN M N F G:    SetU B ->    
  Permutation MN (M ++ N) ->
  MLLS th B M (DW F) ->
  MLLS th B N (DW G) -> MLLS th B MN (DW (MAnd F G)).
  Proof.   
  intros.
  LLtensor M N. 
  Qed.

(* Additive conjuction *)
Tactic Notation "LLwith" := match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_with';sauto
    | [|- MLLN _ _ _ _ _] => eapply @mll_with;sauto
end.

(* Additive disjuction *)
Tactic Notation "LLleft" := match goal with
                           | [ |- MLLS _ _ _ _ ] =>   apply mll_plus1';sauto
                           | [|- MLLN _ _ _ _ _] =>  apply mll_plus1;sauto
                            end.

Tactic Notation "LLright" := match goal with
   | [ |- MLLS _ _ _ _ ] =>   apply mll_plus2';sauto
   | [|- MLLN _ _ _ _ _] =>  apply mll_plus2;sauto
end.

(* Multiplicative disjuction *)
Tactic Notation "LLpar" := match goal with
                         | [ |- MLLS _ _ _ _ ] =>  apply mll_par';sauto
                         | [|- MLLN _ _ _ _ _] => apply mll_par;sauto
                         end.

(* Quantifiers *)
Tactic Notation "LLexists" constr(tt) :=  match goal with
   | [ |- MLLS _ _ _ _ ] => eapply @mll_ex' with (t:=tt);try solveUniform;sauto
   | [|- MLLN _ _ _ _ _] => eapply @mll_ex with (t:=tt);try solveUniform;sauto
end.

Tactic Notation "LLforall" := match goal with
   | [ |- MLLS _ _ _ _ ] => eapply @mll_fx'; intros;sauto
   | [|- MLLN _ _ _ _ _] => eapply @mll_fx; intros;sauto
end.

(* Storing formulas *)
Tactic Notation "LLstore" := match goal with
       | [ |- MLLS _ _ _ _ ] =>  apply mll_store';[solveF | auto]
       | [|- MLLN _ _ _ _ _] => apply mll_store;[solveF | auto]
                           end. 

Tactic Notation "LLstorec" := match goal with
       | [ |- MLLS _ _ _ _ ] =>  apply mll_quest';sauto
       | [|- MLLN _ _ _ _ _] => apply mll_quest;sauto
                           end.

(* Changing to the negative phase *)
Tactic Notation "LLrelease" := match goal with
                         | [ |- MLLS _ _ _ _ ] =>  apply mll_rel';[solveF | auto]
                         | [|- MLLN _ _ _ _ _] => apply mll_rel;[solveF | auto]
                         end. 

(* Axioms *)   
Tactic Notation "LLinit1"  := match goal with
     | [ |- MLLS _ _ _ _ ] =>  apply mll_init1';try SLSolve;auto
     | [|- MLLN _ _ _ _ _] => apply mll_init1;try SLSolve;auto
                          end.


Tactic Notation "LLinit2" constr(a) constr(b) := match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_init2' with (i:=a) (C:=b);[try SLSolve | auto | try perm ];auto
    | [|- MLLN _ _ _ _ _] => eapply @mll_init2 with (i:=a) (C:=b);[try SLSolve | auto | try perm ];auto
                          end.

Tactic Notation "LLinit2" constr(a) := match goal with
    | [ |- MLLS _ _ _ _ ] =>  eapply @mll_init2' with (i:=a)
   | [|- MLLN _ _ _ _ _] => eapply @mll_init2 with (i:=a) 
                          end.
                          
Tactic Notation "LLinit2" := match goal with
     | [ |- MLLS _ _ _ _ ] =>  eapply @mll_init2'
    | [|- MLLN _ _ _ _ _] => eapply @mll_init2
                          end.

Tactic Notation "LLone"  := match goal with
                          | [ |- MLLS _ _ _ _ ] =>  apply mll_one';SLSolve
                          | [|- MLLN _ _ _ _ _] => apply mll_one;SLSolve
                          end.

Tactic Notation "LLtop"  := match goal with
                          | [ |- MLLS _ _ _ _ ] =>  apply mll_top'
                          | [|- MLLN _ _ _ _ _] => apply mll_top
                          end.

(* Others rules *)
Tactic Notation "LLbot"  := match goal with
                          | [ |- MLLS _ _ _ _ ] =>  apply mll_bot';sauto
                          | [|- MLLN _ _ _ _ _] => apply mll_bot;sauto
                          end.
                          
Tactic Notation "LLbang"  := match goal with
                          | [ |- MLLS _ _ _ _ ] =>  apply mll_bangL';sauto
                          | [|- MLLN _ _ _ _ _] => apply mll_bangL;sauto
                          end.

Tactic Notation "createWorld" constr(a) := match goal with
                | [ |- MLLS _ _ _ _ ] => eapply @mll_bangD' with (i:=a); try solve [intro ;subst;solveSubExp];auto
                | [|- MLLN _ _ _ _ _] => eapply @mll_bangD with (i:=a);try solve [intro ;subst;solveSubExp];auto
                                end.

Tactic Notation "createWorld" := match goal with
                | [ |- MLLS _ _ _ _ ] => eapply @mll_bang';sauto
                | [|- MLLN _ _ _ _ _] => eapply @mll_bang;sauto
                end.

(* Exponential phase*)                

Tactic Notation "copyK4"  constr(i) constr(P) constr(B) := match goal with
    | [ |- MLLSExp _ _ _ _ _ _ ] => eapply @mll_copyK4' with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | sauto | sauto]
 | [|- MLLNExp _ _ _ _ _ _ _] => eapply @mll_copyK4 with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | sauto | sauto]
                                                       end;auto.

Tactic Notation "copyUK"  constr(i) constr(P) constr(B) := match goal with
| [ |- MLLSExp _ _ _ _ _ _] => eapply @mll_copyUK' with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | solveSE | sauto | sauto]

| [|- MLLNExp _ _ _ _ _ _ _] => eapply @mll_copyUK with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | solveSE | sauto | sauto]
                                                                     end;auto. 
                                                       
Tactic Notation "copyLK"  constr(i) constr(P) constr(B) := match goal with
 | [ |- MLLSExp _ _ _ _ _ _] => eapply @mll_copyLK' with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | solveSE | sauto | sauto]
 | [|- MLLNExp _ _ _ _ _ _ _] => eapply @mll_copyLK with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | solveSE | sauto | sauto]
                                                       end;auto.   
                                                                                                            
   
Tactic Notation "finishExp"  := match goal with
   | [ |- MLLSExp _ _ _ _ _ _] => eapply @mll_exp';[solveF | sauto]
   | [|- MLLNExp _ _ _ _ _ _ _] => eapply @mll_exp;[solveF | sauto]
          end.
     
                          
(** This tactic applies as many positive/negative rules as
  possible. Connectives as exists and tensor are not automatically
  introduced (due to the decision on the contexts/terms ) *)
  
   Ltac negativePhaseReasoning :=
  try match goal with  
  | [ |- MLLS _ _ _ (UP  ((AAnd _ _)::_))] => LLwith 
  | [ |- MLLS _ _ _ (UP ((MOr ?F ?G)::_))] => LLpar
  | [ |- MLLS _ _ _ (UP ((Quest ?i) ?F :: _))] => LLstorec
  | [ |- MLLS _ _ _ (UP (Bot :: _))] => LLbot
  | [ |- MLLS _ _ _ (UP ( (All _) :: _)) ] => let x:= fresh "x" in
                                              let xp := fresh "properX" in
                                              apply mll_fx' ; try solveUniform ; intros x xp

 (* Storing formulas *)
  | [H: posLFormula ?F |- MLLS _ _ _ (UP (?F :: ?M))] => LLstore
    | [|- MLLS _ _ _ (UP  (?F::_))] =>
      match F with
      | AOr _ _ => LLstore
      | MAnd _ _  => LLstore
      | Some _ =>LLstore
      | (atom _)  => LLstore
      | (perp _)  => LLstore
      | One  => LLstore
      | Zero => LLstore
      end
    end.

  Ltac negativePhaseReasoningN :=
  try match goal with  
  | [ |- MLLN _ _ _ _ (UP  ((AAnd _ _)::_))] => LLwith 
  | [ |- MLLN _ _ _ _ (UP ((MOr ?F ?G)::_))] => LLpar
  | [ |- MLLN _ _ _ _ (UP ((Quest ?i) ?F :: _))] => LLstorec
  | [ |- MLLN _ _ _ _ (UP (Bot :: _))] => LLbot
  | [ |- MLLN _ _ _ _ (UP ( (All _) :: _)) ] => let x:= fresh "x" in
                                              let xp := fresh "properX" in
                                              apply mll_fx' ; try solveUniform ; intros x xp

 (* Storing formulas *)
  | [H: posLFormula ?F |- MLLN _ _ _ _ (UP (?F :: ?M))] => LLstore
    | [|- MLLN _ _ _ _ (UP  (?F::_))] =>
      match F with
      | AOr _ _ => LLstore
      | MAnd _ _  => LLstore
      | Some _ =>LLstore
      | (atom _)  => LLstore
      | (perp _)  => LLstore
      | One  => LLstore
      | Zero => LLstore
      end
    end.

  Ltac positivePhaseReasoning :=
  try match goal with  
  | [USI : UNoDSigMMLL |- MLLS _ _ [] (DW  (MAnd _ _))] => LLtensor (@nil oo)  (@nil oo) 
  | [H: MLLS ?th ?B ?L (DW ?F) |- MLLS ?th ?B ?L (DW (AOr ?F ?G))] => LLleft 
  | [H: MLLS ?th ?B ?L (DW ?G) |- MLLS ?th ?B ?L (DW (AOr ?F ?G))] => LLright 
  | [ |- MLLS _ _ _ (DW (Bang loc _))] => apply mll_bangL';negativePhaseReasoning
 
     (* Change of polarity *)
    | [H: negFormula ?F |- MLLS _ _ _ (DW  ?F)] => LLrelease;negativePhaseReasoning
    | [|- MLLS _ _ _ (DW  ?F)] =>
      match F with
      | MOr _ _ => LLrelease;negativePhaseReasoning
      | All _ =>LLrelease;negativePhaseReasoning
      | Bot  => LLrelease;negativePhaseReasoning
      | (atom _)  => LLrelease;negativePhaseReasoning
      | Top  => LLrelease;negativePhaseReasoning
      | AAnd _ _  => LLrelease;negativePhaseReasoning
      | Quest _ _ => LLrelease;negativePhaseReasoning
      end
    end.
 
  Ltac positivePhaseReasoningN :=
  try match goal with  
  | [USI : UNoDSigMMLL |- MLLN _ _ _ [] (DW  (MAnd _ _))] => LLtensor (@nil oo)  (@nil oo) 
  | [H : SetU ?B |- MLLN _ _ ?B [] (DW  (MAnd _ _))] => LLtensor (@nil oo)  (@nil oo) 

  | [H: MLLN _ ?th ?B ?L (DW ?F) |- MLLN _ ?th ?B ?L (DW (AOr ?F ?G))] => LLleft 
  | [H: MLLN _ ?th ?B ?L (DW ?G) |- MLLN _ ?th ?B ?L (DW (AOr ?F ?G))] => LLright 
  | [ |- MLLN _ _ _ _ (DW (Bang loc _))] => apply mll_bangL;negativePhaseReasoningN
 
     (* Change of polarity *)
    | [H: negFormula ?F |- MLLN _ _ _ _ (DW  ?F)] => LLrelease;negativePhaseReasoningN
    | [|- MLLN _ _ _ _ (DW  ?F)] =>
      match F with
      | MOr _ _ => LLrelease;negativePhaseReasoningN
      | All _ =>LLrelease;negativePhaseReasoningN
      | Bot  => LLrelease;negativePhaseReasoningN
      | (atom _)  => LLrelease;negativePhaseReasoningN
      | Top  => LLrelease;negativePhaseReasoningN
      | AAnd _ _  => LLrelease;negativePhaseReasoningN
      | Quest _ _ => LLrelease;negativePhaseReasoningN
      end
    end.
 
 
 
Lemma init2Cut (OLS : OLSig) (SI:SigMMLL) i A L th :
SetU L -> mt i = true ->
In (i,atom A) L -> MLLS th L [] (DW (perp A)).
 Proof with sauto.
 intros.
 apply InPermutation in H1...
 rewrite H1 in H. 
 LLinit2 i x. inversion H...
 Qed.

  Ltac solveAxioms :=
  try
    match goal with
   | [H: MLLS _ _ _ (DW Zero) |- _ ] => inversion H;subst;solveF
   | [ |- MLLS _ _ _ (DW One) ] => LLone
   | [ |- MLLS _ _ [One] (UP [])] => LLfocus1;solveAxioms   
   | [ |- MLLS _ _ [] (UP [One]) ] => LLstore;LLfocus1;solveAxioms
  
   | [ |- MLLS _ _ [Top] (UP [])] => LLfocus1;LLrelease;solveAxioms   
   | [ |- MLLS _ _ _ (UP (Top :: ?M))] => LLtop
  (* initial rules *)
   | [ |- MLLS _ _ [atom ?A] (DW (perp ?A))] => LLinit1
   | [ |- MLLS _ _ [perp ?A; atom ?A] (UP [])] => LLfocus1;solveAxioms   
   | [ |- MLLS _ _ [atom ?A; perp ?A] (UP [])] => LLfocus1 (perp A) [atom A];solveAxioms   

   | [ H: mt ?a = true |- MLLS _ ((?a,atom ?A)::?B) [] (DW (perp ?A))] => LLinit2 a B
    | [ H: mt ?a = true |- MLLS _ (?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => LLinit2 a B
    | [ H: mt ?a = true |- MLLS _ (?X::?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => LLinit2 a (X::B)
    | [ H: mt ?a = true |- MLLS _ (?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => LLinit2 a (B++E)   
    | [ H: mt ?a = true |- MLLS _ (?X::?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => LLinit2 a (X::B++E)   
  
    | [ H: Permutation ((?a,atom _)::?B) ?D |- MLLS  _ ?D [] (DW (perp ?A))] => LLinit2 a B
    | [ H: Permutation (?B++[(?a,atom ?A)]) ?D |- MLLS _ ?D [] (DW (perp ?A))] => LLinit2 a B
    | [ H: Permutation (?B++(?a,atom ?A)::?E) ?D |- MLLS _ ?D [] (DW (perp ?A))] => LLinit2 a (B++E)

    | [ H: Permutation ?D ((?a,atom ?A)::?B)  |- MLLS _ ?D [] (DW (perp ?A))] => LLinit2 a B
    | [ H: Permutation ?D (?B++[(?a,atom ?A)])  |- MLLS _ ?D [] (DW (perp ?A))] => LLinit2 a B
    | [ H: Permutation ?D (?B++(?a,atom ?A)::?E)  |- MLLS _ ?D [] (DW (perp ?A))] => LLinit2 a (B++E)
 
    | [ H: SetU ?L, Hm: mt ?i = true, HIn: In (?i,atom ?A) ?L |- MLLS _ ?L [] (DW (perp ?A))] =>  try solve [refine (init2Cut i _ _ _ _ _);auto]
  
  end.

 Ltac solveAxiomsN :=
  try
    match goal with
 
   | [ |- MLLN _ _ _ _ (DW One) ] => LLone
   | [ |- MLLN _ _ _  [One] (UP [])] => LLfocus1;solveAxiomsN   
   | [ |- MLLN _ _ _ _ (UP (Top :: ?M))] => LLtop
 
     | [H: MLLN _ _ _ _ (DW Zero) |- _ ] => inversion H;subst;solveF

    (* initial rules *)
   | [ |- MLLN _ _ _ [atom ?A] (DW (perp ?A))] => LLinit1
   | [ |- MLLN _ _ _ [perp ?A; atom ?A] (UP [])] => LLfocus1;solveAxiomsN   
   | [ |- MLLN _ _ _ [atom ?A; perp ?A] (UP [])] => LLfocus1 (perp A) [atom A];solveAxiomsN   

   | [ H: mt ?a = true |- MLLN _ _ ((?a,atom ?A)::?B) [] (DW (perp ?A))] => LLinit2 a B
    | [ H: mt ?a = true |- MLLN _ _ (?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => LLinit2 a B
    | [ H: mt ?a = true |- MLLN _ _ (?X::?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => LLinit2 a (X::B)
    | [ H: mt ?a = true |- MLLN _ _ (?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => LLinit2 a (B++E)   
    | [ H: mt ?a = true |- MLLN _ _ (?X::?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => LLinit2 a (X::B++E)   
  
    | [ H: Permutation ((?a,atom _)::?B) ?D |- MLLN _  _ ?D [] (DW (perp ?A))] => LLinit2 a B
    | [ H: Permutation (?B++[(?a,atom ?A)]) ?D |- MLLN _ _ ?D [] (DW (perp ?A))] => LLinit2 a B
    | [ H: Permutation (?B++(?a,atom ?A)::?E) ?D |- MLLN _ _ ?D [] (DW (perp ?A))] => LLinit2 a (B++E)

    | [ H: Permutation ?D ((?a,atom ?A)::?B)  |- MLLN _ _ ?D [] (DW (perp ?A))] => LLinit2 a B
    | [ H: Permutation ?D (?B++[(?a,atom ?A)])  |- MLLN _ _ ?D [] (DW (perp ?A))] => LLinit2 a B
    | [ H: Permutation ?D (?B++(?a,atom ?A)::?E)  |- MLLN _ _ ?D [] (DW (perp ?A))] => LLinit2 a (B++E)

    | [H: MLLNExp _ 0 _ _ _ _ _ |- _ ] => inversion H 
    
    | [H: MLLN _ 0 _ _ (UP ( ?F::_)) |- _ ] =>
    match F with
      | Top => idtac
      | _ => inversion H
    end
   
    | [H: MLLN _ 0 _ _ (DW ?F) |- _ ] =>
    match F with
      | One => idtac
      | perp _ => idtac
      | _ => inversion H
    end
 
   end.

 Ltac solvell :=
   match goal with
   | [ |- MLLN _ _ _ _ (UP _) ] =>  negativePhaseReasoningN
   | [ |- MLLN _ _ _ _ (DW _) ] =>  positivePhaseReasoningN
   end;solveAxiomsN.
 
 Ltac solvell' :=
   match goal with
   | [ |- MLLS _ _ _ (UP _) ] =>  negativePhaseReasoning
   | [ |- MLLS _ _ _ (DW _) ] =>  positivePhaseReasoning
   end;solveAxioms.
 
 Ltac solveLL :=
   match goal with
   | [ |- MLLS _ _ _ _ ] =>  solvell'
   | [ |- MLLN _ _ _ _ _ ] =>  solvell
   end;auto.


(** Erasing some of the (unimportant) hypotheses added by the [solveF] and [solveLL] procedures *)

Ltac CleanContext :=
  sauto;cleanF;solveF;sauto.

