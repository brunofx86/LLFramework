(** * Tactics for the focused system

The tactics defined in this module solves some of the repetitive goals
generated when the system is used. In particular those related
   to well-formedness conditions on formulas
 *)
Require Export LL.Misc.Utils.
Require Export LL.Framework.SL.FLL.Sequent.
Require Import LL.Misc.Permutations.
Require Import LL.Misc.UtilsForall.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(* Ltac solveUniform :=
  auto;
  repeat 
    match goal with
    | [|- uniform_oo _] =>  constructor 
    | [|- uniform _ ] => eauto 10  using uniform_id, uniform_con, uniform_app, proper_uniform, abstr_lambda
    | [|- uniform_atm _ ] => constructor
    | [|- proper _ ] => constructor
    | [|- level _ _ ] => constructor
    end.
 *)
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
    | [|- ~ negFormula _] => autounfold;intro H; solvePolarity 
    | [|- ~ posFormula _] => autounfold;intro H; solvePolarity
    | [|- ~ posLFormula _] => autounfold;intro H; solvePolarity
    | [|- ~ posAtom _ ] => autounfold;intro H; solvePolarity
    | [|- ~ negAtom _ ] => autounfold;intro H; solvePolarity
    
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
 
(** Notation for forward reasoning on FLL sequents *)

(** Axioms *)

Tactic Notation "LLinit1"  := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_init1';auto
  | [|- FLLN _ _ _ _ _] => apply tri_init1;auto
  end.

Tactic Notation "LLinit2" := match goal with
  | [ |- FLLS _ _ _ _ ] =>  eapply @tri_init2';sauto
  | [|- FLLN _ _ _ _ _] => eapply @tri_init2;sauto
  end.

Tactic Notation "LLone"  := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_one'
  | [|- FLLN _ _ _ _ _] => apply tri_one
  end.

Tactic Notation "LLtop"  := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_top'
  | [|- FLLN _ _ _ _ _] => apply tri_top
  end.

(** Additives *)
 
Tactic Notation "LLleft" := match goal with
  | [ |- FLLS _ _ _ _ ] =>   apply tri_plus1';sauto
  | [|- FLLN _ _ _ _ _] =>  apply tri_plus1;sauto
  end.

Tactic Notation "LLright" := match goal with
  | [ |- FLLS _ _ _ _ ] =>   apply tri_plus2';sauto
  | [|- FLLN _ _ _ _ _] =>  apply tri_plus2;sauto
  end.         

Tactic Notation "LLwith" := match goal with
    | [ |- FLLS _ _ _ _ ] =>  eapply @tri_with';sauto
    | [|- FLLN _ _ _ _ _] => eapply @tri_with;sauto
end. 
  
(** Multiplicatives *)

Tactic Notation "LLbot"  := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_bot';sauto
  | [|- FLLN _ _ _ _ _] => apply tri_bot;sauto
  end.
  
Tactic Notation "LLpar" := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_par';sauto
  | [|- FLLN _ _ _ _ _] => apply tri_par;sauto
  end.

Tactic Notation "LLtensor"  := match goal with
    | [ |- FLLS _ _ [] _ ] =>  eapply @tri_tensor' with (M:=nil) (N:=nil);sauto
    | [|- FLLN _ _ _ [] _] => eapply @tri_tensor with (M:=nil) (N:=nil);sauto
end.

Tactic Notation "LLtensor"  constr(Ctx1) constr(Ctx2) := match goal with
    | [ |- FLLS _ _ _ _ ] =>  eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2);sauto
    | [|- FLLN _ _ _ _ _] => eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2);sauto
end.
 
(** Exponentials *)

Tactic Notation "LLstorec" := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_quest';sauto
  | [|- FLLN _ _ _ _ _] => apply tri_quest;sauto
  end.              

Tactic Notation "LLbang"  := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_bang';sauto
  | [|- FLLN _ _ _ _ _] => apply tri_bang;sauto
  end.
                          
(** Quantifiers *)
  
Tactic Notation "LLexists" constr(tt) :=  match goal with
  | [ |- FLLS _ _ _ _ ] => eapply @tri_ex' with (t:=tt);try solveUniform;sauto
  | [|- FLLN _ _ _ _ _] => eapply @tri_ex with (t:=tt);try solveUniform;sauto
  end.

Tactic Notation "LLforall" := match goal with
  | [ |- FLLS _ _ _ _ ] => eapply @tri_fx'; intros;sauto
  | [|- FLLN _ _ _ _ _] => eapply @tri_fx; intros;sauto
  end.
  
(** Reaction Rules *) 

Tactic Notation "LLrelease" := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_rel';[solvePolarity | auto]
  | [|- FLLN _ _ _ _ _] => apply tri_rel;[solvePolarity | auto]
  end.
  
Tactic Notation "LLstore" := match goal with
  | [ |- FLLS _ _ _ _ ] =>  apply tri_store';[solvePolarity | auto]
  | [|- FLLN _ _ _ _ _] => apply tri_store;[solvePolarity | auto]
  end.
    
(** Decision Rules *)  

(* Focusing on a linear formula *)
Tactic Notation "LLfocus1" := match goal with
    | [ |- FLLS _ _ (?P::?PL) _ ] =>  eapply @tri_dec1' with (F:= P) (L':=PL);[solvePolarity | sauto | sauto ]
    | [|- FLLN _ _ _ (?P::?PL) _] => eapply @tri_dec1 with (F:= P) (L':=PL);[solvePolarity | sauto | sauto ]
end.
                              
Tactic Notation "LLfocus1"  constr(R) := match goal with
    | [ |- FLLS _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R);[solvePolarity | sauto | sauto ]
    | [|- FLLN _ _ _ _ _] => eapply @tri_dec1 with (F:= R);[solvePolarity | sauto | sauto]
end.


Tactic Notation "LLfocus1"  constr(R) constr(T) := match goal with
    | [ |- FLLS _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R) (L':=T);[solvePolarity | sauto | sauto ]
    | [|- FLLN _ _ _ _ _] => eapply @tri_dec1 with (F:= R) (L':=T);[solvePolarity | sauto | sauto]
end.

(* Focusing on a classical formula *)
Tactic Notation "LLfocus2" := match goal with
    | [ |- FLLS _ (?P::_) _ _ ] =>  eapply @tri_dec2' with (F:= P);[solvePolarity | sauto | sauto]
    | [|- FLLN _ _ (?P::_) _ _] => eapply @tri_dec2 with (F:= P);[solvePolarity | sauto | sauto ]
end.
                                                                             
Tactic Notation "LLfocus2"  constr(S) := match goal with
    | [ |- FLLS _ _ _ _ ] =>  eapply @tri_dec2' with (F:= S);[solvePolarity | sauto | sauto]
    | [|- FLLN _ _ _ _ _] => eapply @tri_dec2 with (F:= S);[solvePolarity | sauto | sauto]
end.

(* Focusing on a theory *)
Tactic Notation "LLtheory"  constr(S) := match goal with
    | [ |- FLLS _ _ _ _ ] =>  eapply @tri_dec3' with (F:= S);[solvePolarity | sauto | sauto]
    | [|- FLLN _ _ _ _ _] => eapply @tri_dec3 with (F:= S);[solvePolarity | sauto | sauto]
end.
                                                    
(** This tactic applies as many positive/negative rules as
  possible. Connectives as exists and tensor are not automatically
  introduced (due to the decision on the contexts/terms ) *)

Ltac solveAxiom :=
 match goal with 
  | [ |- FLLN _ _ _ [atom ?A] (DW (perp ?A))] => LLinit1
  | [ |- FLLN _ _ _ [perp ?A; atom ?A] (UP [])] => LLfocus1;LLinit1
  | [ |- FLLN _ _ _ [atom ?A; perp ?A] (UP [])] => LLfocus1 (perp A) [atom A];LLinit1

  | [ |- FLLN _ _ _ [] (DW (perp ?A))] => LLinit2
  | [ |- FLLN _ _ (atom ?A::_) [perp ?A] (UP [])] =>  LLfocus1;LLinit2
  | [ |- FLLN _ _ (perp ?A::atom ?A::_) [] (UP [])] =>  LLfocus2;LLinit2
  | [ |- FLLN _ _ (perp ?A::_) [atom ?A] (UP [])] =>  LLfocus2;LLinit1

  | [ |- FLLN _ _ _ [] (DW (One))] => LLone       
  | [ |- FLLN _ _ _ [One] (UP [])] => LLfocus1;LLone
  | [ |- FLLN _ _ (One::_) [] (UP [])] => LLfocus2;LLone
  
  | [ |- FLLN _ _ _ _ (UP [Top])] => LLtop       
  | [ |- FLLN _ _ (Top::_) _ (UP [])] => LLfocus2;LLrelease;LLtop  
  
  | _ => idtac   
end. 
  
 Ltac solveAxiom' :=
 match goal with 
  | [ |- FLLS  _ _ [atom ?A] (DW (perp ?A))] => LLinit1
  | [ |- FLLS  _ _ [perp ?A; atom ?A] (UP [])] => LLfocus1;LLinit1
  | [ |- FLLS _ _ [atom ?A; perp ?A] (UP [])] => LLfocus1 (perp A) [atom A];LLinit1


  | [ |- FLLS _ _ [] (DW (perp ?A))] => LLinit2
  | [ |- FLLS _ (atom ?A::_) [perp ?A] (UP [])] =>  LLfocus1;LLinit2
  | [ |- FLLS _ (perp ?A::atom ?A::_) [] (UP [])] =>  LLfocus2;LLinit2
  | [ |- FLLS _ (perp ?A::_) [atom ?A] (UP [])] =>  LLfocus2;LLinit1
  
  | [ |- FLLS _ _ [] (DW (One))] => LLone       
  | [ |- FLLS _ _ [One] (UP [])] => LLfocus1;LLone
  | [ |- FLLS _ (One::_) [] (UP [])] => LLfocus2;LLone
  
  | [ |- FLLS _ _ _ (UP [Top])] => LLtop       
  | [ |- FLLS _ (Top::_) _ (UP [])] => LLfocus2;LLrelease;LLtop  
  
  | _ => idtac   
end. 
 
Ltac reasoningLL :=
solveAxiom;
 match goal with 
  (* Change of polarity *)
  | [H:  negFormula ?F |- FLLN _ _ _ _ (DW  ?F)] => LLrelease;reasoningLL
  | [|- FLLN _ _ _ _ (DW ?F)] =>
      match F with
      | Bot => LLrelease ;reasoningLL
      | One => LLone
      | Zero  => idtac
      | Top => LLrelease ;reasoningLL
      
      | atom _  => LLrelease ;reasoningLL
      | perp _  => idtac
      
      | AOr _ _ => idtac
      | MOr _ _ => LLrelease ;reasoningLL
      | MAnd _ _  => idtac 
      | AAnd _ _  => LLrelease ;reasoningLL
      | Bang _ => LLbang;reasoningLL
      | Quest _ => LLrelease ;reasoningLL
      | Some _ => idtac
      | All _ => LLrelease ;reasoningLL     
      end
  
    (* Negative Phase *)
  | [ H: posLFormula ?F |- FLLN _ _ _ _ (UP (?F:: _ ))] => LLstore;auto;reasoningLL
  
  | [|- FLLN _ _ _ _ (UP (?F::_))] =>
      match F with
      | Bot => LLbot ;reasoningLL
      | One => LLstore;reasoningLL
      | Zero  => LLstore;reasoningLL
      | Top => LLtop
      
      | atom _  => LLstore;reasoningLL
      | perp _  =>  LLstore;reasoningLL
      
      | AOr _ _ => LLstore;reasoningLL
      | MOr _ _ => LLpar ;reasoningLL
      | MAnd _ _  => LLstore;reasoningLL
      | AAnd _ _  =>  LLwith;reasoningLL
      | Bang _ => LLstore;reasoningLL
      | Quest _ => LLstorec;reasoningLL
      | Some _ => LLstore;reasoningLL
      | All _ => let x:= fresh "x" in
                 let xp := fresh "properX" in
                 apply tri_fx ;try solveUniform; intros x xp ; reasoningLL      
  end
  | _ => idtac 
end.  

    
Ltac reasoningLL' :=
solveAxiom';
 match goal with
  (* Change of polarity *)
  | [H:  negFormula ?F |- FLLS _ _ _ (DW  ?F)] => LLrelease;reasoningLL'
  | [|- FLLS _ _ _ (DW ?F)] =>
      match F with
      | Bot => LLrelease ;reasoningLL'
      | One => LLone
      | Zero  => idtac
      | Top => LLrelease ;reasoningLL'
      
      | atom _  => LLrelease ;reasoningLL'
      | perp _  => idtac
      
      | AOr _ _ => idtac
      | MOr _ _ => LLrelease ;reasoningLL'
      | MAnd _ _  => idtac
      | AAnd _ _  => LLrelease ;reasoningLL'
      | Bang _ => LLbang;reasoningLL'
      | Quest _ => LLrelease ;reasoningLL'
      | Some _ => idtac
      | All _ => LLrelease ;reasoningLL'     
      end
  
    (* Negative Phase *)
  | [ H: posLFormula ?F |- FLLS _ _ _ (UP (?F:: _ ))] => LLstore;auto;reasoningLL'
  
  | [|- FLLS _ _ _ (UP (?F::_))] =>
      match F with
      | Bot => LLbot;reasoningLL'
      | One => LLstore;reasoningLL'
      | Zero  => LLstore;reasoningLL'
      | Top => LLtop
      
      | atom _  => LLstore;reasoningLL'
      | perp _  => LLstore;reasoningLL'
      
      | AOr _ _ => LLstore;reasoningLL'
      | MOr _ _ => LLpar;reasoningLL'
      | MAnd _ _  => LLstore;reasoningLL'
      | AAnd _ _  => LLwith;reasoningLL'
      | Bang _ => LLstore;reasoningLL'
      | Quest _ => LLstorec;reasoningLL'
      | Some _ => LLstore;reasoningLL'
      | All _ => let x:= fresh "x" in
                 let xp := fresh "properX" in
                 apply tri_fx' ;try solveUniform; intros x xp ; reasoningLL'      
  end
| _ => idtac     
end.  
 
 
Ltac solveLL :=
   match goal with
  | [H: FLLS _ _ _ (DW Zero) |- _ ] => inversion H;solvePolarity
  | [H: FLLN _ _ _ _ (DW Zero) |- _ ] => inversion H;solvePolarity          
  | [H: FLLN _ 0 _ _ (UP _) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW (MAnd _ _)) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW (AOr _ _)) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW (MOr _ _)) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW (AAnd _ _)) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW (Quest _)) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW (Bang _)) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW (Some _)) |- _ ] => inversion H
  | [H: FLLN _ 0 _ _ (DW (All _)) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW (atom _)) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW Top) |- _ ] => inversion H 
  | [H: FLLN _ 0 _ _ (DW Bot) |- _ ] => inversion H 
  
   | [ |- FLLS _ _ _ _ ] =>  reasoningLL'
   | [|- FLLN _ _ _ _ _] => reasoningLL
   | _ => idtac

   end;auto.


(** Erasing some of the (unimportant) hypotheses added by the [solvePolarity] and [solveLL] procedures *)

Ltac CleanContext :=
  sauto;clearPolarity;solvePolarity;sauto.

Ltac foldIsFormula :=
  match goal with 
| [ H: Forall isFormula ?L |-  _ ] => fold (isFormulaL L) in H
end.
  

Ltac solveIsFormula := auto;
try foldIsFormula;
  match goal with 
  | [ H: isFormulaL (_++_::_) |-  _ ] => 
  rewrite Permutation_midle in H;solveIsFormula

  | [ H: isFormulaL (_::_) |-  _ ] => inversion H;subst;clear H;solveIsFormula
  | [ H: isFormulaL (_++[_]) |- _ ] => apply Forall_app in H;destruct H;solveIsFormula


  | [ H: isFormula (_ ?A _) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormula (_ _ ?A) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormula (_ ?A) |- isFormula ?A ] => inversion H;subst;eauto
  | [ H: isFormula (_ ?FX) |- isFormula (?FX _) ] => inversion H;subst;eauto
| _ => idtac
 end.

Ltac Wfirst := simpl;
match goal with
| [ |- context[_++_::_] ] => rewrite Permutation_midle;Wfirst
| [ |- context[_++[_]++_] ] => rewrite Permutation_midle_app;Wfirst
| [ |- context[_++[_;_]++_] ] => rewrite Permutation_midle_app;Wfirst
| [ |- context[_++[_]++_] ] => rewrite Permutation_midle_app;Wfirst
| [ |- context[_++[_]] ] => rewrite <- Permutation_cons_append;Wfirst

| _ => idtac
end; try rewrite app_nil_r.

Ltac solveForall :=  
match goal with
| [  |- Forall _ nil] => apply Forall_nil
| [H: Forall ?P (?a :: _) |- ?P ?a] => apply Forall_inv in H
| [H: Forall ?P (_ :: ?l) |- Forall ?P ?l] => apply Forall_inv_tail in H
| [H: Forall ?P (_ ++ ?l) |- Forall ?P ?l] => apply Forall_app in H; destruct H
| [H: Forall ?P (?l ++ _) |- Forall ?P ?l] => apply Forall_app in H; destruct H
| [ H1 : Forall ?P ?M, H2 : Forall ?P ?N |- Forall ?P (?M++?N) ] => apply Forall_app;split 

| [H: Forall ?P (_ ++ ?a :: _) |- ?P ?a] => apply Forall_elt in H

| [H1: Forall ?P ?L1, 
H2: Permutation ?L1 ?L2 |-  Forall ?P ?L2] => refine(PermuteMap H1 H2)
| [H1: Forall ?P ?L1, 
H2: Permutation ?L2 ?L1 |-  Forall ?P ?L2] => refine(PermuteMap H1 (symmetry H2))

| [H: ?P ?a |-  Forall ?P (?a :: _)] => apply Forall_cons
| [H: Forall ?P ?L |-  Forall ?P (_ :: ?L)] => apply Forall_cons

| [ H1 : Forall ?P ?M, H2 : Forall ?P ?N |- Forall ?P (?M++?N) ] => apply Forall_app;split 
| [ H: Forall ?P (?M++?N) |-  Forall ?P ?M ] => apply Forall_app in H; destruct H
| [ H: Forall ?P (?M++?N) |-  Forall ?P ?N ] => apply Forall_app in H; destruct H 

| _ => idtac
end;auto.


Ltac solveIsFormula1 := auto;try
  match goal with
  | [ H1: isFormulaL ?L, H2: In ?P ?L  |- isFormula ?P ] => apply isFormulaIn in H2;auto
  | [ H1: isFormulaL ?L, H2: In (_ ?A _) ?L  |- isFormula ?A ] => apply isFormula in H2;solveIsFormula1
  | [ H1: isFormulaL ?L, H2: In (_ _ ?A) ?L  |- isFormula ?A ] => apply isFormulaIn in H2;solveIsFormula1
  | [ H1: isFormulaL ?L, H2: In (_ ?A) ?L  |- isFormula (?A _) ] => apply isFormulaIn in H2;solveIsFormula1
 
  | [ H1: isFormulaL ?L, H2: Permutation ?L (?P::_)  |- isFormula ?P ] => apply isFormulaInP in H2;auto
  | [ H1: isFormulaL ?L, H2: Permutation ?L ((_ ?A _)::_)  |- isFormula ?A ] => apply isFormulaInP in H2;solveIsFormula1
  | [ H1: isFormulaL ?L, H2: Permutation ?L ((_ _ ?A)::_)  |- isFormula ?A ] => apply isFormulaInP in H2;solveIsFormula1
  | [ H1: isFormulaL ?L, H2: Permutation ?L ((_ ?A)::_)  |- isFormula (?A _) ] => apply isFormulaInP in H2;solveIsFormula1

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




Ltac SLFormulaSolve := auto; try solve[solveIsFormula1];
match goal with
 | [ |- isFormulaL ?K] => simpl;solveFoldFALL1 isFormula;solveIsFormula1
end.