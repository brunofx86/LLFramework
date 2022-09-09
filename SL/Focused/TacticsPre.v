(** * Tactics for the focused system

The tactics defined in this module solves some of the repetitive goals
generated when the system is used. In particular those related
   to well-formedness conditions on formulas
 *)
Require Export LL.Misc.Utils.
Require Export LL.SL.Focused.Sequent.
Require Import LL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Export FLLNotations.
Set Implicit Arguments.

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

(** Cleaning irrelevant hypothesis *)

Ltac clearPolarity :=
 repeat
 match goal with
 | [H: negativeFormula Top  |- _] => clear H
 | [H: negativeFormula Bot  |- _] => clear H
 | [H: negativeFormula (MOr _ _)  |- _] => clear H
 | [H: negativeFormula (atom _)  |- _] => clear H
 | [H: negativeFormula (All _)  |- _] => clear H
 | [H: negativeFormula (AAnd _ _)  |- _] => clear H
 | [H: negativeFormula (Quest _)  |- _] => clear H
 
 | [H: positiveFormula (perp _)  |- _] => clear H
 | [H: positiveFormula Zero  |- _] => clear H
 | [H: positiveFormula One  |- _] => clear H
 | [H: positiveFormula (MAnd _ _)  |- _] => clear H
 | [H: positiveFormula (Some _)  |- _] => clear H
 | [H: positiveFormula (AOr _ _)  |- _] => clear H
 | [H: positiveFormula (Bang _ )  |- _] => clear H 

 | [H: positiveLFormula (atom _)  |- _] => clear H
 | [H: positiveLFormula (perp _)  |- _] => clear H
 | [H: positiveLFormula Zero  |- _] => clear H
 | [H: positiveLFormula One  |- _] => clear H
 | [H: positiveLFormula (MAnd _ _)  |- _] => clear H
 | [H: positiveLFormula (Some _)  |- _] => clear H
 | [H: positiveLFormula (AOr _ _)  |- _] => clear H
 | [H: positiveLFormula (Bang _ )  |- _] => clear H 

 | [H : ~ IsPositiveAtom (perp _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (MOr _ _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (MAnd _ _) |- _ ] => clear H   
 | [H : ~ IsPositiveAtom (AAnd _ _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (AOr _ _) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (Bang _ ) |- _ ] => clear H    
 | [H : ~ IsPositiveAtom (Quest _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (All _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (Some _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom Top |- _ ] => clear H    
 | [H : ~ IsPositiveAtom Bot |- _ ] => clear H 
 | [H : ~ IsPositiveAtom One |- _ ] => clear H 
 | [H : ~ IsPositiveAtom Zero |- _ ] => clear H  
 end.
      
(** Proving goals about polarity *)

Ltac solvePolarity :=
  sauto;
  let H := fresh "H" in
    match goal with
    | [|- ~ negativeFormula _] => intro H; solvePolarity 
    | [|- ~ positiveFormula _] => intro H; solvePolarity
    | [|- ~ positiveLFormula _] => intro H; solvePolarity
    | [|- ~ IsPositiveAtom _ ] => intro H; solvePolarity
    | [|- ~ IsNegativeAtom _ ] => intro H; solvePolarity
    
    | [H: negativeFormula ?F  |- _] =>
      match F with
      | perp _ => inversion H      
      | MAnd _ _ => inversion H
      | AOr _ _ => inversion H
      | Some _ => inversion H
      | Bang _ => inversion H
      | Zero => inversion H
      | One => inversion H
      end
    | [H : positiveFormula ?F |- _ ] =>
      match F with
      | atom _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H      
      | All _ => inversion H
      | Quest _ => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : positiveLFormula ?F |- _ ] =>
      match F with
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | All _ => inversion H
      | Quest _ => inversion H
      | Bot => inversion H
      | Top => inversion H
    end
    | [H : IsPositiveAtom ?F |- _ ] =>
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
    | [H : IsNegativeAtom ?F |- _ ] =>
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
    | [H : ~ IsPositiveAtom _ |- _ ] => try solve[contradict H;auto]
    | [H : ~ positiveLFormula _ |- _ ] => try solve[contradict H;auto]
    | [H : ~ positiveFormula _ |- _ ] => try solve[contradict H;auto]
     | [H : ~ negativeFormula _ |- _ ] => try solve[contradict H;auto] 
    | _  => idtac
    end;auto.
 
(** Notation for forward reasoning on FLL sequents *)

(** Axioms *)

Tactic Notation "FLLinit1"  := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_init1';auto
  | [|- seqN _ _ _ _ _] => apply tri_init1;auto
  end.

Tactic Notation "FLLinit2" := match goal with
  | [ |- seq _ _ _ _ ] =>  eapply @tri_init2';sauto
  | [|- seqN _ _ _ _ _] => eapply @tri_init2;sauto
  end.

Tactic Notation "FLLone"  := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_one'
  | [|- seqN _ _ _ _ _] => apply tri_one
  end.

Tactic Notation "FLLtop"  := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_top'
  | [|- seqN _ _ _ _ _] => apply tri_top
  end.

(** Additives *)
 
Tactic Notation "FLLleft" := match goal with
  | [ |- seq _ _ _ _ ] =>   apply tri_plus1';sauto
  | [|- seqN _ _ _ _ _] =>  apply tri_plus1;sauto
  end.

Tactic Notation "FLLright" := match goal with
  | [ |- seq _ _ _ _ ] =>   apply tri_plus2';sauto
  | [|- seqN _ _ _ _ _] =>  apply tri_plus2;sauto
  end.         

Tactic Notation "FLLwith" := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_with';sauto
    | [|- seqN _ _ _ _ _] => eapply @tri_with;sauto
end. 
  
(** Multiplicatives *)

Tactic Notation "FLLbot"  := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_bot';sauto
  | [|- seqN _ _ _ _ _] => apply tri_bot;sauto
  end.
  
Tactic Notation "FLLpar" := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_par';sauto
  | [|- seqN _ _ _ _ _] => apply tri_par;sauto
  end.

Tactic Notation "FLLsplit"  := match goal with
    | [ |- seq _ _ [] _ ] =>  eapply @tri_tensor' with (M:=nil) (N:=nil);sauto
    | [|- seqN _ _ _ [] _] => eapply @tri_tensor with (M:=nil) (N:=nil);sauto
end.

Tactic Notation "FLLsplit"  constr(Ctx1) constr(Ctx2) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2);sauto
    | [|- seqN _ _ _ _ _] => eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2);sauto
end.
 
(** Exponentials *)

Tactic Notation "FLLstorec" := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_quest';sauto
  | [|- seqN _ _ _ _ _] => apply tri_quest;sauto
  end.              

Tactic Notation "FLLbang"  := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_bang';sauto
  | [|- seqN _ _ _ _ _] => apply tri_bang;sauto
  end.
                          
(** Quantifiers *)
  
Tactic Notation "FLLexists" constr(tt) :=  match goal with
  | [ |- seq _ _ _ _ ] => eapply @tri_ex' with (t:=tt);try solveUniform;sauto
  | [|- seqN _ _ _ _ _] => eapply @tri_ex with (t:=tt);try solveUniform;sauto
  end.

Tactic Notation "FLLforall" := match goal with
  | [ |- seq _ _ _ _ ] => eapply @tri_fx'; intros;sauto
  | [|- seqN _ _ _ _ _] => eapply @tri_fx; intros;sauto
  end.
  
(** Reaction Rules *) 

Tactic Notation "FLLrelease" := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_rel';[solvePolarity | auto]
  | [|- seqN _ _ _ _ _] => apply tri_rel;[solvePolarity | auto]
  end.
  
Tactic Notation "FLLstore" := match goal with
  | [ |- seq _ _ _ _ ] =>  apply tri_store';[solvePolarity | auto]
  | [|- seqN _ _ _ _ _] => apply tri_store;[solvePolarity | auto]
  end.
    
(** Decision Rules *)  

(* Focusing on a linear formula *)
Tactic Notation "LFocus" := match goal with
    | [ |- seq _ _ (?P::?PL) _ ] =>  eapply @tri_dec1' with (F:= P) (L':=PL);[solvePolarity | sauto | sauto ]
    | [|- seqN _ _ _ (?P::?PL) _] => eapply @tri_dec1 with (F:= P) (L':=PL);[solvePolarity | sauto | sauto ]
end.
                              
Tactic Notation "LFocus"  constr(R) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R);[solvePolarity | sauto | sauto ]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec1 with (F:= R);[solvePolarity | sauto | sauto]
end.


Tactic Notation "LFocus"  constr(R) constr(T) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R) (L':=T);[solvePolarity | sauto | sauto ]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec1 with (F:= R) (L':=T);[solvePolarity | sauto | sauto]
end.

(* Focusing on a classical formula *)
Tactic Notation "CFocus" := match goal with
    | [ |- seq _ (?P::_) _ _ ] =>  eapply @tri_dec2' with (F:= P);[solvePolarity | sauto | sauto]
    | [|- seqN _ _ (?P::_) _ _] => eapply @tri_dec2 with (F:= P);[solvePolarity | sauto | sauto ]
end.
                                                                             
Tactic Notation "CFocus"  constr(S) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec2' with (F:= S);[solvePolarity | sauto | sauto]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec2 with (F:= S);[solvePolarity | sauto | sauto]
end.

(* Focusing on a theory *)
Tactic Notation "TFocus"  constr(S) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec3' with (F:= S);[solvePolarity | sauto | sauto]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec3 with (F:= S);[solvePolarity | sauto | sauto]
end.
                                                    
(** This tactic applies as many positive/negative rules as
  possible. Connectives as exists and tensor are not automatically
  introduced (due to the decision on the contexts/terms ) *)

Ltac solveAxiom :=
 match goal with 
  | [ |- seqN _ _ _ [atom ?A] (DW (perp ?A))] => FLLinit1
  | [ |- seqN _ _ _ [perp ?A; atom ?A] (UP [])] => LFocus;FLLinit1
  | [ |- seqN _ _ _ [atom ?A; perp ?A] (UP [])] => LFocus (perp A) [atom A];FLLinit1

  | [ |- seqN _ _ _ [] (DW (perp ?A))] => FLLinit2
  | [ |- seqN _ _ (atom ?A::_) [perp ?A] (UP [])] =>  LFocus;FLLinit2
  | [ |- seqN _ _ (perp ?A::atom ?A::_) [] (UP [])] =>  CFocus;FLLinit2
  | [ |- seqN _ _ (perp ?A::_) [atom ?A] (UP [])] =>  CFocus;FLLinit1

  | [ |- seqN _ _ _ [] (DW (One))] => FLLone       
  | [ |- seqN _ _ _ [One] (UP [])] => LFocus;FLLone
  | [ |- seqN _ _ (One::_) [] (UP [])] => CFocus;FLLone
  
  | [ |- seqN _ _ _ _ (UP [Top])] => FLLtop       
  | [ |- seqN _ _ (Top::_) _ (UP [])] => CFocus;FLLrelease;FLLtop  
  
  | _ => idtac   
end. 
  
 Ltac solveAxiom' :=
 match goal with 
  | [ |- seq  _ _ [atom ?A] (DW (perp ?A))] => FLLinit1
  | [ |- seq  _ _ [perp ?A; atom ?A] (UP [])] => LFocus;FLLinit1
  | [ |- seq _ _ [atom ?A; perp ?A] (UP [])] => LFocus (perp A) [atom A];FLLinit1


  | [ |- seq _ _ [] (DW (perp ?A))] => FLLinit2
  | [ |- seq _ (atom ?A::_) [perp ?A] (UP [])] =>  LFocus;FLLinit2
  | [ |- seq _ (perp ?A::atom ?A::_) [] (UP [])] =>  CFocus;FLLinit2
  | [ |- seq _ (perp ?A::_) [atom ?A] (UP [])] =>  CFocus;FLLinit1
  
  | [ |- seq _ _ [] (DW (One))] => FLLone       
  | [ |- seq _ _ [One] (UP [])] => LFocus;FLLone
  | [ |- seq _ (One::_) [] (UP [])] => CFocus;FLLone
  
  | [ |- seq _ _ _ (UP [Top])] => FLLtop       
  | [ |- seq _ (Top::_) _ (UP [])] => CFocus;FLLrelease;FLLtop  
  
  | _ => idtac   
end. 
 
Ltac reasoningLL :=
solveAxiom;
 match goal with 
  (* Change of polarity *)
  | [H:  negativeFormula ?F |- seqN _ _ _ _ (DW  ?F)] => FLLrelease;reasoningLL
  | [|- seqN _ _ _ _ (DW ?F)] =>
      match F with
      | Bot => FLLrelease ;reasoningLL
      | One => FLLone
      | Zero  => idtac
      | Top => FLLrelease ;reasoningLL
      
      | atom _  => FLLrelease ;reasoningLL
      | perp _  => idtac
      
      | AOr _ _ => idtac
      | MOr _ _ => FLLrelease ;reasoningLL
      | MAnd _ _  => idtac 
      | AAnd _ _  => FLLrelease ;reasoningLL
      | Bang _ => FLLbang;reasoningLL
      | Quest _ => FLLrelease ;reasoningLL
      | Some _ => idtac
      | All _ => FLLrelease ;reasoningLL     
      end
  
    (* Negative Phase *)
  | [ H: positiveLFormula ?F |- seqN _ _ _ _ (UP (?F:: _ ))] => FLLstore;auto;reasoningLL
  
  | [|- seqN _ _ _ _ (UP (?F::_))] =>
      match F with
      | Bot => FLLbot ;reasoningLL
      | One => FLLstore;reasoningLL
      | Zero  => FLLstore;reasoningLL
      | Top => FLLtop
      
      | atom _  => FLLstore;reasoningLL
      | perp _  =>  FLLstore;reasoningLL
      
      | AOr _ _ => FLLstore;reasoningLL
      | MOr _ _ => FLLpar ;reasoningLL
      | MAnd _ _  => FLLstore;reasoningLL
      | AAnd _ _  =>  FLLwith;reasoningLL
      | Bang _ => FLLstore;reasoningLL
      | Quest _ => FLLstorec;reasoningLL
      | Some _ => FLLstore;reasoningLL
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
  | [H:  negativeFormula ?F |- seq _ _ _ (DW  ?F)] => FLLrelease;reasoningLL'
  | [|- seq _ _ _ (DW ?F)] =>
      match F with
      | Bot => FLLrelease ;reasoningLL'
      | One => FLLone
      | Zero  => idtac
      | Top => FLLrelease ;reasoningLL'
      
      | atom _  => FLLrelease ;reasoningLL'
      | perp _  => idtac
      
      | AOr _ _ => idtac
      | MOr _ _ => FLLrelease ;reasoningLL'
      | MAnd _ _  => idtac
      | AAnd _ _  => FLLrelease ;reasoningLL'
      | Bang _ => FLLbang;reasoningLL'
      | Quest _ => FLLrelease ;reasoningLL'
      | Some _ => idtac
      | All _ => FLLrelease ;reasoningLL'     
      end
  
    (* Negative Phase *)
  | [ H: positiveLFormula ?F |- seq _ _ _ (UP (?F:: _ ))] => FLLstore;auto;reasoningLL'
  
  | [|- seq _ _ _ (UP (?F::_))] =>
      match F with
      | Bot => FLLbot;reasoningLL'
      | One => FLLstore;reasoningLL'
      | Zero  => FLLstore;reasoningLL'
      | Top => FLLtop
      
      | atom _  => FLLstore;reasoningLL'
      | perp _  => FLLstore;reasoningLL'
      
      | AOr _ _ => FLLstore;reasoningLL'
      | MOr _ _ => FLLpar;reasoningLL'
      | MAnd _ _  => FLLstore;reasoningLL'
      | AAnd _ _  => FLLwith;reasoningLL'
      | Bang _ => FLLstore;reasoningLL'
      | Quest _ => FLLstorec;reasoningLL'
      | Some _ => FLLstore;reasoningLL'
      | All _ => let x:= fresh "x" in
                 let xp := fresh "properX" in
                 apply tri_fx' ;try solveUniform; intros x xp ; reasoningLL'      
  end
| _ => idtac     
end.  
 
 
Ltac solveLL :=
   match goal with
  | [H: seq _ _ _ (DW Zero) |- _ ] => inversion H;solvePolarity
  | [H: seqN _ _ _ _ (DW Zero) |- _ ] => inversion H;solvePolarity          
  | [H: seqN _ 0 _ _ (UP _) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW (MAnd _ _)) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW (AOr _ _)) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW (MOr _ _)) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW (AAnd _ _)) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW (Quest _)) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW (Bang _)) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW (Some _)) |- _ ] => inversion H
  | [H: seqN _ 0 _ _ (DW (All _)) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW (atom _)) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW Top) |- _ ] => inversion H 
  | [H: seqN _ 0 _ _ (DW Bot) |- _ ] => inversion H 
  
   | [ |- seq _ _ _ _ ] =>  reasoningLL'
   | [|- seqN _ _ _ _ _] => reasoningLL
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