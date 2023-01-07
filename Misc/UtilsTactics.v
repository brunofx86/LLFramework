
(** * Tactics *)
(**  Some useful tactics dealing with permutations, lists and maps
 *)

Require Export Permutation.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.
Require Export Coq.Init.Nat.
Require Export LL.Misc.Permutations. 
Require Export LL.Misc.Utils.
Require Import Lia.
Export ListNotations.

Set Implicit Arguments.

  
 Global Hint Extern 1 (Permutation ?S ?U) =>
  match goal with
  | H: Permutation S ?T |- _ => apply (Permutation_trans H)
  | H: Permutation ?T S  |- _ => symmetry in H; apply (Permutation_trans H)  
  end : core.
  
Ltac clear_junk :=
repeat
 match goal with
 | [ H: ?A = ?A |- _ ] => clear H
 | [ H: ?A <-> ?A |- _ ] => clear H
 | [ H: ?A -> ?A |- _ ] => clear H
 | [ H1: ?A, H2: ?A |- _ ] => clear H1
 | [ H: Permutation ?A ?A |- _] => clear H 
 | [ H: True |- _ ] => clear H
 | [ H: In ?F (?F::_) |- _ ] => clear H
 | [ H: In ?F (_++[?F]) |- _ ] => clear H
 | [ H: In ?F (_++?F::_)|- _ ] => clear H
 end.

Ltac simpl_goal :=
auto;
  match goal with
  | H : _ /\ _ |- _ => decompose [and or] H; clear H; simpl_goal
  | H : _ \/ _ |- _ => decompose [and or] H ; clear H; simpl_goal 
  | H : @ex _ _ |- _ => destruct H as [? H]; simpl_goal
  |  |- _ /\ _ => split; simpl_goal
  | |- _ => idtac  
  end.
  
 Ltac simplifier :=
subst;simpl_goal;
  match goal with
 | [ H: map ?f ?B = [_] |- _ ] => apply map_eq_cons in H;simplifier
 | [ H: map ?f ?B = [ ] |- _ ] => apply map_eq_nil in H;simplifier
 
 | [ H: context[_++nil] |- _ ] => rewrite app_nil_r in H;simplifier
 | [ H: context[nil++_] |- _ ] => rewrite app_nil_l in H;simplifier
 | [  |- context[_++nil] ] => rewrite app_nil_r;simplifier
 | [  |- context[nil++_] ] => rewrite app_nil_l;simplifier

 | [ H: context[_ - 0] |- _ ] => rewrite Nat.sub_0_r in H;simplifier
 | [ H: context[S _ - 1] |- _ ] => simpl in H;rewrite Nat.sub_0_r in H;simplifier 
 | [ H: context[fst (_, _)] |- _ ] => simpl in H;simplifier
 | [ H: context[snd (_, _)] |- _ ] => simpl in H;simplifier
 | [  |- context[_ - 0] ] => rewrite Nat.sub_0_r;simplifier
 | [  |- context[S _ - 1] ] => simpl;rewrite Nat.sub_0_r;simplifier
 | [  |- context[fst (_, _)] ] => simpl;simplifier
 | [  |- context[snd (_, _)] ] => simpl;simplifier
 
   | [ H1: ?f ?a = true, H2: context[?f ?a] |- _ ] => rewrite H1 in H2;simplifier
  | [ H1: ?f ?a = false, H2: context[?f ?a] |- _ ] => rewrite H1 in H2;simplifier
                   
  | [ H: ?f ?a = true |- context[?f ?a]  ] => rewrite H;simplifier
  | [ H: ?f ?a = false |- context[?f ?a]  ] => rewrite H;simplifier
 
   | [ H1: ?f = [], H2: context[?f] |- _ ] => rewrite H1 in H2;simplifier                 
  | [ H: ?f = [] |- context[?f]  ] => rewrite H;simplifier 
   | |- _ => idtac   
end;auto.

                    
Ltac strivial := 
try
  match goal with
 | [H1: ?f ?a = true, H2: ?f ?a = false |- _] => rewrite H1 in H2; discriminate H2
 
 | [  |- ?a = ?a ] => reflexivity 
 | [H: False |- _] => contradiction
 | [H1: ?F , H2 : ~ ?F |- _ ] => contradiction
 | [ |- In ?F (?F :: _)] => apply in_eq
 | [H: In ?F ?L  |- In ?F (_ :: ?L)] => apply in_cons;auto
 | [H: In ?F ?L  |- In ?F (?L ++ _)] => apply in_or_app;left;auto
 | [H: In ?F ?L  |- In ?F (_ ++ ?L)] => apply in_or_app;right;auto
 | [ |- In ?F (_++ ?F :: _)] => apply in_elt
 | [ H: In _ nil |- _ ] => inversion H 
 | [ H: [_] = nil |- _ ] => inversion H 
 | [ H: nil = [_] |- _ ] => inversion H 

 | [ H: Permutation ?A ?B |- Permutation ?B ?A  ] => symmetry in H;auto
 | [ |- Permutation (?x::?y::?A) (?y::?x::?A)  ] =>  rewrite perm_swap;auto
 | [H : ?A /\ ?B |- ?A ] => firstorder 
 | [H : ?A /\ ?B |- ?B ] => firstorder  
 | [H : ?A |- ?A \/ ?B ] => firstorder 
 | [H : ?B |- ?A \/ ?B] => firstorder 
   
 | [ H: ?a <> ?a |- _ ] => try solve [timeout 2 firstorder]

 | [ H1: forall x, ?P x -> ?L = ?R, H2: ?P ?X |- _ ] => rewrite (H1 X H2) in x
 | [ H1: ?P ?X -> ?P ?Y, H2: ?P ?X |- ?P ?Y ] => apply H1;auto
 | [ H1: _ ?P ?X -> _ ?P ?Y, H2: _ ?P ?X, H3: ?P ?F  |- _ ?P (?F::?Y) ] => simpl;apply H1;auto
 | [  |- _ <= _ ] => try solve[lia]
 | [|- _ >= _ ] => try solve[lia]
 | [|- _ < _ ] => try solve[lia]
 | [|- _ > _ ] => try solve[lia]
 | [|- Permutation _ _ ] => try solve[simpl;subst;perm]
 end;auto.

  
Ltac clean_goal :=
try
repeat 
 match goal with
 | [ H: ?a = ?b |- _ ] => solve [inversion H]
 | [ H: [?a] = [?b] |- _ ] => inversion H;subst;clear H
 | [ H: (_,_) = (_,_) |- _ ] => inversion H;clear H

 (* About Permutations *)
 | [ H: Permutation nil ?L |- _] => apply Permutation_nil in H
 | [ H: Permutation ?L nil  |- _] => symmetry in H; apply Permutation_nil in H
 | [ H: Permutation [?a] ?L  |- _] => apply Permutation_length_1_inv in H
 | [ H: Permutation ?L [?a] |- _] => symmetry in H; apply Permutation_length_1_inv in H
 | [ H: Permutation [?a] [?b]  |- _] => apply Permutation_length_1 in H
 
 (* About Lists *)

(*  | [ H: In _ [_] |- _ ] => 
        let newH := fresh "H" in inversion H as [newH | newH];[subst| inversion newH]    *) 
 | [ H: ?A ++ ?B = nil |- _ ] => 
        apply app_eq_nil in H; destruct H
 | [ H: nil =  ?A ++ ?B |- _ ] => 
      symmetry in H; apply app_eq_nil in H; destruct H
 | [ H: ?A ++ ?B = [_] |- _ ] => 
        apply app_eq_unit in H; decompose [and or] H;clear H
 | [ H: [_] = ?A ++ ?B |- _ ] => 
        symmetry in H; apply app_eq_unit in H; decompose [and or] H;clear H
        
 | [ H: Remove _ [_] _ |- _ ] =>  apply RemoveUnique in H 
end;subst.


Ltac sauto := subst; (* after an inversion *) 
              simplifier; clean_goal;
              try solve [strivial]; 
              clear_junk; auto.

(* Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.
Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
   |- _ ⇒ rewrite (H1 X H2) in x
  end.
 *) 
        
Ltac checkPermutationCases H := simpl in H;
 let Hs := type of H in 
  match Hs with
  | Permutation (?P1::?L1) (?P2::?L2) => apply PProp_perm_select in H;sauto
  | Permutation  (?L1++?L2) (?L3++?P::nil) => symmetry in H;apply PProp_perm_sel in H;sauto
  | Permutation (?L3++?P::nil) (?L1++?L2) => apply PProp_perm_sel in H;sauto
  | Permutation  (?L1++?L2) (?P::?L3) => apply PProp_perm_select' in H;sauto
  | Permutation (?P::?L3) (?L1++?L2) => symmetry in H;apply PProp_perm_select' in H;sauto
end.

