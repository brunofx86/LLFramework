(** * Permutations 
Some additional results about permutations. Most of the proofs in this
script where taken from #<a href="https://github.com/PrincetonUniversity/certicoq/blob/master/libraries/MyPermutations.v">
https://github.com/PrincetonUniversity/certicoq/blob/master/libraries/MyPermutations.v</a>#
 *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Lemma eq_then_Permutation: forall{A:Type} (l1 l2:list A),
    l1 = l2 -> Permutation l1 l2.
Proof.
  intros A l1 l2 H.
  rewrite H; reflexivity.
Qed.

(* Permutation_app_head *)
Lemma app_compat_perm_latter(A:Type) : forall l a1 a2:list A,
    Permutation a1 a2 -> Permutation (l++a1) (l++a2).
Proof.
  intros l a1 a2 Ha.
  induction l.
  - exact Ha.
  - apply perm_skip,IHl.
Qed.

#[global] Instance app_compat_perm(A:Type) :
  Proper (@Permutation A ==> @Permutation A ==> @Permutation A) (@app A).
Proof.
  unfold Proper,respectful.
  intros a1 a2 Ha b1 b2 Hb.
  induction Ha.
  - exact Hb.
  - apply perm_skip.
    exact IHHa.
  - apply perm_trans with ((x::y::l)++b1).
    + apply perm_swap.
    + apply perm_skip,perm_skip,app_compat_perm_latter,Hb.
  - apply perm_trans with (l'++b2); [exact IHHa1|].
    apply perm_trans with (l'++b1); [|exact IHHa2].
    apply app_compat_perm_latter,Permutation_sym,Hb.
Qed.

(* Permutation_in *)
Lemma Permutation_In_In: forall{A:Type} (x:A) (l1 l2:list A),
    Permutation l1 l2 -> In x l1 -> In x l2.
Proof.
  intros A x l1 l2 HP H.
  induction HP.
  - exact H.
  - destruct H as [H|H].
    + left.
      exact H.
    + right.
      apply IHHP,H.
  - destruct H as [H|[H|H]].
    + right.
      left.
      exact H.
    + left.
      exact H.
    + right.
      right.
      exact H.
  - apply IHHP2,IHHP1,H.
Qed.

#[global] Instance In_compat_perm(A:Type):
  Proper (eq ==> @Permutation A ==> iff) (@In A).
Proof.
  unfold Proper,respectful.
  intros x1 x2 Hx l1 l2 Hl.
  rewrite Hx; clear x1 Hx.
  split.
  - apply Permutation_In_In,Hl.
  - apply Permutation_In_In.
    symmetry.
    exact Hl.
Qed.

#[global] Instance length_compat_perm(A:Type):
  Proper (@Permutation A ==> eq) (@length A).
Proof.
  unfold Proper, respectful.
  intros LA LB HL.
  apply Permutation_length,HL.
Qed.

(* app_assoc_reverse *)
Lemma app_normalize_1:
  forall(A:Type) (l1 l2 l3:list A),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros A l1 l2 l3.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma app_normalize_2:
  forall(A:Type) (a1:A) (l2 l3:list A),
    (a1 :: l2) ++ l3 = a1 :: (l2 ++ l3).
Proof.
  intros; reflexivity.
Qed.

(* app_nil_l *)
Lemma app_normalize_3:
  forall(A:Type) (l1:list A), (nil++l1) = l1.
Proof.
  intros; reflexivity.
Qed.

Ltac app_normalize := repeat (
                          rewrite app_normalize_1 || 
                          rewrite app_normalize_2 ||
                          rewrite app_normalize_3).

(* Permutation_app_swap_app *)
Lemma perm_takeit_1:
  forall(A:Type) (target:list A) (l1 l2:list A),
    Permutation (l1 ++ (target ++ l2)) (target ++ (l1 ++ l2)).
Proof.
  intros A target l1 l2.
  eapply Permutation_app_swap_app.
 Qed.

(* Permutation_middle *)
Lemma perm_takeit_2:
  forall(A:Type) (target:list A) (a1:A) (l2:list A),
    Permutation (a1 :: (target ++ l2)) (target ++ (a1 :: l2)).
Proof.
  intros A target a1 l2.
  apply Permutation_middle.
Qed.

(* Permutation_app_comm *)
Lemma perm_takeit_3:
  forall(A:Type) (target:list A) (l1:list A),
    Permutation (l1 ++ target) (target ++ l1).
Proof.
  intros A target l1.
  apply Permutation_app_comm.
Qed.

(* Permutation_cons_append *)
Lemma perm_takeit_4:
  forall(A:Type) (target:list A) (a1:A),
    Permutation (a1 :: target) (target ++ (a1::nil)).
Proof.
  intros A target a1.
  apply Permutation_cons_append.
Qed.

(*  symmetry
     Permutation_middle *)
Lemma perm_takeit_5:
  forall(A:Type) (target:A) (l1 l2:list A),
    Permutation (l1 ++ (target :: l2)) (target :: (l1 ++ l2)).
Proof.
  intros A target l1 l2.
  symmetry.
  apply Permutation_middle.
Qed.

(* perm_swap *)
Lemma perm_takeit_6:
  forall(A:Type) (target:A) (a1:A) (l2:list A),
    Permutation (a1 :: (target :: l2)) (target :: (a1 :: l2)).
Proof.
  intros A target a1 l2.
  apply perm_swap.
Qed.

(* symmetry
    Permutation_cons_append *)
Lemma perm_takeit_7:
  forall(A:Type) (target:A) (l1:list A),
    Permutation (l1 ++ (target::nil)) (target :: l1).
Proof.
  intros A target l1.
  symmetry.
  apply Permutation_cons_append.
Qed.

(* perm_swap *)
Lemma perm_takeit_8:
  forall(A:Type) (target:A) (a1:A),
    Permutation (a1 :: (target::nil)) (target :: (a1::nil)).
Proof.
  intros A target a1.
  apply perm_swap.
Qed.

Ltac perm_simplify := app_normalize; repeat (
                                         rewrite app_nil_r ||
                                         match goal with
                                         | [ |- Permutation ?L1 ?L1 ] => reflexivity
                                         | [ |- Permutation nil nil ] => reflexivity
                                         | [ |- Permutation (?A1++_) (?A1++_) ] => apply Permutation_app_head
                                         | [ |- Permutation (?A1::_) (?A1::_) ] => apply perm_skip
                                         | [ |- Permutation _ (?L1++_) ] => (
                                             rewrite (perm_takeit_1 _ L1) at 1 ||
                                             rewrite (perm_takeit_2 _ L1) at 1 ||
                                             rewrite (perm_takeit_3 _ L1) at 1 ||
                                             rewrite (perm_takeit_4 _ L1) at 1 )
                                         | [ |- Permutation _ (?A1::_) ] => (
                                             rewrite (perm_takeit_5 _ A1) at 1 ||
                                             rewrite (perm_takeit_6 _ A1) at 1 ||
                                             rewrite (perm_takeit_7 _ A1) at 1 ||
                                             rewrite (perm_takeit_8 _ A1) at 1 )
                                         | [ |- Permutation _ _ ] => fail
                                         end).

Ltac perm := autounfold;
  match goal with
  | [ |- Permutation _ _ ] => perm_simplify; fail "perm failed"
  | [ |- _ ] => fail "perm can't solve this system."
  end.

Lemma PProp_perm_select:
  forall(A:Type) (P1 P2:A) (L1 L2:list A),
    Permutation (P1::L1) (P2::L2) ->
    (
      P1 = P2 /\ Permutation L1 L2
    ) \/ (
      exists L2',
        Permutation L2 (P1::L2') /\
        Permutation L1 (P2::L2')
    ).
Proof.
  intros A P1 P2 L1 L2 HP.
  assert (HI:=in_eq P1 L1).
  rewrite HP in HI.
  destruct HI as [HI|HI].
  - left.
    split.
    + symmetry.
      exact HI.
    + rewrite HI in HP.
      apply Permutation_cons_inv in HP.
      exact HP.
  - right.
    destruct (in_split _ _ HI) as (L2A,(L2B,HL2)).
    exists (L2A++L2B).
    split.
    + rewrite HL2.
      perm.
    + apply Permutation_cons_inv with (a:=P1).
      rewrite HP.
      rewrite HL2.
      perm.
Qed.


Lemma PProp_perm_select':
  forall(A:Type) (P:A) (L1 L2 L3:list A),
    Permutation (L1++L2) (P::L3) ->
    (exists L1', Permutation L1 (P :: L1') /\ 
                 Permutation (L1'++L2) L3) 
    \/ 
    exists L2', Permutation L2 (P :: L2') /\ 
                Permutation (L1++L2') L3 .
Proof.
  induction L1.
  - intros; right. 
    exists L3. auto.
  - intros.  
    rewrite app_normalize_2 in H.
    apply PProp_perm_select in H.
    destruct H.
    +
      destruct H;subst;left.
      exists L1. auto.
    +
      do 2 destruct H.
      apply IHL1 in H0.
      destruct H0.
      *
        do 2 destruct H0.
        left.
        exists (a::x0).
        split.
        rewrite H0.
        perm.
        rewrite H.
        rewrite <- H1.
        perm.
      *  
        do 2 destruct H0.
        right.
        exists (x0).
        split.
        rewrite H0.
        perm.
        rewrite H.
        rewrite <- H1.
        perm.
Qed.    

Lemma PProp_perm_sel:
  forall(A:Type) (P:A) (L1 L2 L3:list A),
    Permutation (L3++P::nil) (L1++L2)  ->
    (exists L1', Permutation L1 (L1'++P::nil) /\ 
                 Permutation (L1'++L2) L3) 
    \/ 
    exists L2', Permutation L2 (L2'++P::nil) /\ 
                Permutation (L1++L2') L3 .
Proof. 
  intros.
  rewrite perm_takeit_7 in H.
  symmetry in H.
  apply PProp_perm_select' in H.
  destruct H;[left;destruct H|right;destruct H].
  * exists x.
    destruct H;split;auto.
    rewrite perm_takeit_7;auto.
  * exists x.
    destruct H;split;auto.
    rewrite perm_takeit_7;auto.
Qed.

Lemma Permutation_filter: forall{A:Type} (f: A -> bool) (f_dec:forall a, {f a = true} + {f a = false})(l1 l2:list A),
   Permutation l1 l2 -> Permutation (filter f l1) (filter f l2).
Proof.
  induction l1;intros;auto.
  apply Permutation_nil in H;subst;auto.
  symmetry in H.
  assert(Permutation l2 (a :: l1)) by auto.
  apply Permutation_vs_cons_inv in H.
  do 2 destruct H.
  rewrite H.
  apply eq_then_Permutation in H.
  destruct (f_dec a).
  rewrite filter_app.
  simpl. 
  rewrite e;auto.
  rewrite perm_takeit_5.
  rewrite <- filter_app.
  apply perm_skip.
  rewrite H in H0.
  rewrite <- Permutation_middle in H0.
  
  apply Permutation_cons_inv in H0.
  symmetry in H0.
  apply IHl1 in H0.
  rewrite H0;auto.
  
  rewrite filter_app.
  simpl. 
  rewrite e;auto.
  rewrite <- filter_app.
  rewrite H in H0.
  rewrite <- Permutation_middle in H0.
  
  apply Permutation_cons_inv in H0.
  symmetry in H0.
  apply IHl1 in H0.
  rewrite H0;auto.
 Qed.


Lemma Permutation_assoc_comm: forall (T:Type) (X Y Z : list T), Permutation  ((X ++ Y) ++ Z) ((X ++ Z) ++ Y).
  intros.
  perm.
Qed.


Lemma Permutation_vs_cons_inv'
     : forall (A : Type) (l l1 : list A) (a : A),
       Permutation l (a :: l1) ->
       exists l' l'' : list A, l = l' ++ a :: l'' /\ Permutation l1 (l'++l'').
  Proof with auto.
  intros.
  assert(Permutation l (a :: l1)) by auto.
  apply Permutation_vs_cons_inv in H...
  do 2 destruct H...
  exists x, x0.
  split;auto.
  rewrite H in H0.
  symmetry in H0.
  rewrite  <- Permutation_middle in H0.
  apply Permutation_cons_inv in H0...
Qed.  
 