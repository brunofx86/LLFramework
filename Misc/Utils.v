(** * Utils *)
(** Common definitions including:
 -  theorems about lists and permutation.  
 -  the induction scheme for Strong Induction
 -  some arithmetic results (specially dealing with [max] and [min])
 *)

Require Export Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Export Coq.Lists.List.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Arith.Arith.
Require Export Coq.Init.Nat.
Require Import Lia.
Require Export  LL.Misc.Hybrid.

Export ListNotations.

Set Implicit Arguments.

(** ** External definitions for the Object Logic (OL)
The class [OLSig] specifies the external definitions for terms and
atomic propositions of the object logic. The syntax is parametric on:

 - [atm] : type for atomic propositions (judgments at the Object Logic level)
 - [con] : type for syntactic constructors at the OL level
 - [uniform_atm] : predicate ruling out exotic terms at the OL level
 *)

Class OLSig :=
  {
    (* Signature for atoms (judgments at the OL level) *)
    atm:Set; 
    (* Type for constants (constructors for OL syntax) *)
    con:Set; 
    (* predicate ruling out exotic terms for atoms *)
    uniform_atm : (expr con -> atm) -> Prop
  }.

Ltac solveUniform :=
  auto;
  repeat 
    match goal with
    | [|- uniform _ ] => eauto 10  using uniform_id, uniform_con, uniform_app, proper_uniform, abstr_lambda
    | [|- uniform_atm _ ] => constructor
    | [|- proper _ ] => constructor
    | [|- level _ _ ] => constructor
    end.


Lemma NatComp : forall x y, x >= y + 1 -> S x - y - 2 = x - y - 1.
Proof with subst;auto. lia.
Qed.  

Section ForAllMap. 
  
Lemma ForallIn :  forall {A : Type} {F : A} {L : list A} (f : A -> Prop), 
      Forall f L -> In F L -> f F. 
  Proof.
    intros.
    generalize (Forall_forall f L );intro.
    destruct H1.
    apply H1 with (x:= F) in H ;auto.
  Qed.
  
Lemma ForallInP : forall {A : Type} {F : A} {L L': list A} (f : A -> Prop), 
      Forall f L -> Permutation L (F::L') -> f F. 
  Proof.
    intros.
    eapply @ForallIn with (F:=F) in H;auto.
    rewrite H0.
    simpl;auto.
  Qed.
  
  
  
End ForAllMap .
  
  
(** ** Operations on lists/multisets *)
Section MultisetOperations.
  Variable T:Type.

  (** removing an element from a list *)
  Inductive Remove :T -> list T -> list T -> Prop :=
  | Remove1: forall t l, Remove t (t::l) l
  | Remove2: forall t t' l1 l2,  Remove t l1 l2 -> Remove t (t'::l1) (t'::l2).
  
End MultisetOperations.

Global Hint Constructors Remove : core .


(** ** Additional results about permutations *)
Section Permutations.

  Variable A:Type.

Lemma ListConsApp (a b: A) : forall L M , a :: L = M ++ [b] -> 
       (L=[]/\M=[]/\a=b) \/ exists X, M = a :: X /\ L = X++[b].
Proof with subst;auto.
  induction M; intros...
  * inversion H...
  * rewrite <- app_comm_cons in H. 
    inversion H;subst...
    right.
    exists M...
 Qed.   
 
 Lemma ListConsApp' (a b: A) : forall L M1 M2 , a :: L = M1 ++ [b] ++ M2 -> 
        (L=M2/\M1=[]/\a=b) \/ 
       exists X, M1 = a :: X /\ L = X++[b]++M2.
Proof with subst;auto.
  destruct M1;intros...
  * inversion H;subst...
  * rewrite <- app_comm_cons in H. 
    inversion H;subst...
    right.
    exists M1...
 Qed. 

  Lemma ListConsApp'' (a : A) M1: forall L M2 , a :: L = M1 ++ M2 -> 
       (M1=[ ]/\M2=a::L) \/ 
       exists X, M1 = a :: X /\ L = X++M2.
Proof with subst;auto.
  induction M1;intros...
  rewrite <- app_comm_cons in H. 
   inversion H;subst...
   right.
   exists M1... 
 Qed. 

 Lemma ListConsApp1 (a b: A) : forall L M1 M2 , L++[a] = M1 ++ [b] ++ M2 -> 
        (L=M1/\M2=[]/\a=b) \/ 
       exists X, M2 = X++[a] /\ L = M1++[b]++X.
Proof with subst;auto.
  intros.
  revert dependent M1.
  revert a b L.
  
  induction M2;intros...
  * inversion H;subst...
    left... apply app_inj_tail in H1... 
    firstorder.
  * right.
    assert(L ++ [a0] = (M1 ++ [b]) ++ [a] ++ M2).
    rewrite app_assoc in H...
    apply IHM2 in H0.
    destruct H0...
    destruct H0...
    destruct H1...
    
    exists nil...
    
    destruct H0...
    destruct H0...
    exists (a::x)...
    firstorder.
    assert(M1 ++ [b] ++ a :: x ++ [a0]=(M1 ++ [b] ++ a :: x) ++ [a0]).
    
   
    rewrite app_assoc_reverse...
    simpl.
    rewrite app_assoc_reverse...
    Qed.
 

  Lemma ListConsApp3 (a : A) M1: forall L M2 , M1 ++ M2 = L ++ [a] -> 
       (M2=[ ]/\M1=L++[a]) \/ 
       exists X, M2 = X++[a] /\ L = M1++X.
Proof with subst;auto.
  induction M2;intros...
  left... firstorder.
  rewrite app_nil_r in H...
  right.
  symmetry in H.
  apply ListConsApp1 in H...
  destruct H...
  destruct H...
  destruct H0...
  exists nil... firstorder.
  rewrite app_nil_r...
  destruct H...
  destruct H...
  exists (a0::x)... 
 Qed. 

       
  Lemma Perm_swap_inv : forall (x y : A) (N M : list A),
      Permutation (x :: N) (y :: x :: M) ->
      Permutation N ( y :: M).
    intros.
    rewrite perm_swap in H.
    apply Permutation_cons_inv in H;auto.
  Qed.

  Lemma Perm_swap_inv_app : forall y N M (x : A) ,
      Permutation (x :: N) (y ++ x :: M) ->
      Permutation N ( y ++ M).
    intros.
    rewrite  (Permutation_cons_append M x) in H.
    rewrite  Permutation_cons_append in H.
    rewrite app_assoc in H.
    rewrite  <- Permutation_cons_append in H.
    rewrite  <- (Permutation_cons_append (y ++ M) x ) in H.
    apply Permutation_cons_inv in H;auto.
  Qed.

  Theorem PermutConsApp: forall (a : A) l1 b l2,
      Permutation (a :: l1 ++ b :: l2) (b :: a :: l1 ++ l2).
    intros.
    rewrite perm_swap.
    rewrite <- Permutation_middle.
    auto.
  Qed.

  Lemma PermutationInCons : forall (F:A) M N,
      Permutation (F::M) N -> In F N.
    intros.
    eapply Permutation_in with (x:= F) (l':=N);eauto.
    constructor;auto.
  Qed.


  (** A slightly different version of  [Permutation_map] *)
  Lemma PermuteMap : forall (L L' : list A) (f: A->Prop),
      Forall f L -> Permutation L L'-> Forall f L'.
    intros.
    apply Permutation_sym in H0.
    assert(forall x, In x L' -> In x L) by eauto using Permutation_in.
    rewrite Forall_forall in H.
    rewrite Forall_forall;intros.
    firstorder.
  Qed.

(* Permutation_app_inv *)
  Lemma Permutation_mid : forall (F:A) l1 l2 l1' l2', 
      Permutation (l1 ++ F :: l2) (l1' ++ F :: l2') ->
      Permutation (l1 ++ l2) (l1' ++ l2').
    intros.
    assert(Permutation (F::l2) (l2 ++ [F]))
      by  apply Permutation_cons_append.
    rewrite H0 in H.
    assert(Permutation (F::l2') (l2' ++ [F]))
      by  apply Permutation_cons_append.
    rewrite H1 in H.
    apply Permutation_app_inv_r with (l:= [F]).
    do 2 rewrite app_assoc_reverse;auto.
  Qed.
  
 (* perm_takeit_5 *)
  Lemma Permutation_midle : forall  (F:A) l1 l2,
      Permutation (l1 ++ F :: l2) ( F :: l1  ++ l2).
    intros.
    generalize (Permutation_cons_append  l1 F);intro.
    change (F::l1++l2) with ( (F::l1) ++ l2).
    rewrite H.
    assert(l1 ++ F :: l2 = (l1 ++ [F]) ++ l2).
    rewrite app_assoc_reverse;auto.
    rewrite H0.
    auto.
  Qed.


(* Permutation_app_swap_app *)
  Lemma Permutation_midle_app : forall  (la lb lc: list A),
      Permutation (la ++ lb ++ lc) ( lb ++ la  ++ lc).
    intros.
    rewrite <- app_assoc_reverse. 
    rewrite Permutation_app_comm with (l:=la).
    rewrite app_assoc_reverse;auto.
  Qed.


  Lemma InPermutation : forall (l:A) L,
      In l L -> exists L', Permutation L (l :: L').
    induction L;intros.
    inversion H.
    inversion H;subst.
    exists L;auto.
    apply IHL in H0.
    destruct H0 as [L' H0].
    exists (a :: L').
    rewrite H0.
    constructor.
  Qed.
  

End Permutations.

(** ** Properties about [Remove] *)
Section Remove.
  Variable A:Type.
  
  Lemma Remove_In  : forall (F: A) (L L' :list A),
      Remove F L L' -> In F L.
  Proof.    
    induction L;intros.
    + inversion H.    
    + inversion H;subst.
      ++ constructor;auto.
      ++ apply IHL in H4.
         right;auto.
  Qed.

  Lemma In_Remove  : forall (F: A) (L :list A),
      In F L -> exists L', Remove F L L'.
  Proof.    
    induction L;intros.
    + inversion H. 
    + inversion H;subst.
      ++ exists L.
         constructor.
      ++ apply IHL in H0.
         destruct H0 as [L'].
         exists (a::L').
         constructor;auto.
  Qed.

  Lemma RemoveUnique : forall (F G:A) L,
      Remove F [G] L -> F = G.
  Proof.    
    intros.
    apply Remove_In in H.
    inversion H;auto.
    inversion H0.
  Qed.

  Lemma Remove_app_head : forall (F:A) L1 L1' L2,
      Remove F L1 L1' -> Remove F (L2 ++ L1) (L2 ++ L1').
  Proof.    
    induction L2;intros;auto.
    apply IHL2 in H.
    change ((a :: L2) ++ L1) with (a :: (L2 ++ L1)) .
    change ((a :: L2) ++ L1') with (a :: (L2 ++ L1')) .
    apply Remove2;auto.
  Qed.

  Lemma Remove_app_in : forall (F:A) L1 L2,
      Remove F (L1 ++ F :: L2) (L1 ++ L2).
  Proof.    
    intros.
    apply Remove_app_head.
    constructor.
  Qed.

  Lemma Remove_head: forall (F:A) L1 L,
      Remove F (F :: L1) L ->
      L = L1 \/ (exists l1, L = F::l1 /\ Remove F L1 l1).
  Proof.    
    intros.
    inversion H;subst;auto.
    right.
    exists l2;auto.
  Qed.

  Lemma Remove_inv: forall (F:A) a L L1,
      Remove F L (a :: L1) ->
      exists b1 b2 L2, L = b1 :: b2 :: L2 /\
                       ( ( b1=F /\ a::L1 = b2::L2) \/
                         (a=b1 /\ Remove F (b2::L2) L1) ) .
  Proof with subst.
    intros.
    revert dependent L1.
    revert dependent a.
    revert dependent F.
    induction L;intros ...
    + inversion H.
    + inversion H ...
      repeat eexists;auto.
      destruct L1.
      ++  inversion H2 ...
          repeat eexists;auto.
      ++ apply IHL in H2.
         destruct H2 as [b1 [b2 [ L2 [H2 H2']]]].
         destruct H2'.
         +++ inversion H2 ...
             repeat eexists;auto.
             right; firstorder ...
             inversion H2...
             constructor.
         +++ destruct H0 ...
             repeat eexists;auto.
  Qed.

  Lemma Remove_inv_cons: forall (F:A) a L L1,
      Remove F (a::L) L1 ->
      (F =a /\ L = L1) \/
      (exists L1', L1 = a::L1' /\ Remove F L L1') .
  Proof.    
    intros.
    inversion H;subst.
    + left;auto.
    + right.
      eexists.
      eauto.
  Qed.

End Remove.


(** ** Preperties relating [Remove] and [Permutation] *)
Section RemovePermutation.
  Variable A:Type.
  
  Lemma Remove_Permutation_Ex  : forall (F : A) (L L' M : list A),
      Remove F L L' -> Permutation L M -> exists M', Remove F M M'.
  Proof.     
    intros.
    apply Remove_In in H as Hrm.
    destruct L.
    + inversion Hrm.
    + assert(In F M).
      eapply Permutation_in;eauto.
      apply In_Remove;auto.
  Qed.

  Lemma Remove_upto_permute : forall (F:A) L1 L2 L,
      Remove F L L1 -> Remove F L L2 ->  Permutation L1 L2.
  Proof with subst.
    intros.
    revert dependent L1.
    revert dependent L2.
    induction L;intros.
    +  inversion H.
    + apply Remove_inv_cons in H as H'.
      apply Remove_inv_cons in H0 as H0'.
      destruct H';destruct H0'.
      ++ firstorder;subst;auto. (* case both took the first element *)
      ++ firstorder...
         apply Remove_In in H4 as H4'.
         apply In_Remove in H4'.
         destruct H4'.
         assert (Permutation x x0) by  (eapply IHL;eauto).
         apply Remove_In in H1 as H1'.
         apply in_split in H1'.
         firstorder ...
         assert (Remove a (x1 ++ a :: x2) (x1++x2)) by apply Remove_app_in.
         generalize (IHL x0 H1 (x1++x2) H3);intro.
         assert (Permutation  (a:: x1 ++ x2) (x1 ++a :: x2) ) by  apply Permutation_middle.
         rewrite <- H6.
         constructor.
         rewrite H5.
         rewrite H2.
         auto.
      ++ firstorder...
         apply Remove_In in H4 as H4'.
         apply In_Remove in H4'.
         destruct H4'.
         assert (Permutation x x0) by  (eapply IHL;eauto).
         apply Remove_In in H1 as H1'.
         apply in_split in H1'.
         firstorder ...
         assert (Remove a (x1 ++ a :: x2) (x1++x2)) by apply Remove_app_in.
         generalize (IHL x0 H1 (x1++x2) H3);intro.
         assert (Permutation  (a:: x1 ++ x2) (x1 ++a :: x2) ) by  apply Permutation_middle.
         rewrite <- H6.
         constructor.
         rewrite H5.
         rewrite H2.
         auto.
      ++ firstorder;subst.
         generalize (IHL x0 H4 x H3);intro.
         constructor;auto.
  Qed.
    

  Lemma Remove_permute : forall (F:A) L1 L2 L,
      Remove F (L1 ++ F :: L2) L -> Permutation (L1 ++ L2) L.
  Proof.    
    intros.
    assert(Remove  F (L1 ++ F :: L2) (L1 ++ L2)) by  apply Remove_app_in.
    eapply Remove_upto_permute;eauto.
  Qed.

  Lemma Remove_app_tail : forall (F:A) L1 L1' L2,
      Remove F L1 L1' -> Remove F (L1++L2) (L1'++L2).
  Proof.    
    intros. induction H.
    *
      apply Remove1.
    *
      change ((t' :: l1) ++ L2) with (t' ::(l1 ++ L2)).
      change ((t' :: l2) ++ L2) with (t' ::(l2 ++ L2)).
      apply Remove2;auto.
  Qed.

  Lemma Remove_Permutation_Ex2  : forall (F : A) (L L' M : list A),
      Remove F L L' -> Permutation L M ->
      exists M', Remove F M M'  /\ Permutation M' L'.
  Proof.    
    intros.
    assert(HFL: In F L) by eauto using Remove_In.
    assert(HFM: In F M).
    { apply Permutation_in with (x:=F) in H0; auto; constructor;auto. }
    apply In_nth_error in HFL as HFL'.
    destruct HFL' as [n  HFL'].
    apply nth_error_split in HFL'.
    destruct HFL' as [l1 [l2 [HFL' HFL''] ]];subst.
    apply In_nth_error in HFM as HFM'.
    destruct HFM' as [n  HFM'].
    apply nth_error_split in HFM'.
    destruct HFM' as [l1' [l2' [HFM' HFM''] ]];subst.
    exists (l1' ++ l2').
    split.
    + apply Remove_app_head.
      constructor.
    + apply Remove_permute in H.
      apply Permutation_mid in H0.
      rewrite <- H0.
      rewrite H.
      auto.
  Qed.

  Lemma Remove_Permute : forall (F : A) (L L' M : list A),
      Remove F L L' -> Permutation L (F :: L').
  Proof.    
    induction L;intros.
    inversion H.
    apply Remove_inv_cons in H.
    firstorder;subst.
    constructor;auto.
    assert(Permutation (F::a::x) (a :: F ::x)).
    constructor.
    rewrite H.
    constructor.
    apply IHL;auto.
  Qed.

 Variable B:Type.
 
  Lemma Remove_Map : forall (F : A) (L L' : list A) (f: A -> B),
      Remove F L L' -> Remove (f F) (map f L) (map f L').
  Proof.    
    induction L;intros.
    inversion H.
    simpl...
    apply Remove_inv_cons in H.
    firstorder;subst.
    simpl...
    constructor;auto.
    simpl...
    constructor;auto.
  Qed.


End RemovePermutation.


(** ** Strong Induction *)

Section StrongIndPrinciple.

  Variable P: nat -> Prop.

  Hypothesis P0: P O.

  Hypothesis Pn: forall n, (forall m, m<=n -> P m) -> P (S n).

  Lemma strind_hyp : forall n, (forall m, ((m <= n) -> P m)).
  Proof.
    induction n; intros m H;inversion H;auto.
  Qed.
  (** Strong induction principle *)
  Theorem strongind: forall n, P n.
  Proof.
    induction n; auto.
    apply Pn.
    apply strind_hyp.
  Qed.

End StrongIndPrinciple.


(** ** Aditional results on Arithmentic *)
Section Arithmentic.

  Lemma MaxPlus : forall a b, (Nat.max a b <= plus a  b).
    intros;lia.
  Qed.
  
  Lemma MaxPlus' : forall a b c, (plus a b <= c -> Nat.max a b <= c).
    intros;lia.
  Qed.
  
  
  Theorem GtExists : forall n, n>0 -> exists n', n = S n'.
    intros.
    destruct n;inversion H;subst;eauto.
  Qed.

End Arithmentic.

Ltac mgt0 := let H := fresh "H" in
             match goal with [_ :  ?m >= S _ |- _] =>
                             assert(H : m>0) by lia;
                             apply GtExists in H;
                             destruct H;subst
             end.


Section Pairs.

Variable S:Type. (* SubExps *)
Variable F:Type. (* Formulas *)


(* fst (split L) *)
Definition first (L:list (S * F)) :=  map fst L.
(* snd (split L) *)
Definition second (L:list (S * F)) := map snd L.

Lemma secondPerm C1 C2 : Permutation C1 C2 -> Permutation (second C1)  (second C2).
Proof with subst;auto.
  intros; apply Permutation_map... Qed.
         
Lemma secondApp C1 C2 : second (C1 ++ C2) = second C1 ++ second C2.
Proof.
  induction C1;simpl.
  reflexivity.
  rewrite IHC1.
  reflexivity. Qed.

Lemma firstApp C1 C2 : first (C1 ++ C2) = first C1 ++ first C2.
Proof.
  induction C1;simpl.
  reflexivity.
  rewrite IHC1.
  reflexivity. Qed.

Lemma InFirst c B : In c B -> In (fst c) (first B). 
Proof.
 induction B;intros;auto.
 unfold second.
 inversion H;subst;auto;
 simpl;auto.
 Qed.
 
Lemma InSecond c B : In c B -> In (snd c) (second B). 
Proof.
 induction B;intros;auto.
 unfold second.
 inversion H;subst;auto;
 simpl;auto.
 Qed.
 
 Lemma InSecondInv i A B : In (i,A) B -> In A (second B). 
Proof.
 induction B;intros;auto.
 inversion H;subst;auto;
 simpl;auto.
 Qed.
 
 End Pairs.

   
