
Require Export LL.Misc.Utils.
Require Export LL.Misc.UtilsTactics.
Require Export Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RelationClasses.
Require Import Coq.Logic.FinFun.


Export ListNotations.
Set Implicit Arguments.

Section LLSyntax.
  
  (** Connectives of the logic *)
  Inductive oo : Set :=
  | atom : nat -> oo
  | perp : nat -> oo
  | Top : oo
  | One : oo
  | Zero : oo
  | Bot : oo 
  | AAnd : oo -> oo -> oo
  | MAnd : oo -> oo -> oo
  | AOr : oo -> oo -> oo
  | MOr : oo -> oo -> oo 
  | Bang : oo -> oo
  | Quest : oo -> oo .
  
  (** Complexity of formulas *)
  Fixpoint complexity (X:oo) :=
    match X with
    | atom A   => 1
    | perp A   => 1
    | One => 1
    | Bot => 1
    | Zero => 1
    | Top => 1
    | MAnd F G => 1+ complexity F + complexity G
    | AAnd F G => 1+ complexity F + complexity G
    | MOr F G => 1+ complexity F + complexity G
    | AOr F G => 1+ complexity F + complexity G
    | Bang F   => 1+ complexity F
    | Quest F  => 1+ complexity F
    end.
    
  (** Complexity on list of formulas *)
  Fixpoint complexityL (L: list oo) :=
    match L with
    | nil => 0
    | a :: L' => complexity a + complexityL L'
    end.

  Lemma Complexity0 : forall F, complexity F > 0.
    induction F;simpl;lia.
  Qed.

  Lemma ComplexityL0 : forall L, complexityL L =0 -> L = [].
    intros;destruct L;simpl;auto.
    simpl in H.
    generalize (Complexity0 o);intros.
    lia.
  Qed.
  
  (** Classical linear logic dualities *)
  Fixpoint dual (X: oo) :=
    match X with
    | atom A   => perp A
    | perp A   => atom A
    | One => Bot
    | Bot => One
    | Zero => Top
    | Top => Zero
    | MAnd F G => MOr (dual  F) (dual G)
    | AAnd F G => AOr (dual  F) (dual G)
    | MOr F G => MAnd (dual  F) (dual G)
    | AOr F G => AAnd (dual  F) (dual G)
    | Bang F   => Quest (dual F)
    | Quest F  => Bang (dual   F)
    end.


 
 (** Negation is involutive *)
  Lemma dualInvolutive F : F = dual (dual F).
  Proof.
  
    induction F; simpl; auto;
      try( try(rewrite <- IHF1); try(rewrite <- IHF2); try(rewrite <- IHF);auto);
      try(assert (o = fun x =>  dual (dual (o x))) by
             (extensionality e; apply H); rewrite <- H0; auto).
  Qed.
 
  Lemma dualComplexity F : complexity F = complexity (dual F) .
 Proof with sauto.
  induction F...
  all: try solve [simpl;sauto].
  Qed.


Lemma dualSubst F C : F = dual C -> C = dual F.
Proof.
  intros.
  rewrite H. rewrite <- dualInvolutive;auto. Qed.

Lemma dualInj : Injective dual.
Proof with subst;auto.
 intros A B H.
 apply dualSubst in H...
 apply dualInvolutive.
Qed.

End LLSyntax.

Global Hint Resolve Complexity0
                    dualComplexity: core.

Module LLNotations .
  Notation "'⊥'" := Bot.
  Notation "'⊤'" := Top.
  Notation "'1" := One.
  Notation "'0'" := Zero.
  Notation "A ⊗ B" := (MAnd A B ) (at level 50) .
  Notation "A ⅋ B" := (MOr A B) (at level 50) .
  Notation "A ⊕ B" := (AOr A B) (at level 50) . 
  Notation "A & B" := (AAnd A B) (at level 50) .
  Notation "! A" := (Bang A) (at level 50) .
  Notation "? A" := (Quest A) (at level 50) .
  Notation " A ∘" := (dual A) (at level 10) .
End LLNotations .
