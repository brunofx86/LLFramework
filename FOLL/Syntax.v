
Require Export LL.Misc.Utils.
Require Export LL.Misc.Hybrid.
Require Export LL.Misc.UtilsTactics.
Require Export Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RelationClasses.
Require Import Coq.Logic.FinFun.


Export ListNotations.
Set Implicit Arguments.

Section LLSyntax.
  Context `{OLS: OLSig}.
  
  (** Connectives of the logic *)
  Inductive oo : Set :=
  | atom : atm -> oo
  | perp : atm -> oo
  | Top : oo
  | One : oo
  | Zero : oo
  | Bot : oo 
  | AAnd : oo -> oo -> oo
  | MAnd : oo -> oo -> oo
  | AOr : oo -> oo -> oo
  | MOr : oo -> oo -> oo 
  | Bang : oo -> oo
  | Quest : oo -> oo 
  | All : (expr con -> oo) -> oo 
  | Some : (expr con -> oo) -> oo.


   
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
    | Some FX => 1+ complexity (FX (VAR con 0))
    | All FX => 1+ complexity (FX (VAR con 0))
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
    | Some X => All (fun x => dual  (X x))
    | All X => Some (fun x => dual (X x))
    end.


 
 (** Negation is involutive *)
  Theorem ng_involutive: forall F: oo, F = dual (dual F).
  Proof.
    intro. 
    induction F; simpl; auto;
      try( try(rewrite <- IHF1); try(rewrite <- IHF2); try(rewrite <- IHF);auto);
      try(assert (o = fun x =>  dual (dual (o x))) by
             (extensionality e; apply H); rewrite <- H0; auto).
  Qed.
 
  Lemma DualComplexity F: complexity F = complexity (dual F) .
 Proof with sauto.
  induction F...
  all: try solve [simpl;sauto].
  Qed.


Lemma dualSubst F C : F = dual C -> C = dual F.
Proof.
  intros.
  rewrite H. rewrite <- ng_involutive;auto. Qed.

Lemma dualInj : Injective dual.
Proof with subst;auto.
 intros A B H.
 apply dualSubst in H...
 apply ng_involutive.
Qed.

  
  (** Uniform Predicate (ruling out exotic terms) *)
  Inductive uniform_oo: (expr con -> oo) -> Prop := 
  | uniform_atom: forall (a: expr con -> atm),
      uniform_atm a -> uniform_oo (fun x => (atom (a x)))
  | uniform_perp: forall (a: expr con -> atm),
      uniform_atm a -> uniform_oo (fun x => (perp (a x)))
  | uniform_Top: uniform_oo (fun x => Top)
  | uniform_One: uniform_oo (fun x => One)
  | uniform_Bot: uniform_oo (fun x => Bot)  
  | uniform_Zero: uniform_oo (fun x => Zero)
  | uniform_AAnd: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (AAnd (A x) (B x)))
  | uniform_MAnd: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (MAnd (A x) (B x)))
  | uniform_AOr: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (AOr (A x) (B x)))
  | uniform_MOr: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (MOr (A x) (B x))) 
  | uniform_Bang: forall (A: expr con -> oo),
      uniform_oo A -> uniform_oo (fun x => (Bang (A x)))
  | uniform_Quest: forall (A: expr con -> oo), 
      uniform_oo A -> uniform_oo (fun x => (Quest (A x)))
  | uniform_All: forall (A: expr con -> expr con -> oo),
      (forall y:expr con, uniform_oo (fun x => (A y x))) ->
      uniform_oo (fun x => (All (fun y => (A y x))))
  | uniform_Some: forall (A: expr con -> expr con -> oo),
      (forall y:expr con, uniform_oo (fun x => (A y x))) ->
      uniform_oo (fun x => (Some (fun y => (A y x)))).

 
  Lemma ComplexityUniformEq : forall FX x y , uniform_oo FX ->
                                            proper x -> proper y ->
                                            complexity (FX x) =  complexity (FX y).
    intros.
    induction H;subst;simpl;firstorder.
  Qed.

 (** Well formedness condition  *)
  Inductive isFormula: oo -> Prop  :=
  | wf_atm : forall (P1:atm), isFormula (atom P1)
  | wf_perp : forall (P1:atm), isFormula (perp P1)
  | wf_Top : isFormula Top
  | wf_One : isFormula One
  | wf_Zero : isFormula Zero
  | wf_Bot : isFormula Bot
  | wf_AAnd : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (AAnd A1 A2)
  | wf_MAnd : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (MAnd A1 A2)
  | wf_AOr : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (AOr A1 A2)
  | wf_MOr : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (MOr A1 A2)
  | wf_Bang : forall (A1 :oo), isFormula A1 -> isFormula (Bang A1)
  | wf_Quest : forall (A1 :oo), isFormula A1 -> isFormula (Quest A1)
  | wf_All : forall (A : expr con -> oo), uniform_oo A -> (forall t: expr con, isFormula (A t)) -> isFormula (All A)
  | wf_Some : forall (A : expr con -> oo), uniform_oo A -> (forall t: expr con, isFormula (A t)) -> isFormula (Some A).
  
  (** Well formendness conditions for lists and arrows *)
  Definition isFormulaL  (L:list oo)  := Forall isFormula L. 
 
  Lemma isFormulaIn F L: 
      isFormulaL L -> In F L -> isFormula F. 
  Proof.
    intros.
    eapply @ForallIn with (F:=F) in H;auto.
  Qed.


Lemma isFormulaInP F L L': 
      isFormulaL L -> Permutation L (F::L') -> isFormula F. 
  Proof.
 intros.
    eapply @ForallInP with (F:=F) in H;auto.
  Qed.
 
 
  Generalizable All Variables.
  Global Instance isFormulaL_morph : 
    Proper ((@Permutation oo) ==> Basics.impl) (isFormulaL).
  Proof.
    unfold Proper; unfold respectful; unfold Basics.impl.
    intros.
    unfold isFormulaL.
    rewrite <- H;auto.
  Qed.  

 
End LLSyntax.

Global Hint Constructors uniform_oo isFormula: core.
Global Hint Resolve Complexity0
                    DualComplexity: core.

Global Hint Unfold isFormulaL :core.

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
  Notation " A ^ " := (dual A) (at level 10) .
  Notation "'∀{' FX '}'" := (All FX) (at level 10) .
  Notation "'∃{' FX '}'" := (Some FX) (at level 10) .
End LLNotations .
