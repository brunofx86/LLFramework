Require Export LL.FOLL.Syntax.
Export ListNotations.
Set Implicit Arguments.


Create HintDb LLBase.


Section FLLSyntax.
  Context `{OLS: OLSig}.
  
  (** Arrows for the focused system
      - [UP] : negative phase
      - [DW] : positive phase 
   *)
  Inductive Arrow  := 
  | UP (l : list oo) (* negative phase *)
  | DW (F : oo). (* positive phase *)

  (** Transforming arrows into lists of formulas *)
  Definition Arrow2LL (A: Arrow) : list oo :=
    match A  with
    | UP l => l
    | DW F => [F]
    end.

  (** Checking when a formulas has to lose focusing *)
  Inductive negativeFormula : oo -> Prop :=
  | RelNA1 : forall A,  negativeFormula (atom A)
  | RelTop : negativeFormula Top
  | RelBot : negativeFormula Bot
  | RelPar : forall F G, negativeFormula (MOr F G)
  | RelWith : forall F G, negativeFormula (AAnd F G)
  | RelQuest : forall F, negativeFormula (Quest F)
  | RelForall : forall FX, negativeFormula (All FX).

  (** Positive formulas (focusing persists *)
  Inductive positiveFormula : oo -> Prop :=
  | PosAt : forall A,  positiveFormula (perp A)
  | PosOne : positiveFormula One
  | PosZero : positiveFormula Zero
  | PosTensor : forall F G, positiveFormula (MAnd F G)
  | PosPlus : forall F G, positiveFormula (AOr F G)
  | PosBang : forall F, positiveFormula (Bang F)
  | PosEx : forall FX, positiveFormula (Some FX).

  (** Checking when a formulas has to be stored *)
  Inductive positiveLFormula : oo -> Prop :=
  | PosLAt : forall A,  positiveLFormula (atom A)
  | PosLPe : forall A,  positiveLFormula (perp A)
  | PosLOne : positiveLFormula One
  | PosLZero : positiveLFormula Zero
  | PosLTensor : forall F G, positiveLFormula (MAnd F G)
  | PosLPlus : forall F G, positiveLFormula (AOr F G)
  | PosLBang : forall F, positiveLFormula (Bang F)
  | PosLEx : forall FX, positiveLFormula (Some FX).

  Theorem PositiveToLPositive : forall F,
      positiveFormula F -> positiveLFormula F.
    intros.
    inversion H;constructor.
  Qed.
  

  (** Every formula is either  a positive formula, or it must be negativeFormulad *)
  Theorem PositiveOrNegative : forall F,
      positiveFormula F \/ negativeFormula F.
    intros.
    destruct F;try (left;constructor);try(right;constructor).
  Qed.

  Theorem PositiveNegativeSplit : forall M, exists M1 M2, 
    Forall positiveFormula M1 /\ Forall negativeFormula M2 /\ Permutation M (M1++M2).
  Proof with sauto. 
    induction M; intros...
    - exists nil. 
      exists nil...
    - destruct (PositiveOrNegative a).
      { exists (a::x). 
        exists x0...
        rewrite H2... }
      { exists x. 
        exists (a::x0)...
        rewrite H2... }
  Qed.      
  

  (** Positive formulas cannot be negativeFormulad *)
  Theorem PositiveNotNegative: forall F,
      positiveFormula F -> ~ negativeFormula F.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.

  Theorem NegativeNotPositive : forall F,
      negativeFormula F -> ~ positiveFormula F.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.
  
  (** The dual of a positive formula is a negativeFormula formula *)
  Theorem PositiveDualNegative : forall F,
      positiveFormula F -> negativeFormula (dual F).
    intros F Hpos.
    inversion Hpos;subst;constructor.
  Qed.

  Theorem NegativeDualPositive : forall F, negativeFormula F -> positiveFormula (dual F).
    intros F Hrel.
    inversion Hrel;subst;constructor.
  Qed.
  
  (** Postive atoms *)
  Inductive IsPositiveAtom : oo -> Prop :=
  | IsPAP : forall A, IsPositiveAtom (atom A).

  (** Negative atoms *)
  Inductive IsNegativeAtom : oo -> Prop :=
  | IsNAP : forall A, IsNegativeAtom (perp A).

  
  Theorem NegativeAtomDec : forall F,
      IsNegativeAtom F \/ ~ IsNegativeAtom F.
    induction F;auto; try solve[right;intro H'; inversion H'].
    left;constructor.
  Qed.

  Theorem PositiveAtomDec : forall F,
      IsPositiveAtom F \/ ~ IsPositiveAtom F.
    induction F;auto; try solve[right;intro H'; inversion H'].
    left;constructor.
  Qed.

Lemma NotAsynchronousPosAtoms :
    forall F, positiveLFormula F -> positiveFormula F \/ IsPositiveAtom F.
    intros.
    inversion H;auto; first [left;constructor
                             | right;constructor ].
  Qed.

Theorem PositiveAtomToNegativeFormula : forall F,
      IsPositiveAtom F -> negativeFormula F.
    intros.
    inversion H;constructor.
  Qed.
 
Theorem NetagiveAtomToPositiveFormula : forall F,
      IsNegativeAtom F -> positiveFormula F.
    intros.
    inversion H;constructor.
  Qed.
 
Theorem PositiveAtomToPositiveLFormula : forall F,
      IsPositiveAtom F -> positiveLFormula F.
    intros.
    inversion H;constructor.
  Qed.

  (** Checking when a formulas has to lose focusing *)
  Inductive negativeFormula' : oo -> Prop :=
  | RelTop' : negativeFormula' Top
  | RelBot' : negativeFormula' Bot
  | RelPar' : forall F G, negativeFormula' (MOr F G)
  | RelWith' : forall F G, negativeFormula' (AAnd F G)
  | RelQuest' : forall F, negativeFormula' (Quest F)
  | RelForall' : forall FX, negativeFormula' (All FX).

 Theorem PositiveLOrNegative' : forall F,
      positiveLFormula F \/ negativeFormula' F.
    intros.
    destruct F;try (left;constructor);try(right;constructor).
  Qed.



   Theorem PositiveLNegativeSplit : forall M, exists M1 M2, 
    Forall positiveLFormula M1 /\ Forall negativeFormula' M2 /\Permutation M (M1++M2).
  Proof with sauto. 
    induction M; intros...
    - exists nil. 
      exists nil...
    - destruct (PositiveLOrNegative' a).
      { exists (a::x). 
        exists x0...
        rewrite H2... }
      { exists x. 
        exists (a::x0)...
        rewrite H2... }
  Qed.      
  
 End FLLSyntax.

Global Hint Constructors 
    negativeFormula 
    positiveFormula
    positiveLFormula 
    uniform_oo isFormula IsPositiveAtom
    IsNegativeAtom: core.
    
Global Hint Resolve 
     PositiveToLPositive
     PositiveAtomToNegativeFormula
     PositiveAtomToPositiveLFormula
     NetagiveAtomToPositiveFormula : core.    

Global Hint Unfold isFormulaL :core.