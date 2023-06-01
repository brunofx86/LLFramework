Require Export LL.FOLL.Syntax.
Export ListNotations.
Set Implicit Arguments.

Create HintDb LLBase.

Section FLLSyntax.
  Context `{OLS: OLSig}.
  
  Inductive Arrow  := 
  | UP (l : list oo) (* negative phase *)
  | DW (F : oo). (* positive phase *)

  (** Transforming arrows into lists of formulas *)
  Definition Arrow2LL (A: Arrow) : list oo :=
    match A  with
    | UP l => l
    | DW F => [F]
    end.

  (** Checking when a formula has to lose focusing *)
  Inductive negFormula : oo -> Prop :=
  | RelNA1 : forall A,  negFormula (atom A)
  | RelTop : negFormula Top
  | RelBot : negFormula Bot
  | RelPar : forall F G, negFormula (MOr F G)
  | RelWith : forall F G, negFormula (AAnd F G)
  | RelQuest : forall F, negFormula (Quest F)
  | RelForall : forall FX, negFormula (All FX).

  (** Checking whether focusing persists *)
  Inductive posFormula : oo -> Prop :=
  | PosAt : forall A,  posFormula (perp A)
  | PosOne : posFormula One
  | PosZero : posFormula Zero
  | PosTensor : forall F G, posFormula (MAnd F G)
  | PosPlus : forall F G, posFormula (AOr F G)
  | PosBang : forall F, posFormula (Bang F)
  | PosEx : forall FX, posFormula (Some FX).

  (** Checking when a formulas has to be stored *)
  Inductive posLFormula : oo -> Prop :=
  | PosLAt : forall A,  posLFormula (atom A)
  | PosLPe : forall A,  posLFormula (perp A)
  | PosLOne : posLFormula One
  | PosLZero : posLFormula Zero
  | PosLTensor : forall F G, posLFormula (MAnd F G)
  | PosLPlus : forall F G, posLFormula (AOr F G)
  | PosLBang : forall F, posLFormula (Bang F)
  | PosLEx : forall FX, posLFormula (Some FX).

  Lemma posPosL : forall F,
      posFormula F -> posLFormula F.
 Proof.  intros. inversion H;constructor. Qed.
  
  (** Every formula is either a positive formula, or it must be negative formula *)
  Lemma posOrNeg : forall F,
      posFormula F \/ negFormula F.
   Proof. intros. destruct F;try (left;constructor);try(right;constructor). Qed.

  Lemma PosNegSplit : forall M, exists M1 M2, 
    Forall posFormula M1 /\ Forall negFormula M2 /\ Permutation M (M1++M2).
  Proof with sauto. 
    induction M; intros...
    - exists nil, nil... 
    - destruct (posOrNeg a).
      { exists (a::x), x0... 
        rewrite H2... }
      { exists x, (a::x0)...
        rewrite H2... }
  Qed.      

  (** Positive formulas cannot be negFormulad *)
  Lemma posNotNeg: forall F,
      posFormula F -> ~ negFormula F.
  Proof.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.

  Lemma negNotPos : forall F,
      negFormula F -> ~ posFormula F.
  Proof.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.
  
  (** The dual of a positive formula is a negFormula formula *)
  Lemma posDualNeg : forall F,
      posFormula F -> negFormula (dual F).
  Proof.
    intros F Hpos. inversion Hpos;subst;constructor.
  Qed.

  Lemma negDualPos : forall F, negFormula F -> posFormula (dual F).
  Proof.
    intros F Hrel. inversion Hrel;subst;constructor.
  Qed.
  
  (** Atoms *)
  Inductive posAtom : oo -> Prop :=
  | IsPAP : forall A, posAtom (atom A).

  (** Negated atoms *)
  Inductive negAtom : oo -> Prop :=
  | IsNAP : forall A, negAtom (perp A).

  Lemma negAtomDec : forall F,
      negAtom F \/ ~ negAtom F.
  Proof.
    induction F;auto; try solve[right;intro H'; inversion H'].
    left;constructor.
  Qed.

  Lemma posAtomDec : forall F,
      posAtom F \/ ~ posAtom F.
    induction F;auto; try solve[right;intro H'; inversion H'].
 Proof.
    left;constructor.
  Qed.

Lemma posLDestruct :
    forall F, posLFormula F -> posFormula F \/ posAtom F.
 Proof.
    intros.
    inversion H;auto; first [left;constructor
                             | right;constructor ].
  Qed.

Lemma posAtomNeg : forall F,
      posAtom F -> negFormula F.
 Proof.
    intros. inversion H;constructor.
  Qed.
 
Lemma negAtomPos : forall F,
      negAtom F -> posFormula F.
Proof.
    intros. inversion H;constructor.
  Qed.
 
Lemma posAtomPosL : forall F,
      posAtom F -> posLFormula F.
 Proof.
    intros. inversion H;constructor.
  Qed.

  (** Negative Formula without literals *)
  Inductive negFormula' : oo -> Prop :=
  | RelTop' : negFormula' Top
  | RelBot' : negFormula' Bot
  | RelPar' : forall F G, negFormula' (MOr F G)
  | RelWith' : forall F G, negFormula' (AAnd F G)
  | RelQuest' : forall F, negFormula' (Quest F)
  | RelForall' : forall FX, negFormula' (All FX).

 Lemma posLOrNeg' : forall F,
      posLFormula F \/ negFormula' F.
 Proof.
    intros.  destruct F;try (left;constructor);try(right;constructor).
  Qed.

   Lemma posLNegSplit : forall M, exists M1 M2, 
    Forall posLFormula M1 /\ Forall negFormula' M2 /\Permutation M (M1++M2).
  Proof with sauto. 
    induction M; intros...
    - exists nil, nil...
    - destruct (posLOrNeg' a).
      { exists (a::x), x0... 
        rewrite H2... }
      { exists x, (a::x0)... 
        rewrite H2... }
  Qed.      
  
 End FLLSyntax.

Global Hint Constructors 
    negFormula 
    posFormula
    posLFormula 
    uniform_oo isFormula posAtom
    negAtom: core.
    
Global Hint Resolve 
     posPosL
     posAtomNeg
     posAtomPosL
     negAtomPos : core.    

Global Hint Unfold isFormulaL :core.