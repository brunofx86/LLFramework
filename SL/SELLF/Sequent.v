(** * Focused Sequent system 
This file specifies a one-sided focused system for MMLL The system is
   parametric to [theory: oo->Prop], defining the formulas that can be used in
   rule [tri_dec3]. In this implementation, all the atoms are assumed to be
   positive and then, proofs must finish with the initial rule focusing on
   atomic propositions of the form [perp A]. The exchange rule is embedded in
   the definition, e.g., of [tri_tensor]. 
 *)


Require Export LL.Misc.Utils. 
Require Export LL.SL.SELLF.Locations.

Export ListNotations.
Set Implicit Arguments.

Section LLSequent.
  Context `{SI : SigSELL}.
  Context `{OLS: OLSig}.

 
  Variable theory : oo -> Prop. (* theory Definition *)

  (* Andreoli's triadic system for linear logic *)
  Reserved Notation " n '|-F-' B ';' L ';' X " (at level 80).

  (** Sequent rules. in [n '|-F-' B ';' L ';' X], [n] is the height of
  the derivation ; [B] a list representing the classical context ; [L]
  the linear context and [X] and [Arrow] that can be [DW F] (for the
  positive phase) or [UP L] (for the negative phase). *)
  Inductive seqN:  nat -> list TypedFormula -> list oo -> Arrow -> Prop :=
  | tri_init1 : forall B A n, SetU B -> n |-F- B ; [atom A] ; DW (perp A)
  | tri_init2 : forall B C A n i, SetU C -> Permutation ((i, atom A)::C) B -> n |-F- B ; [] ; DW (perp A)
  | tri_one : forall B n, SetU B ->  n |-F- B ; [] ; DW One
  
  | tri_tensor : forall B C D BD M N MN F G n, Permutation MN (M++N) -> Permutation BD (B++C++D) -> SetU B ->
                                     SetL C -> SetL D ->
                                        (n |-F- B++C ; M ; DW F) ->
                                        (n |-F- B++D ; N ; DW G )->
                                        S n |-F- BD ; MN ; DW (MAnd F G)
                                        
  | tri_plus1 : forall B M F G n,
      n |-F- B ; M ; DW F -> S n |-F- B ; M ; DW (AOr F G)
  | tri_plus2 : forall B M F G n,
      n |-F- B ; M ; DW G -> S n |-F- B ; M ; DW (AOr F G)
  | tri_rel : forall B F L n,
      negativeFormula F -> n |-F- B ; L ; UP [F] ->  S n |-F- B ; L ; DW F
  | tri_top : forall B L M n,
      n |-F- B ; L ; UP (Top :: M)
  | tri_bot : forall B L M n,
      n |-F- B ; L ; UP M -> S n  |-F- B ; L ; UP (Bot :: M)
  | tri_par : forall B L M F G n,
      n |-F- B ; L ; UP (F::G::M) -> S n  |-F- B ; L ; UP((MOr F G) :: M)
  | tri_with : forall B L M F G n,
      (n |-F- B ; L ; UP (F :: M)) ->
      (n |-F- B ; L ; UP (G :: M)) -> S n|-F- B ; L ; UP ((AAnd F  G) :: M)
  | tri_quest : forall B L M F n i,
      n |-F- (i,F)::B ; L ; UP M -> S n  |-F- B ; L ; UP ((Quest i F) :: M)         
  | tri_store : forall B L M F n,
      positiveLFormula  F-> n |-F- B ; F::L ; UP M -> S n |-F- B ; L ; UP (F::M)
  | tri_dec1 : forall B L L' F n,
      positiveFormula F -> Permutation (F::L') L -> n |-F- B ; L' ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec2u : forall B L F n i,
     u i = true -> ~IsPositiveAtom F -> In (i,F) B -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec2l : forall B B' L F n i,
     u i = false -> ~IsPositiveAtom F -> Permutation ((i,F)::B') B -> n |-F- B' ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec3 : forall B L F n,
      theory F -> ~IsPositiveAtom F -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_ex  : forall B FX M t n,
      uniform_oo FX -> proper t -> n |-F- B; M ; DW (FX t) -> S n|-F- B; M ; DW (Some  FX)
  | tri_fx  : forall B L FX M n,
      uniform_oo FX -> (forall x, proper x -> n |-F- B ; L ; UP( (FX x) ::  M)) ->
      S n |-F- B ; L ; UP ((All FX) :: M)                                                                                                                           
  | tri_bang : forall a B F n, LtX a (getL B) ->
     n  |-F- getLtX a B ; [] ; (UP [F]) -> S n  |-F- B ; [] ; DW (Bang a F)
 
  where " n '|-F-' B ';' L ';' X " := (seqN n B L X).

   
  (** Well formedness conditions for arrows. *)
  Definition isArrow (Ar:Arrow) : Prop :=
    match Ar with
    | UP l => isFormulaL l
    | DW F => isFormula F
    end.
  
  Reserved Notation " '|-f-' B ';' L ';' X " (at level 80).

  (** The same system without the height of the derivation *)
  Inductive seq:  list TypedFormula -> list oo -> Arrow -> Prop :=
  | tri_init1' : forall B A ,  SetU B ->  |-f- B ; [atom A] ; DW (perp A)
  | tri_init2' : forall B C A i, SetU C -> Permutation ((i, atom A)::C) B -> |-f- B ; [] ; DW (perp A)
  
  | tri_one' : forall B, SetU B -> |-f- B ; [] ; DW One
  | tri_tensor' : forall M N MN B C D BD F G, Permutation MN (M++N) -> Permutation BD (B++C++D) -> SetU B ->
                                     SetL C -> SetL D ->
                                       |-f- B++C ; M ; DW F ->
                                        |-f- B++D ; N ; DW G ->
                                        |-f- BD ; MN ; DW (MAnd F G)
  | tri_plus1' : forall B M F G ,
      |-f- B ; M ; DW F -> |-f- B ; M ; DW (AOr F G)
  | tri_plus2' : forall B M F G,
      |-f- B ; M ; DW G -> |-f- B ; M ; DW (AOr F G)
  | tri_rel' : forall B F L,
      negativeFormula F -> |-f- B ; L ; UP [F] ->  |-f- B ; L ; DW F
  | tri_top' : forall B L M,
      |-f- B ; L ; UP (Top :: M)
  | tri_bot' : forall B L M,
      |-f- B ; L ; UP M -> |-f- B ; L ; UP (Bot :: M)
  | tri_par' : forall B L M F G,
      |-f- B ; L ; UP (F::G::M) -> |-f- B ; L ; UP((MOr F G) :: M)
  | tri_with' : forall B L M F G,
      |-f- B ; L ; UP (F :: M) ->
      |-f- B ; L ; UP (G :: M) -> |-f- B ; L ; UP ((AAnd F  G) :: M)
  | tri_quest' : forall B L M F i,
      |-f- (i,F)::B ; L ; UP M -> |-f- B ; L ; UP ((Quest i F) :: M)         
  | tri_store' : forall B L M F,
      positiveLFormula  F-> |-f- B ; F::L; UP M -> |-f- B ; L ; UP (F::M)
  | tri_dec1' : forall B L L' F,
      positiveFormula F -> Permutation (F::L') L -> |-f- B ; L' ; DW F -> |-f- B ; L ; UP []
  | tri_dec2u' : forall B L F i,
     u i = true -> ~IsPositiveAtom F -> In (i,F) B -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | tri_dec2l' : forall B B' L F i,
     u i = false -> ~IsPositiveAtom F -> Permutation ((i,F)::B') B -> |-f- B' ; L ; DW F -> |-f- B ; L ; UP []

  | tri_dec3' : forall B L F ,
      theory F -> ~IsPositiveAtom F -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | tri_ex'  : forall B FX M t,
      uniform_oo FX -> proper t -> |-f- B; M ; DW (FX t) -> |-f- B; M ; DW (Some  FX)
  | tri_fx'  : forall B L FX M ,
      uniform_oo FX -> (forall x, proper x -> |-f- B ; L ; UP( (FX x) ::  M)) ->
      |-f- B ; L ; UP ((All FX) :: M) 
 | tri_bang' : forall a B F, LtX a (getL B) ->
   |-f- getLtX a B ; [] ; (UP [F]) -> |-f- B ; [] ; DW (Bang a F)
                                                                                           
  where "'|-f-' B ';' L ';' X " := (seq B L X).

  
End LLSequent .

Module SELLNotations .

Notation "n ⊢ B ';' L ⇕ X " := (seqN _ n B L X)  (at level 80).
Notation "n ⊢ B ';' L ⇓ F " := (seqN _ n B L (DW F))  (at level 80).
Notation "n ⊢ B ';' L ⇑ F " := (seqN _ n B L (UP F))  (at level 80).
Notation "⊢ B ';' L ⇕ X " := (seq _ B L X)  (at level 80).
Notation "⊢ B ';' L ⇓ F " := (seq _ B L (DW F))  (at level 80).
Notation "⊢ B ';' L ⇑ F " := (seq _ B L (UP F))  (at level 80).

End SELLNotations .

Global Hint Constructors seqN seq: core .
