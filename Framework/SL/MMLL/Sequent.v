(** * Focused Sequent system 
This file specifies a one-sided focused system for MMLL The system is
   parametric to [theory: oo->Prop], defining the formulas that can be used in
   rule [mll_dec3]. In this implementation, all the atoms are assumed to be
   positive and then, proofs must finish with the initial rule focusing on
   atomic propositions of the form [perp A]. The exchange rule is embedded in
   the definition, e.g., of [mll_tensor]. 
 *)


Require Export LL.Misc.Utils. 
Require Export LL.Framework.SL.MMLL.Locations.

Export ListNotations.
Set Implicit Arguments.

Section LLSequent.
  Context `{SI : SigMMLL}.
  Context `{OLS: OLSig}.

  Variable theory : oo -> Prop. (* theory Definition *)

  Reserved Notation " n '|-F-' B ';' L ';' X " (at level 80).

  (** Sequent rules. in [n '|-F-' B ';' L ';' X], [n] is the height of
  the derivation ; [B] a list representing the classical context ; [L]
  the linear context and [X] and [Arrow] that can be [DW F] (for the
  positive phase) or [UP L] (for the negative phase). *)
  Inductive MLLN:  nat -> list location -> list oo -> Arrow -> Prop :=
  | mll_init1 : forall B A n, SetU B -> n |-F- B ; [atom A] ; DW (perp A)
  | mll_init2 : forall B C A n i, SetU C -> mt i = true -> Permutation ((i, atom A)::C) B -> n |-F- B ; [] ; DW (perp A)
  | mll_one : forall B n, SetU B ->  n |-F- B ; [] ; DW One
  
  | mll_tensor : forall B C D BD M N MN F G n, Permutation MN (M++N) -> Permutation BD (B++C++D) -> SetU B ->
                                     SetL C -> SetL D ->
                                        (n |-F- B++C ; M ; DW F) ->
                                        (n |-F- B++D ; N ; DW G )->
                                        S n |-F- BD ; MN ; DW (MAnd F G)
                                        
  | mll_plus1 : forall B M F G n,
      n |-F- B ; M ; DW F -> S n |-F- B ; M ; DW (AOr F G)
  | mll_plus2 : forall B M F G n,
      n |-F- B ; M ; DW G -> S n |-F- B ; M ; DW (AOr F G)
  | mll_rel : forall B F L n,
      negFormula F -> n |-F- B ; L ; UP [F] ->  S n |-F- B ; L ; DW F
  | mll_top : forall B L M n,
      n |-F- B ; L ; UP (Top :: M)
  | mll_bot : forall B L M n,
      n |-F- B ; L ; UP M -> S n  |-F- B ; L ; UP (Bot :: M)
  | mll_par : forall B L M F G n,
      n |-F- B ; L ; UP (F::G::M) -> S n  |-F- B ; L ; UP((MOr F G) :: M)
  | mll_with : forall B L M F G n,
      (n |-F- B ; L ; UP (F :: M)) ->
      (n |-F- B ; L ; UP (G :: M)) -> S n|-F- B ; L ; UP ((AAnd F  G) :: M)
  | mll_quest : forall B L M F n i,
      n |-F- (i,F)::B ; L ; UP M -> S n  |-F- B ; L ; UP ((Quest i F) :: M)         
  | mll_store : forall B L M F n,
      posLFormula  F-> n |-F- B ; F::L ; UP M -> S n |-F- B ; L ; UP (F::M)
  | mll_dec1 : forall B L L' F n,
      posFormula F -> Permutation (F::L') L -> n |-F- B ; L' ; DW F -> S n |-F- B ; L ; UP []
  | mll_dec2u : forall B L F n i,
     u i = true -> mt i = true -> ~posAtom F -> In (i,F) B -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | mll_dec2l : forall B B' L F n i,
     u i = false -> mt i = true -> ~posAtom F -> Permutation ((i,F)::B') B -> n |-F- B' ; L ; DW F -> S n |-F- B ; L ; UP []
  | mll_dec3 : forall B L F n,
      theory F -> ~posAtom F -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | mll_ex  : forall B FX M t n,
      uniform_oo FX -> proper t -> n |-F- B; M ; DW (FX t) -> S n|-F- B; M ; DW (Some  FX)
  | mll_fx  : forall B L FX M n,
      uniform_oo FX -> (forall x, proper x -> n |-F- B ; L ; UP( (FX x) ::  M)) ->
      S n |-F- B ; L ; UP ((All FX) :: M)                                                                                                                           
  | mll_bangL : forall B F n,
     SetU B ->  n  |-F- B ; [] ; (UP [F]) -> S n  |-F- B ; [] ; DW (Bang loc F)
  | mll_bang : forall B F n i, i <> loc ->
     MLLNExp n B i [] [] (UP [F]) -> S n  |-F- B ; [] ; DW (Bang i F)
| mll_bangD : forall n B i,  MLLNExp n B i [] [] (UP [ ]) -> md i = true -> S n |-F- B ; [] ; UP []     
     with
      MLLNExp : nat -> list location -> subexp -> list location -> list oo -> Arrow -> Prop :=
       | mll_copyK4 : forall b F n L M C B B' i, lt i b  -> m4 b = true -> 
        Permutation ((b,F)::B') B -> MLLNExp n B' i (C++[(plust b,F)]) L (UP M) -> 
                                          MLLNExp (S n) B i C L (UP M)
       | mll_copyUK : forall b F n L M C B B' i, lt i b  -> m4 b = false -> u b = true ->
        Permutation ((b,F)::B') B -> MLLNExp n B' i (C++[(loc,F)]) L (UP M) -> 
                                          MLLNExp (S n) B i C L (UP M) 
       | mll_copyLK : forall b F n L M C B B' i, lt i b  -> m4 b = false -> u b = false ->
        Permutation ((b,F)::B') B -> MLLNExp n B' i C L (UP (M++[F])) -> 
                                          MLLNExp (S n) B i C L (UP M)                                    
       | mll_exp : forall B C i L M n, SetU B -> (* NoLtX i B -> *)
                  n |-F- C; L; UP M -> MLLNExp (S n) B i C L (UP M)
      
  where " n '|-F-' B ';' L ';' X " := (MLLN n B L X).

  (** Well formedness conditions for arrows. *)
  Definition isArrow (Ar:Arrow) : Prop :=
    match Ar with
    | UP l => isFormulaL l
    | DW F => isFormula F
    end.
  
  Reserved Notation " '|-f-' B ';' L ';' X " (at level 80).

  (** The same system without the height of the derivation *)
  Inductive MLLS:  list location -> list oo -> Arrow -> Prop :=
  | mll_init1' : forall B A ,  SetU B ->  |-f- B ; [atom A] ; DW (perp A)
  | mll_init2' : forall B C A i, SetU C -> mt i = true -> Permutation ((i, atom A)::C) B -> |-f- B ; [] ; DW (perp A)
  
  | mll_one' : forall B, SetU B -> |-f- B ; [] ; DW One
  | mll_tensor' : forall M N MN B C D BD F G, Permutation MN (M++N) -> Permutation BD (B++C++D) -> SetU B ->
                                     SetL C -> SetL D ->
                                       |-f- B++C ; M ; DW F ->
                                        |-f- B++D ; N ; DW G ->
                                        |-f- BD ; MN ; DW (MAnd F G)
  | mll_plus1' : forall B M F G ,
      |-f- B ; M ; DW F -> |-f- B ; M ; DW (AOr F G)
  | mll_plus2' : forall B M F G,
      |-f- B ; M ; DW G -> |-f- B ; M ; DW (AOr F G)
  | mll_rel' : forall B F L,
      negFormula F -> |-f- B ; L ; UP [F] ->  |-f- B ; L ; DW F
  | mll_top' : forall B L M,
      |-f- B ; L ; UP (Top :: M)
  | mll_bot' : forall B L M,
      |-f- B ; L ; UP M -> |-f- B ; L ; UP (Bot :: M)
  | mll_par' : forall B L M F G,
      |-f- B ; L ; UP (F::G::M) -> |-f- B ; L ; UP((MOr F G) :: M)
  | mll_with' : forall B L M F G,
      |-f- B ; L ; UP (F :: M) ->
      |-f- B ; L ; UP (G :: M) -> |-f- B ; L ; UP ((AAnd F  G) :: M)
  | mll_quest' : forall B L M F i,
      |-f- (i,F)::B ; L ; UP M -> |-f- B ; L ; UP ((Quest i F) :: M)         
  | mll_store' : forall B L M F,
      posLFormula  F-> |-f- B ; F::L; UP M -> |-f- B ; L ; UP (F::M)
  | mll_dec1' : forall B L L' F,
      posFormula F -> Permutation (F::L') L -> |-f- B ; L' ; DW F -> |-f- B ; L ; UP []
  | mll_dec2u' : forall B L F i,
     u i = true -> mt i = true -> ~posAtom F -> In (i,F) B -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | mll_dec2l' : forall B B' L F i,
     u i = false -> mt i = true -> ~posAtom F -> Permutation ((i,F)::B') B -> |-f- B' ; L ; DW F -> |-f- B ; L ; UP []

  | mll_dec3' : forall B L F ,
      theory F -> ~posAtom F -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | mll_ex'  : forall B FX M t,
      uniform_oo FX -> proper t -> |-f- B; M ; DW (FX t) -> |-f- B; M ; DW (Some  FX)
  | mll_fx'  : forall B L FX M ,
      uniform_oo FX -> (forall x, proper x -> |-f- B ; L ; UP( (FX x) ::  M)) ->
      |-f- B ; L ; UP ((All FX) :: M) 
 | mll_bangL' : forall B F,
    SetU B -> |-f- B ; [] ; (UP [F]) -> |-f- B ; [] ; DW (Bang loc F)
                                                                                                                          
| mll_bang' : forall B F i, i <> loc -> 
     MLLSExp B i [] [] (UP [F]) -> |-f- B ; [] ; DW (Bang i F)
| mll_bangD' : forall B i,  MLLSExp B i [] [] (UP []) -> md i = true -> |-f- B ; [] ; UP []
     with
     MLLSExp : list location -> subexp -> list location -> list oo -> Arrow -> Prop :=
       | mll_copyK4' : forall b F L M C B B' i, lt i b  -> m4 b = true -> 
        Permutation ((b,F)::B') B-> MLLSExp B' i (C++[(plust b,F)]) L (UP M) -> 
                                      MLLSExp B i C L (UP M)
       | mll_copyUK' : forall b F L M C B B' i, lt i b  -> m4 b = false -> u b = true ->
        Permutation ((b,F)::B') B -> MLLSExp B' i (C++[(loc,F)]) L (UP M) -> 
                                      MLLSExp B i C L (UP M) 
        | mll_copyLK' : forall b F L M C B B' i, lt i b  -> m4 b = false -> u b = false ->
        Permutation ((b,F)::B') B -> MLLSExp B' i C L (UP (M++[F])) -> 
                                      MLLSExp B i C L (UP M)                                      
       | mll_exp' : forall B C i L M , SetU B -> (* NoLtX i B -> *)
                  |-f- C; L; UP M -> MLLSExp B i C L (UP M)

  where "'|-f-' B ';' L ';' X " := (MLLS B L X).

End LLSequent .

Module FLLNotations .

Notation "n ⊢ B ';' L ⇕ X " := (MLLN _ n B L X)  (at level 80).
Notation "n ⊢ B ';' L ⇓ F " := (MLLN _ n B L (DW F))  (at level 80).
Notation "n ⊢ B ';' L ⇑ F " := (MLLN _ n B L (UP F))  (at level 80).
Notation "⊢ B ';' L ⇕ X " := (MLLS _ B L X)  (at level 80).
Notation "⊢ B ';' L ⇓ F " := (MLLS _ B L (DW F))  (at level 80).
Notation "⊢ B ';' L ⇑ F " := (MLLS _ B L (UP F))  (at level 80).

End FLLNotations .

Global Hint Constructors MLLN MLLS: core .