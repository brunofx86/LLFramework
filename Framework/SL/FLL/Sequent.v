Require Export LL.Framework.SL.FLL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section FLLSequent.
  Context `{OLS: OLSig}.
 
  Variable th : oo -> Prop.
  
  (* Andreoli's triadic system for linear logic *)
  Reserved Notation " n '|-F-' B ';' L ';' X " (at level 80).

  (** Sequent rules. in [n '|-F-' B ';' L ';' X], [n] is the height of
  the derivation ; [B] a list representing the classical context ; [L]
  the linear context and [X] and [Arrow] that can be [DW F] (for the
  positive phase) or [UP L] (for the negative phase). *)
  Inductive FLLN:  nat -> list oo -> list oo -> Arrow -> Prop :=
 (* axioms *)
  | tri_init1 : forall B A n,  n |-F- B ; [atom A] ; DW (perp A)
  | tri_init2 : forall B A n,  In (atom A) B -> n |-F- B ; [] ; DW (perp A)
  | tri_one : forall B n,  n |-F- B ; [] ; DW One
  | tri_top : forall B L M n,
      n |-F- B ; L ; UP (Top :: M)
 (* additives *)
  | tri_plus1 : forall B M F G n,
      n |-F- B ; M ; DW F -> S n |-F- B ; M ; DW (AOr F G)
  | tri_plus2 : forall B M F G n,
      n |-F- B ; M ; DW G -> S n |-F- B ; M ; DW (AOr F G)
  | tri_with : forall B L M F G n,
      (n |-F- B ; L ; UP (F :: M)) ->
      (n |-F- B ; L ; UP (G :: M)) -> S n|-F- B ; L ; UP ((AAnd F  G) :: M)
 (* multiplicatives *)
  | tri_bot : forall B L M n,
      n |-F- B ; L ; UP M -> S n  |-F- B ; L ; UP (Bot :: M)
  | tri_par : forall B L M F G n,
      n |-F- B ; L ; UP (F::G::M) -> S n  |-F- B ; L ; UP((MOr F G) :: M)
  | tri_tensor : forall B M N MN F G n, Permutation MN (M++N) ->
                                        (n |-F- B ; M ; DW F) ->
                                        (n |-F- B ; N ; DW G )->
                                        S n |-F- B ; MN ; DW (MAnd F G)
 (* exponentials *)
  | tri_quest : forall B L M F n,
      n |-F- F::B ; L ; UP M -> S n  |-F- B ; L ; UP ((Quest F) :: M)
  | tri_bang : forall B F n,
      n |-F- B ; [] ; UP [F] -> S n  |-F- B ; [] ; DW (Bang F) 
 (* quantifiers *)
  | tri_ex  : forall B FX M t n,
      uniform_oo FX -> proper t -> n |-F- B; M ; DW (FX t) -> S n|-F- B; M ; DW (Some  FX)
  | tri_fx  : forall B L FX M n,
      uniform_oo FX -> (forall x, proper x -> n |-F- B ; L ; UP( (FX x) ::  M)) ->
      S n |-F- B ; L ; UP ((All FX) :: M)                                                                                                                           
 (* reaction rules *)
  | tri_rel : forall B F L n,
      negFormula F -> n |-F- B ; L ; UP [F] ->  S n |-F- B ; L ; DW F
  | tri_store : forall B L M F n,
      posLFormula F -> n |-F- B ; F::L ; UP M -> S n |-F- B ; L ; UP (F::M)
 (* decision rules *)
  | tri_dec1 : forall B L L' F n,
      posFormula F -> Permutation (F::L') L -> n |-F- B ; L' ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec2 : forall B L F n,
      ~ posAtom F -> In F B -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec3 : forall B L F n,
      ~ posAtom F -> th F -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []      

  where " n '|-F-' B ';' L ';' X " := (FLLN n B L X).
  
  Reserved Notation " '|-f-' B ';' L ';' X " (at level 80).

  Inductive FLLS: list oo -> list oo -> Arrow -> Prop :=
 (* axioms *)
  | tri_init1' : forall B A, |-f- B ; [atom A] ; DW (perp A)
  | tri_init2' : forall B A,  In (atom A) B -> |-f- B ; [] ; DW (perp A)
  | tri_one' : forall B, |-f- B ; [] ; DW One
  | tri_top' : forall B L M,
      |-f- B ; L ; UP (Top :: M)
 (* additives *)
  | tri_plus1' : forall B M F G,
      |-f- B ; M ; DW F -> |-f- B ; M ; DW (AOr F G)
  | tri_plus2' : forall B M F G,
      |-f- B ; M ; DW G -> |-f- B ; M ; DW (AOr F G)
  | tri_with' : forall B L M F G,
      (|-f- B ; L ; UP (F :: M)) ->
      (|-f- B ; L ; UP (G :: M)) -> |-f- B ; L ; UP ((AAnd F  G) :: M)
 (* multiplicatives *)
  | tri_bot' : forall B L M,
      |-f- B ; L ; UP M -> |-f- B ; L ; UP (Bot :: M)
  | tri_par' : forall B L M F G,
      |-f- B ; L ; UP (F::G::M) -> |-f- B ; L ; UP((MOr F G) :: M)
  | tri_tensor' : forall B M N MN F G, Permutation MN (M++N) ->
                                        (|-f- B ; M ; DW F) ->
                                        (|-f- B ; N ; DW G )->
                                         |-f- B ; MN ; DW (MAnd F G)

 (* exponentials *)
  | tri_quest' : forall B L M F,
      |-f- B++[F] ; L ; UP M -> |-f- B ; L ; UP ((Quest F) :: M)
  | tri_bang' : forall B F,
      |-f- B ; [] ; UP [F] -> |-f- B ; [] ; DW (Bang F)
 (* quantifiers *)
  | tri_ex'  : forall B FX M t,
      uniform_oo FX -> proper t -> |-f- B; M ; DW (FX t) -> |-f- B; M ; DW (Some  FX)
  | tri_fx'  : forall B L FX M,
      uniform_oo FX -> (forall x, proper x -> |-f- B ; L ; UP( (FX x) ::  M)) ->
      |-f- B ; L ; UP ((All FX) :: M)                                                                                                                           
 (* reaction rules *)
  | tri_rel' : forall B F L,
      negFormula F -> |-f- B ; L ; UP [F] ->  |-f- B ; L ; DW F
  | tri_store' : forall B L M F,
      posLFormula F -> |-f- B ; F::L ; UP M -> |-f- B ; L ; UP (F::M)
 (* decision rules *)
  | tri_dec1' : forall B L L' F,
      posFormula F -> Permutation (F::L') L -> |-f- B ; L' ; DW F -> |-f- B ; L ; UP []
  | tri_dec2' : forall B L F,
      ~posAtom F -> In F B -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | tri_dec3' : forall B L F,
      ~posAtom F -> th F -> |-f- B ; L ; DW F -> |-f- B ; L ; UP [] 
  where "'|-f-' B ';' L ';' X " := (FLLS B L X).
   
End FLLSequent .

Global Hint Constructors FLLN : core.
Global Hint Constructors FLLS : core.

Declare Scope FLL.
Declare Scope FLLT.

Notation "n ⊢ B ; L ⇕ X " := (FLLN _ n B L X)  (at level 80):FLL.
Notation "n ⊢ B ; L ⇓ F " := (FLLN _ n B L (DW F))  (at level 80):FLL.
Notation "n ⊢ B ; L ⇑ F " := (FLLN _ n B L (UP F))  (at level 80):FLL.
Notation "⊢ B ; L ⇕ X " := (FLLS _ B L X)  (at level 80):FLL.
Notation "⊢ B ; L ⇓ F " := (FLLS _ B L (DW F))  (at level 80):FLL.
Notation "⊢ B ; L ⇑ F " := (FLLS _ B L (UP F))  (at level 80):FLL.

Notation "th - n ⊢ B ';' L ⇕ X " := (FLLN th n B L X)  (at level 80):FLLT.
Notation "th - n ⊢ B ';' L ⇓ F " := (FLLN th n B L (DW F))  (at level 80):FLLT.
Notation "th - n ⊢ B ';' L ⇑ F " := (FLLN th n B L (UP F))  (at level 80):FLLT.
Notation "th - ⊢ B ';' L ⇕ X " := (FLLS th B L X)  (at level 80):FLLT.
Notation "th - ⊢ B ';' L ⇓ F " := (FLLS th B L (DW F))  (at level 80):FLLT.
Notation "th - ⊢ B ';' L ⇑ F " := (FLLS th B L (UP F))  (at level 80):FLLT.
