Require Export LL.Misc.Utils. 
Require Export LL.SL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section LL3Sequent.
  Context `{OLS: OLSig}.
  Definition multiset := list.
  Reserved Notation "n '|--' B ';' L " (at level 80).

  Inductive LL3N: nat -> multiset oo -> list oo -> Prop :=
  | ll3_init : forall B A n, n |-- B ; [atom A; perp A]
  | ll3_one : forall B n,  n |-- B ; [One]
  
  | ll3_tensor : forall B M N F G n,
                                        (n |-- B ; F::M) ->
                                        (n |-- B ; G::N) ->
                                        (S n) |-- B ; (MAnd F G)::(M ++ N) 
  | ll3_plus1 : forall B M F G n,
      n |-- B ; F::M -> (S n) |-- B ; (AOr F G)::M
  | ll3_plus2 : forall B M F G n,
      n |-- B ; G::M -> (S n) |-- B ; (AOr F G)::M
      
  | ll3_bang : forall B F n,
      n |-- B ; [F] -> (S n) |-- B ; [Bang F]
  
   | ll3_exh : forall B M L n,
    Permutation M L -> n |-- B ; M ->  (S n) |-- B ; L
 
  | ll3_top : forall B M n,
      n |-- B ; Top :: M
  | ll3_bot : forall B M n,
      n |-- B ; M -> (S n) |-- B ; Bot :: M
  | ll3_par : forall B M F G n,
      n |-- B ; F::G::M -> (S n) |-- B ; (MOr F G) :: M
  | ll3_with : forall B M F G n,
      n |-- B ; F :: M ->
      n |-- B ; G :: M -> (S n) |-- B ; (AAnd F  G) :: M
  | ll3_quest : forall B M F n,
      n |-- F::B ; M -> (S n) |-- B ; (Quest F) :: M
  
  | ll3_abs : forall B L F n,
     In F B -> n |-- B ; F::L -> (S n) |-- B ; L 
  
  | ll3_ex  : forall B FX M t n,
      uniform_oo FX -> proper t -> n |-- B; (FX t)::M -> (S n)|-- B; (Some  FX)::M
  | ll3_fx  : forall B FX M n,
      uniform_oo FX -> (forall x, proper x -> n |-- B ; (FX x) ::  M) ->
      (S n) |-- B ; (All FX) :: M                                                                                                                           
  where "n '|--' B ';' L " := (LL3N n B L).
    
  Reserved Notation "'|--' B ';' L" (at level 80).

  (** The same system without the height of the derivation *)
  Inductive LL3S:  multiset oo -> multiset oo -> Prop :=
  | ll3_init' : forall B A,  |-- B ; [atom A; perp A]
  | ll3_one' : forall B,  |-- B ; [One]
  
  | ll3_tensor' : forall B M N  F G,
                                    (|-- B ; F::M) ->
                                    (|-- B ; G::N) ->
                                     |-- B ; (MAnd F G)::(M++N) 
  | ll3_plus1' : forall B M F G,
      |-- B ; F::M -> |-- B ; (AOr F G)::M
  | ll3_plus2' : forall B M F G,
      |-- B ; G::M -> |-- B ; (AOr F G)::M
      
  | ll3_bang' : forall B F,
      |-- B ; [F] -> |-- B ; [Bang F]
  
  | ll3_exh' : forall B M L,
    Permutation M L -> |-- B ; M ->  |-- B ; L
 
  | ll3_top' : forall B M,
      |-- B ; Top :: M
  | ll3_bot' : forall B M,
      |-- B ; M -> |-- B ; Bot :: M
  | ll3_par' : forall B M F G,
      |-- B ; F::G::M ->  |-- B ; (MOr F G) :: M
  | ll3_with' : forall B M F G,
      |-- B ; F :: M ->
      |-- B ; G :: M -> |-- B ; (AAnd F  G) :: M
  | ll3_quest' : forall B M F,
      |-- F::B ; M -> |-- B ; (Quest F) :: M
  
  | ll3_abs' : forall B L F,
     In F B -> |-- B ; F::L -> |-- B ; L 
  
  | ll3_ex'  : forall B FX M t,
      uniform_oo FX -> proper t -> |-- B; (FX t)::M -> |-- B; (Some  FX)::M
  
  | ll3_fx'  : forall B FX M,
      uniform_oo FX -> (forall x, proper x -> |-- B ; (FX x) ::  M) ->
      |-- B ; (All FX) :: M                                                                                                                           
  where "'|--' B ';' L " := (LL3S B L).
  
End LL3Sequent .

Global Hint Constructors LL3N : core .
Global Hint Constructors LL3S : core. 
  
Notation "'LL3' n '|--' B ';' L " := (LL3N n B L)  (at level 80).
Notation "'LL3' '|--' B ';' L " := (LL3S B L)  (at level 80).
 