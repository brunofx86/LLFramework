Require Export LL.Misc.Utils. 
Require Export LL.FOLL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section LL3Sequent.
  Context `{OLS: OLSig}.

  Inductive LL3S:  list oo -> list oo -> Prop :=
  (* axioms *)  
  | ll3_init' : forall B A,  LL3S B [atom A; perp A]
  | ll3_one' : forall B,  LL3S B [One]
  | ll3_top' : forall B M,
      LL3S B (Top::M)
  (* additives *)   
  | ll3_plus1' : forall B M F G,
      LL3S B (F::M) -> LL3S B (AOr F G::M)
  | ll3_plus2' : forall B M F G,
      LL3S B (G::M) -> LL3S B (AOr F G::M) 
  | ll3_with' : forall B M F G,
      LL3S B (F::M) ->
      LL3S B (G::M) -> LL3S B (AAnd F G::M)      
  (* multiplicatives *)
  | ll3_bot' : forall B M,
      LL3S B M -> LL3S B (Bot::M)
  | ll3_par' : forall B M F G,
      LL3S B (F::G::M) ->  LL3S B (MOr F G::M)
  | ll3_tensor' : forall B M N  F G,
                                    LL3S B (F::M) ->
                                    LL3S B (G::N) ->
                                     LL3S B (MAnd F G::(M++N))         
  (* exponentials *)  
  | ll3_quest' : forall B M F,
      LL3S (F::B) M -> LL3S B (Quest F::M)     
  | ll3_bang' : forall B F,
      LL3S B [F] -> LL3S B [Bang F]  
  (* quantifiers *) 
  | ll3_ex'  : forall B FX M t,
      uniform_oo FX -> proper t -> LL3S B (FX t::M) -> LL3S B (Some FX::M)
  | ll3_fx'  : forall B FX M,
      uniform_oo FX -> (forall x, proper x -> LL3S B (FX x::M)) ->
      LL3S B (All FX::M)       
  (* structurals *)       
  | ll3_abs' : forall B L F,
     In F B -> LL3S B (F::L) -> LL3S B L  
  | ll3_exh' : forall B M L,
    Permutation M L -> LL3S B M ->  LL3S B L. 
 
  Inductive LL3N: nat -> list oo -> list oo -> Prop :=
  (* axioms *)
  | ll3_init : forall B A n, LL3N n B [atom A; perp A]
  | ll3_one : forall B n,  LL3N n B [One]
  | ll3_top : forall B M n,
      LL3N n B (Top::M)
  (* additives *) 
  | ll3_plus1 : forall B M F G n,
      LL3N n B (F::M) -> LL3N (S n) B (AOr F G::M)
  | ll3_plus2 : forall B M F G n,
      LL3N n B (G::M) -> LL3N (S n) B (AOr F G::M)  
  | ll3_with : forall B M F G n,
      LL3N n B (F::M) ->
      LL3N n B (G::M) -> LL3N (S n) B (AAnd F  G::M)      
  (* multiplicatives *)
  | ll3_bot : forall B M n,
      LL3N n B M -> LL3N (S n) B (Bot::M)
  | ll3_par : forall B M F G n,
      LL3N n B (F::G::M) -> LL3N (S n) B (MOr F G::M)  
  | ll3_tensor : forall B M N F G n,
                                        LL3N n B (F::M) ->
                                        LL3N n B (G::N) ->
                                        LL3N (S n) B (MAnd F G::(M ++ N))       
  (* exponentials *)
  | ll3_quest : forall B M F n,
      LL3N n (F::B) M -> LL3N (S n) B (Quest F::M)      
  | ll3_bang : forall B F n,
      LL3N n B [F] -> LL3N (S n) B [Bang F]
  (* quantifiers *) 
  | ll3_ex  : forall B FX M t n,
      uniform_oo FX -> proper t -> LL3N n B (FX t::M) -> LL3N (S n) B (Some  FX::M)
  | ll3_fx  : forall B FX M n,
      uniform_oo FX -> (forall x, proper x -> LL3N n B (FX x::M)) ->
      LL3N (S n) B (All FX::M)      
  (* structurals *)     
  | ll3_abs : forall B L F n,
     In F B -> LL3N n B (F::L) -> LL3N (S n) B L  
  | ll3_exh : forall B M L n,
    Permutation M L -> LL3N n B M ->  LL3N (S n) B L.                                                                                                 

End LL3Sequent .

Global Hint Constructors LL3N : core .
Global Hint Constructors LL3S : core. 
  
Notation "'LL3' n '|--' B ';' L " := (LL3N n B L)  (at level 80).
Notation "'LL3' '|--' B ';' L " := (LL3S B L)  (at level 80).