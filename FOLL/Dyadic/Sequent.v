Require Export LL.Misc.Utils. 
Require Export LL.FOLL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section LL2Sequent.
  Context `{OLS: OLSig}.

  Inductive LL2S:  list oo -> list oo -> Prop :=
  (* axioms *)  
  | ll2_init' : forall B A L, Permutation L [atom A; perp A] -> LL2S B L
  | ll2_one' : forall B, LL2S B [One]
  | ll2_top' : forall B M L, Permutation L (Top::M) ->
      LL2S B L
  (* additives *)  
  | ll2_plus1' : forall B M F G L, Permutation L (AOr F G::M) ->
      LL2S B (F::M) -> LL2S B L
  | ll2_plus2' : forall B M F G L, Permutation L (AOr F G::M) ->
      LL2S B (G::M) -> LL2S B L    
  | ll2_with' : forall B M F G L, Permutation L (AAnd F G::M) ->
      LL2S B (F::M) ->
      LL2S B (G::M) -> LL2S B L      
  (* multiplicatives *)  
  | ll2_bot' : forall B M L, Permutation L (Bot::M) ->
      LL2S B M -> LL2S B L
  | ll2_par' : forall B M F G L, Permutation L (MOr F G::M) ->
      LL2S B (F::G::M) -> LL2S B L  
  | ll2_tensor' : forall B M N F G L, Permutation L (MAnd F G::(M ++ N)) ->
                                        LL2S B (F::M) ->
                                        LL2S B (G::N) ->
                                        LL2S B L       
  (* exponentials *) 
  | ll2_quest' : forall B M F L, Permutation L (Quest F::M) ->
      LL2S (F::B) M -> LL2S B L      
  | ll2_bang' : forall B F,
      LL2S B [F] -> LL2S B [Bang F]     
  (* quantifiers *)   
  | ll2_ex'  : forall B FX M L t,  Permutation L ((Some FX)::M) ->
      uniform_oo FX -> proper t -> LL2S B  (FX t::M) -> LL2S B L
  | ll2_fx'  : forall B FX M L, Permutation L (All FX::M) ->
      uniform_oo FX -> (forall x, proper x -> LL2S B (FX x::M)) ->
      LL2S B L        
  (* structurals *)     
  | ll2_abs' : forall B L F, 
     In F B -> LL2S B (F::L) -> LL2S B L.

  Inductive LL2N:  nat -> list oo -> list oo -> Prop :=
  (* axioms *)
  | ll2_init : forall B A L n, Permutation L [atom A; perp A] -> LL2N n B L
  | ll2_one : forall B n, LL2N n B [One]
  | ll2_top : forall B M L n, Permutation L (Top::M) ->
      LL2N n B L
  (* additives *)      
  | ll2_plus1 : forall B M F G L n, Permutation L (AOr F G::M) ->
      LL2N n B (F::M) -> LL2N (S n) B L
  | ll2_plus2 : forall B M F G L n, Permutation L (AOr F G::M) ->
      LL2N n B (G::M) -> LL2N (S n) B L
  | ll2_with : forall B M F G L n, Permutation L (AAnd F G::M) ->
      LL2N n B (F::M) ->
      LL2N n B (G::M) -> LL2N (S n) B L 
  (* multiplicatives *)     
  | ll2_bot : forall B M L n, Permutation L (Bot::M) ->
      LL2N n B M -> LL2N (S n) B L
  | ll2_par : forall B M F G L n, Permutation L (MOr F G ::M) ->
      LL2N n B (F::G::M) -> LL2N (S n) B L         
  | ll2_tensor : forall B M N F G L n, Permutation L (MAnd F G::(M ++ N)) ->
                                        LL2N n B (F::M) ->
                                        LL2N n B (G::N) ->
                                        LL2N (S n)  B L 
   (* exponentials *)          
  | ll2_quest : forall B M F L n, Permutation L (Quest F::M) ->
      LL2N n (F::B) M -> LL2N (S n) B L   
  | ll2_bang : forall B F n,
      LL2N n B [F] -> LL2N (S n) B [Bang F]
  (* quantifiers *)   
  | ll2_ex  : forall B FX M L t n,  Permutation L (Some  FX::M) ->
      uniform_oo FX -> proper t -> LL2N n B (FX t::M) -> LL2N (S n) B L
  | ll2_fx  : forall B FX M L n, Permutation L (All  FX::M) ->
      uniform_oo FX -> (forall x, proper x -> LL2N n B (FX x::M)) ->
      LL2N (S n) B L  
  (* structurals *)            
  | ll2_abs : forall B L F n, 
     In F B -> LL2N n B (F::L) -> LL2N (S n) B L. 
                                     
 End LL2Sequent .

Global Hint Constructors LL2N : core .
Global Hint Constructors LL2S : core. 
 
Notation "'LL2' n '|--' B ';' L " := (LL2N n B L)  (at level 80).
Notation "'LL2' '|--' B ';' L " := (LL2S B L)  (at level 80).