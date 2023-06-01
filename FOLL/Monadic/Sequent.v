Require Export LL.Misc.Utils. 
Require Export LL.FOLL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section LL1Sequent.
  Context `{OLS: OLSig}.
 
  Inductive LL1S: list oo -> Prop :=
  (* axioms *)
  | ll1_init' : forall A L, Permutation L [atom A; perp A] -> LL1S  L
  | ll1_one' : LL1S [One]
  | ll1_top' : forall M L, Permutation L (Top::M) -> LL1S  L  
  (* additives *)
  | ll1_plus1' : forall M F G L, Permutation L (AOr F G::M) ->
      LL1S (F::M) -> LL1S  L
  | ll1_plus2' : forall M F G L, Permutation L (AOr F G::M) ->
      LL1S  (G::M) -> LL1S  L
  | ll1_with' : forall M F G L, Permutation L (AAnd F G::M) ->
      LL1S  (F::M) ->
      LL1S  (G::M) -> LL1S  L    
  (* multiplicatives *)   
  | ll1_bot' : forall M L, Permutation L (Bot::M) ->
      LL1S  M -> LL1S  L  
  | ll1_par' : forall M F G L, Permutation L (MOr F G::M) ->
      LL1S  (F::G::M) ->  LL1S  L       
  | ll1_tensor' : forall M N F G L, Permutation L (MAnd F G::(M ++ N)) ->
                                        LL1S (F::M) ->
                                        LL1S (G::N) ->
                                         LL1S L 
  (* exponentials *)
  | ll1_quest' : forall M F L, Permutation L (Quest F::M) ->
      LL1S (F::M) ->  LL1S  L
   | ll1_bang' : forall M L F, Permutation L (Bang F:: map Quest M)->
      LL1S  (F:: map Quest M) -> LL1S L             
  (* quantifiers *)
  | ll1_ex'  : forall FX M L t,  Permutation L (Some FX::M) ->
      uniform_oo FX -> proper t -> LL1S (FX t::M) -> LL1S  L
  | ll1_fx'  : forall FX M L, Permutation L (All  FX::M) ->
      uniform_oo FX -> (forall x, proper x -> LL1S  (FX x::M)) ->
       LL1S  L  
  (* structural *)            
  | ll1_weak' : forall M F L, Permutation L (Quest F::M) ->
      LL1S M -> LL1S  L
  | ll1_contr' : forall M F L, Permutation L (Quest F::M) ->
       LL1S (Quest F::L) ->  LL1S  L.

  Inductive LL1N:  nat -> list oo -> Prop :=
  (* axioms *)
  | ll1_init : forall A L n, Permutation L [atom A; perp A] -> LL1N n  L
  | ll1_one : forall n, LL1N n [One]
  | ll1_top : forall M L n, Permutation L (Top::M) -> LL1N n  L  
  (* additives *)
  | ll1_plus1 : forall M F G L n, Permutation L (AOr F G::M) ->
      LL1N n (F::M) -> LL1N (S n)  L
  | ll1_plus2 : forall M F G L n, Permutation L (AOr F G::M) ->
      LL1N n  (G::M) -> LL1N (S n)  L
  | ll1_with : forall M F G L n, Permutation L (AAnd F G::M) ->
      LL1N n  (F::M) ->
      LL1N n  (G::M) -> LL1N (S n)  L    
  (* multiplicatives *)   
  | ll1_bot : forall M L n, Permutation L (Bot::M) ->
      LL1N n  M -> LL1N (S n)  L  
  | ll1_par : forall M F G L n, Permutation L (MOr F G::M) ->
      LL1N n  (F::G::M) -> LL1N (S n)  L       
  | ll1_tensor : forall M N F G L n, Permutation L (MAnd F G::(M ++ N)) ->
                                        LL1N n (F::M) ->
                                        LL1N n (G::N) ->
                                        LL1N (S n) L 
  (* exponentials *)
  | ll1_quest : forall M F L n, Permutation L (Quest F::M) ->
      LL1N n (F::M) -> LL1N (S n)  L
   | ll1_bang : forall M L F n, Permutation L (Bang F::map Quest M)->
      LL1N n  (F::map Quest M) -> LL1N (S n) L             
  (* quantifiers *)
  | ll1_ex  : forall FX M L t n,  Permutation L (Some FX::M) ->
      uniform_oo FX -> proper t -> LL1N n (FX t::M) -> LL1N (S n)  L
  | ll1_fx  : forall FX M L n, Permutation L (All  FX::M) ->
      uniform_oo FX -> (forall x, proper x -> LL1N n  (FX x::M)) ->
      LL1N (S n) L  
  (* structurals *)            
  | ll1_weak : forall M F L n, Permutation L (Quest F::M) ->
      LL1N n M -> LL1N (S n)  L
  | ll1_contr : forall M F L n, Permutation L (Quest F::M) ->
      LL1N n (Quest F::L) -> LL1N (S n)  L.

 End LL1Sequent .

Global Hint Constructors LL1N : core .
Global Hint Constructors LL1S : core. 
 
Notation "'LL1' n '|--' L " := (LL1N n L)  (at level 80).
Notation "'LL1' '|--' L " := (LL1S L)  (at level 80).