Require Export LL.Misc.Utils. 
Require Export LL.SL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section LL1Sequent.
  Context `{OLS: OLSig}.
 
  Reserved Notation "n '|--'  L " (at level 80).

  Inductive LL1N:  nat -> list oo -> Prop :=
  (* axioms *)
  | ll1_init : forall A L n, Permutation L [atom A; perp A] -> n |--  L
  | ll1_one : forall n, n |-- [One]
  | ll1_top : forall M L n, Permutation L (Top :: M) -> n |--  L  
  (* additives *)
  | ll1_plus1 : forall M F G L n, Permutation L ((AOr F G)::M) ->
      n |-- F::M -> S n |--  L
  | ll1_plus2 : forall M F G L n, Permutation L ((AOr F G)::M) ->
      n |--  G::M -> S n |--  L
  | ll1_with : forall M F G L n, Permutation L ((AAnd F G)::M) ->
      n |--  F :: M ->
      n |--  G :: M -> S n |--  L    
  (* multiplicatives *)   
  | ll1_bot : forall M L n, Permutation L (Bot :: M) ->
      n |--  M -> S n |--  L  
  | ll1_par : forall M F G L n, Permutation L ((MOr F G) :: M) ->
      n |--  F::G::M -> S n |--  L       
  | ll1_tensor : forall M N F G L n, Permutation L ((MAnd F G)::(M ++ N)) ->
                                        (n |-- F::M) ->
                                        (n |-- G::N) ->
                                        (S n) |-- L 
  (* exponentials *)
  | ll1_quest : forall M F L n, Permutation L ((Quest F) :: M) ->
      n |-- F:: M -> S n |--  L
   | ll1_bang : forall M L F n, Permutation L ((Bang F) :: map Quest M)->
      n |--  F:: map Quest M -> S n |-- L             
  (* quantifiers *)
  | ll1_ex  : forall FX M L t n,  Permutation L ((Some  FX)::M) ->
      uniform_oo FX -> proper t -> n |-- (FX t)::M -> S n|--  L
  | ll1_fx  : forall FX M L n, Permutation L ((All  FX)::M) ->
      uniform_oo FX -> (forall x, proper x -> n |--  (FX x) ::  M) ->
      S n |--  L  
  (* structurals *)            
  | ll1_weak : forall M F L n, Permutation L ((Quest F) :: M) ->
      n |-- M -> S n |--  L
  | ll1_contr : forall M F L n, Permutation L ((Quest F) :: M) ->
      n |-- (Quest F) :: L -> S n |--  L                                                                            
  where "n '|--' L " := (LL1N n L).
   
  Reserved Notation "'|--' L" (at level 80).

  Inductive LL1S: list oo -> Prop :=
  (* axioms *)
  | ll1_init' : forall A L, Permutation L [atom A; perp A] -> |--  L
  | ll1_one' : |-- [One]
  | ll1_top' : forall M L, Permutation L (Top :: M) -> |--  L  
  (* additives *)
  | ll1_plus1' : forall M F G L, Permutation L ((AOr F G)::M) ->
      |-- F::M -> |--  L
  | ll1_plus2' : forall M F G L, Permutation L ((AOr F G)::M) ->
      |--  G::M -> |--  L
  | ll1_with' : forall M F G L, Permutation L ((AAnd F G)::M) ->
      |--  F :: M ->
      |--  G :: M -> |--  L    
  (* multiplicatives *)   
  | ll1_bot' : forall M L, Permutation L (Bot :: M) ->
      |--  M -> |--  L  
  | ll1_par' : forall M F G L, Permutation L ((MOr F G) :: M) ->
      |--  F::G::M ->  |--  L       
  | ll1_tensor' : forall M N F G L, Permutation L ((MAnd F G)::(M ++ N)) ->
                                        |-- F::M ->
                                        |-- G::N ->
                                         |-- L 
  (* exponentials *)
  | ll1_quest' : forall M F L, Permutation L ((Quest F) :: M) ->
      |-- F:: M ->  |--  L
   | ll1_bang' : forall M L F, Permutation L ((Bang F) :: map Quest M)->
      |--  F:: map Quest M -> |-- L             
  (* quantifiers *)
  | ll1_ex'  : forall FX M L t,  Permutation L ((Some  FX)::M) ->
      uniform_oo FX -> proper t -> |-- (FX t)::M -> |--  L
  | ll1_fx'  : forall FX M L, Permutation L ((All  FX)::M) ->
      uniform_oo FX -> (forall x, proper x -> |--  (FX x) ::  M) ->
       |--  L  
  (* structural *)            
  | ll1_weak' : forall M F L, Permutation L ((Quest F) :: M) ->
      |-- M -> |--  L
  | ll1_contr' : forall M F L, Permutation L ((Quest F) :: M) ->
       |-- (Quest F) :: L ->  |--  L      
  where "'|--'  L " := (LL1S L).

 End LL1Sequent .

Global Hint Constructors LL1N : core .
Global Hint Constructors LL1S : core. 
 
Notation "'LL1' n '|--' L " := (LL1N n L)  (at level 80).
Notation "'LL1' '|--' L " := (LL1S L)  (at level 80).

