Require Export LL.Misc.Utils. 
Require Export LL.PLL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section LL2Sequent.
  Definition multiset := list.
 
  Reserved Notation "n '|--' B ';' L " (at level 80).

  Inductive LL2N:  nat -> multiset oo -> multiset oo -> Prop :=
  (* axioms *)
  | ll2_init : forall B A L n, Permutation L [atom A; perp A] -> n |-- B ; L
  | ll2_one : forall B n, n |-- B ; [One]
  | ll2_top : forall B M L n, Permutation L (Top :: M) ->
      n |-- B ; L
  (* additives *)      
  | ll2_plus1 : forall B M F G L n, Permutation L ((AOr F G)::M) ->
      n |-- B ; F::M -> S n |-- B ; L
  | ll2_plus2 : forall B M F G L n, Permutation L ((AOr F G)::M) ->
      n |-- B ; G::M -> S n |-- B ; L
  | ll2_with : forall B M F G L n, Permutation L ((AAnd F G)::M) ->
      n |-- B ; F :: M ->
      n |-- B ; G :: M -> S n |-- B ; L 
  (* multiplicatives *)     
  | ll2_bot : forall B M L n, Permutation L (Bot :: M) ->
      n |-- B ; M -> S n |-- B ; L
  | ll2_par : forall B M F G L n, Permutation L ((MOr F G) :: M) ->
      n |-- B ; F::G::M -> S n |-- B ; L         
  | ll2_tensor : forall B M N F G L n, Permutation L ((MAnd F G)::(M ++ N)) ->
                                        (n |-- B ; F::M) ->
                                        (n |-- B ; G::N) ->
                                        (S n) |-- B ; L 
   (* exponentials *)          
  | ll2_quest : forall B M F L n, Permutation L ((Quest F) :: M) ->
      n |-- F::B ; M -> S n |-- B ; L   
  | ll2_bang : forall B F n,
      n |-- B ; [F] -> S n |-- B ; [Bang F]
  (* structurals *)            
  | ll2_abs : forall B L F n, 
     In F B -> n |-- B ; F::L -> S n |-- B ; L 
  
                                                                                                                    
  where "n '|--' B ';' L " := (LL2N n B L).
   
  Reserved Notation "'|--' B ';' L" (at level 80).

  Inductive LL2S:  multiset oo -> multiset oo -> Prop :=
  (* axioms *)  
  | ll2_init' : forall B A L, Permutation L [atom A; perp A] -> |-- B ; L
  | ll2_one' : forall B, |-- B ; [One]
  | ll2_top' : forall B M L, Permutation L (Top :: M) ->
      |-- B ; L
  (* additives *)  
  | ll2_plus1' : forall B M F G L, Permutation L ((AOr F G)::M) ->
      |-- B ; F::M -> |-- B ; L
  | ll2_plus2' : forall B M F G L, Permutation L ((AOr F G)::M) ->
      |-- B ; G::M -> |-- B ; L    
  | ll2_with' : forall B M F G L, Permutation L ((AAnd F G)::M) ->
      |-- B ; F :: M ->
      |-- B ; G :: M -> |-- B ; L      
  (* multiplicatives *)  
  | ll2_bot' : forall B M L, Permutation L (Bot :: M) ->
      |-- B ; M -> |-- B ; L
  | ll2_par' : forall B M F G L, Permutation L ((MOr F G) :: M) ->
      |-- B ; F::G::M -> |-- B ; L  
  | ll2_tensor' : forall B M N F G L, Permutation L ((MAnd F G)::(M ++ N)) ->
                                        |-- B ; F::M ->
                                        |-- B ; G::N ->
                                        |-- B ; L       
  (* exponentials *) 
  | ll2_quest' : forall B M F L, Permutation L ((Quest F) :: M) ->
      |-- F::B ; M -> |-- B ; L      
  | ll2_bang' : forall B F,
      |-- B ; [F] -> |-- B ; [Bang F]     
  (* structurals *)     
  | ll2_abs' : forall B L F, 
     In F B -> |-- B ; F::L -> |-- B ; L 
  where "'|--' B ';' L " := (LL2S B L).

  
 End LL2Sequent .

Global Hint Constructors LL2N : core .
Global Hint Constructors LL2S : core. 
 
Notation "'LL2' n '|--' B ';' L " := (LL2N n B L)  (at level 80).
Notation "'LL2' '|--' B ';' L " := (LL2S B L)  (at level 80).

