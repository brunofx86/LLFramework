
Require Import LL.Framework.SL.FLL.PreTactics.

Set Implicit Arguments.

(* Create HintDb LLBase.
 *)
Section FLLAuxiliar.
  Context `{OLS: OLSig}.

 Variable th : oo -> Prop.

Section Axioms.

 Example Axiom1 A B : FLLS th B [] (UP [atom A;perp A]).
 Proof. solveLL. Qed.   
 
 Example Axiom2 A B : FLLS th B [] (UP [perp A;atom A]).
 Proof. solveLL. Qed.  
 
 Example Axiom3 A B : FLLS th B [perp A] (UP [atom A]).
 Proof. solveLL. Qed.  

 Example Axiom4 A B : FLLS th B [perp A] (DW (atom A)).
 Proof. solveLL. Qed.  
 
 Example Axiom5 A B : FLLS th B [atom A] (UP [perp A]).
 Proof. solveLL. Qed.  

 Example Axiom6 A B : FLLS th (atom A ::B) [perp A] (UP []).
 Proof. solveLL. Qed.
 
 Example Axiom7 A B : FLLS th (atom A ::B) [] (UP [perp A]).
 Proof. solveLL. Qed.
 
 Example Axiom8 A B : FLLS th (atom A ::B) [] (DW(perp A)).
 Proof. solveLL.  Qed.
 
 Example Axiom9 A B : FLLS th (atom A ::B) [] (DW(perp A)).
 Proof. solveLL.  Qed.
 
 Example UnFocusOne B : FLLS th B [] (UP [One]).
 Proof. solveLL.  Qed.
 
 Example UnFocusOne' B : FLLS th B [One] (UP []).
 Proof. solveLL.  Qed.
 
 
End Axioms.
 
  Lemma FocusZero B L : FLLS th B L (DW (Zero)) -> False.
  Proof.
  intros. 
  solveLL.
 Qed.
 
 

End FLLAuxiliar.


   
 
  