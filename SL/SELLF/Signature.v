Require Export LL.Misc.UtilsTactics.

Require Export Coq.Classes.SetoidDec.

Require Export Coq.Classes.RelationClasses.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.DecidableClass.
Require Import Coq.Logic.FunctionalExtensionality.


(** ** Subexponential Signature

This class defines the set of indices that can be used in subexponentials. 
For each of them, it is possible to define the axioms (D,T 4) that
it features and whether it is linear or unbounded 

*)
Class Signature :=
  { 
    subexp: Set;
    lt : relation subexp ; (* < relation of the preorder *)
    lt_pre : PreOrder lt ; (* < is a preorder *)
    lt_dec : forall x y, {lt x  y} + {~ lt x  y}; (* < is decidable *)
    
    u : subexp -> bool ;
   
    (* closure condition *)
    uClosure : forall x y,u x = true -> lt x y -> u y = true;                                               
  }.
  
#[global] Instance Lt_Reflexive `{Signature} : Reflexive lt.
Proof. apply @PreOrder_Reflexive;eauto. exact lt_pre. Qed.

#[global] Instance Lt_Transitive `{Signature} : Transitive lt.
Proof.  apply @PreOrder_Transitive;eauto. exact lt_pre. Qed.

(* All subexponentials are unbouded *)
Class UnbSignature `{Signature}:=
  { 
    allU: forall x, u x = true; }.

Section LLSignature.
 
  Context `{SI : Signature}.
  
    Lemma subDec sub : forall x:subexp, {sub x = true} + {sub x = false}.
  Proof.
   intros;eauto using Sumbool.sumbool_of_bool.
  Qed.  

  Lemma uDec : forall x, {u x = true} + {u x = false}.
  Proof.
   intros;eauto using Sumbool.sumbool_of_bool.
  Qed.
   
  End LLSignature.
  
 



