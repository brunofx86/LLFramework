Require Export LL.Misc.UtilsTactics.
Require Export LL.Misc.Database.

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
Class SigSELL :=
  { 
    subexp: Set;
    lt : relation subexp ; (* relation on subexp *)
    lt_pre : PreOrder lt ; (* "lt" is a preorder *)
    lt_dec : forall x y, {lt x  y} + {~ lt x  y}; (* "lt" is decidable *)
    I : list subexp;
    un : list subexp;
    (* unbounded labels *)
    u : subexp -> bool ;
   
    (* closure condition *)
    uClosure : forall x y,u x = true -> lt x y -> u y = true  
   }.
  
#[global] Instance Lt_Reflexive `{SigSELL} : Reflexive lt.
Proof. apply @PreOrder_Reflexive;eauto. exact lt_pre. Qed.

#[global] Instance Lt_Transitive `{SigSELL} : Transitive lt.
Proof.  apply @PreOrder_Transitive;eauto. exact lt_pre. Qed.

(* All subexponentials are unbouded *)
Class USigSELL `{SigSELL}:=
  { 
    allU: forall x, u x = true }.

Section SELLSignature.
 
  Context `{SI : SigSELL}.
  
  (** Decidibility on modalities *)
  Lemma subDec sub : forall x:subexp, {sub x = true} + {sub x = false}.
  Proof.
   intros;eauto using Sumbool.sumbool_of_bool.
  Qed.  
  
  Lemma uDec : forall x, {u x = true} + {u x = false}.
  Proof.
  apply subDec.
  Qed.
    
  End SELLSignature.
  
  Global Hint Resolve lt_pre uClosure allU:core.
