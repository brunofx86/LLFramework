Require Export LL.SL.DyadicExc.Sequent.


Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(** Axioms *)

Ltac LL3init := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_init'
       | [|- LL3N _ _ _] => eapply @ll3_init end;auto.
 

Ltac LL3top := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_top'
       | [|- LL3N _ _ _] => eapply @ll3_top end;auto.                               

(** Additives *)

Ltac LL3plus1 := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_plus1'
       | [|- LL3N _ _ _] =>  eapply @ll3_plus1 end;auto.

Ltac LL3plus2 := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_plus2'
       | [|- LL3N _ _ _] =>  eapply @ll3_plus2 end;auto.

Ltac LL3with := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_with'
       | [|- LL3N _ _ _] => eapply @ll3_with end;auto.
       
(** Multiplicatives *)

Ltac LL3bot := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_bot'
       | [|- LL3N _ _ _] => eapply @ll3_bot end;auto.  
       
Ltac LL3par := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_par'
       | [|- LL3N _ _ _] => eapply @ll3_par end;auto. 

Ltac LL3tensor := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_tensor'
       | [|- LL3N _ _ _] => eapply @ll3_tensor end;auto.
                    
(** Exponentials *)

Ltac LL3store := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_quest'
       | [|- LL3N _ _ _] => eapply @ll3_quest end;auto.                       

Ltac LL3bang := match goal with
       | [ |- LL3S _ _ ] => eapply ll3_bang'
       | [|- LL3N _ _ _] => eapply ll3_bang end;auto.
       
(** Quantifiers *)

Ltac LL3exist tt := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_ex' with (t:=tt)
       | [|- LL3N _ _ _] => eapply @ll3_ex with (t:=tt) end;auto.

Ltac LL3forall := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_fx';intros
       | [|- LL3N _ _ _] => eapply @ll3_fx;intros end;auto.
       
(** Structurals *)
    
Ltac LL3copy CF := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_abs' with (F:=CF)
       | [|- LL3N _ _ _] => eapply @ll3_abs  with (F:=CF) end;auto.                       

Ltac LL3exchangeL CX := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_exh' with (M:=CX);try perm
       | [|- LL3N _ _ _] => eapply @ll3_exh with (M:=CX);try perm end;auto.                        