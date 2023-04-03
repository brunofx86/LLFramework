Require Export LL.FOLL.DyadicExc.Sequent.


Module DyadicExcTactics.

(** Axioms *)

Ltac LLinit := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_init'
       | [|- LL3N _ _ _] => eapply @ll3_init end;auto.
 

Ltac LLtop := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_top'
       | [|- LL3N _ _ _] => eapply @ll3_top end;auto.                               

(** Additives *)

Ltac LLleft := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_plus1'
       | [|- LL3N _ _ _] =>  eapply @ll3_plus1 end;auto.

Ltac LLright := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_plus2'
       | [|- LL3N _ _ _] =>  eapply @ll3_plus2 end;auto.

Ltac LLwith := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_with'
       | [|- LL3N _ _ _] => eapply @ll3_with end;auto.
       
(** Multiplicatives *)

Ltac LLbot := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_bot'
       | [|- LL3N _ _ _] => eapply @ll3_bot end;auto.  
       
Ltac LLpar := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_par'
       | [|- LL3N _ _ _] => eapply @ll3_par end;auto. 

Ltac LLtensor := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_tensor'
       | [|- LL3N _ _ _] => eapply @ll3_tensor end;auto.
                    
(** Exponentials *)

Ltac LLstore := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_quest'
       | [|- LL3N _ _ _] => eapply @ll3_quest end;auto.                       

Ltac LLbang := match goal with
       | [ |- LL3S _ _ ] => eapply ll3_bang'
       | [|- LL3N _ _ _] => eapply ll3_bang end;auto.
       
(** Quantifiers *)

Ltac LLexists tt := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_ex' with (t:=tt)
       | [|- LL3N _ _ _] => eapply @ll3_ex with (t:=tt) end;auto.

Ltac LLforall := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_fx';intros
       | [|- LL3N _ _ _] => eapply @ll3_fx;intros end;auto.
       
(** Structurals *)
    

Ltac LLcopy CF := match goal with
       | [ |- LL3S _ _ ] =>  eapply @ll3_abs' with (F:=CF)
       | [|- LL3N _ _ _] => eapply @ll3_abs  with (F:=CF) end;auto.                       

Ltac LL3exchangeL CX := match goal with
       | [ |- LL3S _ _ ] => eapply @ll3_exh' with (M:=CX);try perm
       | [|- LL3N _ _ _] => eapply @ll3_exh with (M:=CX);try perm end;auto.      

End DyadicExcTactics.
                  