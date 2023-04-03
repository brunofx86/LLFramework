Require Export LL.PLL.Sequent.

(** Axioms *) 
 
Ltac LLinit Ax := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_init' with (A:=Ax);try perm
     | [|- LL2N _ _ _] => eapply @ll2_init  with (A:=Ax);try perm end;auto.
 
Ltac LLtop CXT := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_top' with (M:=CXT);try perm
     | [|- LL2N _ _ _] => eapply @ll2_top  with (M:=CXT);try perm end;auto.                       

(** Additives *)  

Ltac LLleft CF1 CF2 CTX := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_plus1' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL2N _ _ _] =>  eapply @ll2_plus1 with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.    
     
Ltac LLright CF1 CF2 CTX := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_plus2' with (F:=CF1) (G:=CF2) (M:=CTX);[try perm | ]
     | [|- LL2N _ _ _] =>  eapply @ll2_plus2 with (F:=CF1) (G:=CF2) (M:=CTX);[try perm | ]
                            end;auto.

Ltac LLwith CF1 CF2 CTX := match goal with
     | [ |- LL2S _ _ ] => eapply @ll2_with' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL2N _ _ _] => eapply @ll2_with with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.
     
(** Multiplicatives *) 

Ltac LLbot CXT := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_bot' with (M:=CXT);try perm
     | [|- LL2N _ _ _] => eapply @ll2_bot  with (M:=CXT);try perm end;auto.   
     
Ltac LLpar CF1 CF2 CTX := match goal with
     | [ |- LL2S _ _ ] => eapply @ll2_par' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL2N _ _ _] => eapply @ll2_par with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.

Ltac LLtensor CF1 CF2 CTX1 CTX2 := match goal with
     | [ |- LL2S _ _ ] => eapply @ll2_tensor' with (F:=CF1) (G:=CF2) (M:=CTX1) (N:=CTX2);try perm
     | [|- LL2N _ _ _] => eapply @ll2_tensor with (F:=CF1) (G:=CF2) (M:=CTX1) (N:=CTX2);try perm end;auto.
     
(** Exponentials *)

Ltac LLstore CF CXT  := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_quest' with (F:=CF) (M:=CXT); try perm
     | [|- LL2N _ _ _] => eapply @ll2_quest  with (F:=CF) (M:=CXT);try perm end;auto.  
     
Ltac LLbang := match goal with
     | [ |- LL2S _ _ ] =>  apply ll2_bang'
     | [|- LL2N _ _ _] =>  apply ll2_bang
                            end;auto.
                                 
(** Structurals *)       

Ltac LLcopy CF := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_abs' with (F:=CF)
     | [|- LL2N _ _ _] => eapply @ll2_abs  with (F:=CF) end;auto.                     