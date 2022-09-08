Require Export LL.SL.Monadic.Sequent.


Ltac LL1init Ax := match goal with
     | [ |- LL1S _ ] =>  eapply @ll1_init' with (A:=Ax);try perm
     | [|- LL1N _ _] => eapply @ll1_init  with (A:=Ax);try perm end;auto.
 
Ltac LL1top CXT := match goal with
     | [ |- LL1S _ ] =>  eapply @ll1_top' with (M:=CXT);try perm
     | [|- LL1N _ _] => eapply @ll1_top  with (M:=CXT);try perm end;auto.                       

Ltac LL1bot CXT := match goal with
     | [ |- LL1S _ ] =>  eapply @ll1_bot' with (M:=CXT);try perm
     | [|- LL1N _ _] => eapply @ll1_bot  with (M:=CXT);try perm end;auto.                       

Ltac LL1store CF CXT  := match goal with
     | [ |- LL1S _ ] =>  eapply @ll1_quest' with (F:=CF) (M:=CXT); try perm
     | [|- LL1N _ _] => eapply @ll1_quest  with (F:=CF) (M:=CXT);try perm end;auto.                       

Ltac LL1bang CF CM := match goal with
     | [ |- LL1S _ ] =>  eapply @ll1_bang' with (F:=CF) (M:=CM)
     | [|- LL1N _ _] => eapply @ll1_bang  with (F:=CF) (M:=CM) end;auto.                       
 
                          
Ltac LL1par CF1 CF2 CTX := match goal with
     | [ |- LL1S _ ] => eapply @ll1_par' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL1N _ _] => eapply @ll1_par with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.

Ltac LL1tensor CF1 CF2 CTX1 CTX2 := match goal with
     | [ |- LL1S _ ] => eapply @ll1_tensor' with (F:=CF1) (G:=CF2) (M:=CTX1) (N:=CTX2);try perm
     | [|- LL1N _ _] => eapply @ll1_tensor with (F:=CF1) (G:=CF2) (M:=CTX1) (N:=CTX2);try perm end;auto.

Ltac LL1with CF1 CF2 CTX := match goal with
     | [ |- LL1S _ ] => eapply @ll1_with' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL1N _ _] => eapply @ll1_with with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.
                         
Ltac LL1plus1 CF1 CF2 CTX := match goal with
     | [ |- LL1S _ ] =>  eapply @ll1_plus1' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL1N _ _] =>  eapply @ll1_plus1 with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.    
     
Ltac LL1plus2 CF1 CF2 CTX := match goal with
     | [ |- LL1S _ ] =>  eapply @ll1_plus2' with (F:=CF1) (G:=CF2) (M:=CTX);[try perm | ]
     | [|- LL1N _ _] =>  eapply @ll1_plus2 with (F:=CF1) (G:=CF2) (M:=CTX);[try perm | ]
                            end;auto.

Ltac LL1exist tt CF CTX := match goal with
     | [ |- LL1S _ ] => eapply @ll1_ex' with (t:=tt) (FX:=CF) (M:=CTX) ;[try perm | auto | auto | ]
     | [|- LL1N _ _] => eapply @ll1_ex with (t:=tt) (FX:=CF) (M:=CTX);[try perm | auto | auto | ] end;auto.

Ltac LL1forall CF CTX := match goal with
     | [ |- LL1S _ ] => eapply @ll1_fx' with (FX:=CF) (M:=CTX) ;[try perm | auto | intros ]
     | [|- LL1N _ _] => eapply @ll1_fx with (FX:=CF) (M:=CTX) ;[try perm | auto | intros ] end;auto.


Ltac LL1weak CF CTX := match goal with
     | [ |- LL1S _ ] => eapply @ll1_weak' with (F:=CF) (M:=CTX) ;[try perm | ]
     | [|- LL1N _ _] => eapply @ll1_weak with (F:=CF) (M:=CTX) ;[try perm | ] end;auto.

Ltac LL1contr CF CTX := match goal with
     | [ |- LL1S _ ] => eapply @ll1_contr' with (F:=CF) (M:=CTX) ;[try perm | ]
     | [|- LL1N _ _] => eapply @ll1_contr with (F:=CF) (M:=CTX) ;[try perm | ] end;auto.
