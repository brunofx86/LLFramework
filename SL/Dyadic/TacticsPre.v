Require Export LL.SL.Dyadic.Sequent.


Ltac LL2init Ax := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_init' with (A:=Ax);try perm
     | [|- LL2N _ _ _] => eapply @ll2_init  with (A:=Ax);try perm end;auto.
 
Ltac LL2top CXT := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_top' with (M:=CXT);try perm
     | [|- LL2N _ _ _] => eapply @ll2_top  with (M:=CXT);try perm end;auto.                       

Ltac LL2bot CXT := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_bot' with (M:=CXT);try perm
     | [|- LL2N _ _ _] => eapply @ll2_bot  with (M:=CXT);try perm end;auto.                       

Ltac LL2store CF CXT  := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_quest' with (F:=CF) (M:=CXT); try perm
     | [|- LL2N _ _ _] => eapply @ll2_quest  with (F:=CF) (M:=CXT);try perm end;auto.                       

Ltac LL2copy CF := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_abs' with (F:=CF)
     | [|- LL2N _ _ _] => eapply @ll2_abs  with (F:=CF) end;auto.                       

                          
Ltac LL2par CF1 CF2 CTX := match goal with
     | [ |- LL2S _ _ ] => eapply @ll2_par' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL2N _ _ _] => eapply @ll2_par with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.

Ltac LL2tensor CF1 CF2 CTX1 CTX2 := match goal with
     | [ |- LL2S _ _ ] => eapply @ll2_tensor' with (F:=CF1) (G:=CF2) (M:=CTX1) (N:=CTX2);try perm
     | [|- LL2N _ _ _] => eapply @ll2_tensor with (F:=CF1) (G:=CF2) (M:=CTX1) (N:=CTX2);try perm end;auto.

Ltac LL2with CF1 CF2 CTX := match goal with
     | [ |- LL2S _ _ ] => eapply @ll2_with' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL2N _ _ _] => eapply @ll2_with with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.
                         
Ltac LL2plus1 CF1 CF2 CTX := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_plus1' with (F:=CF1) (G:=CF2) (M:=CTX);try perm
     | [|- LL2N _ _ _] =>  eapply @ll2_plus1 with (F:=CF1) (G:=CF2) (M:=CTX);try perm end;auto.    
     
Ltac LL2plus2 CF1 CF2 CTX := match goal with
     | [ |- LL2S _ _ ] =>  eapply @ll2_plus2' with (F:=CF1) (G:=CF2) (M:=CTX);[try perm | ]
     | [|- LL2N _ _ _] =>  eapply @ll2_plus2 with (F:=CF1) (G:=CF2) (M:=CTX);[try perm | ]
                            end;auto.

Ltac LL2bang := match goal with
     | [ |- LL2S _ _ ] =>  apply ll2_bang'
     | [|- LL2N _ _ _] =>  apply ll2_bang
                            end;auto.

Ltac LL2exist tt CF CTX := match goal with
     | [ |- LL2S _ _ ] => eapply @ll2_ex' with (t:=tt) (FX:=CF) (M:=CTX) ;[try perm | auto | auto | ]
     | [|- LL2N _ _ _] => eapply @ll2_ex with (t:=tt) (FX:=CF) (M:=CTX);[try perm | auto | auto | ] end;auto.

Ltac LL2forall CF CTX := match goal with
     | [ |- LL2S _ _ ] => eapply @ll2_fx' with (FX:=CF) (M:=CTX) ;[try perm | auto | intros ]
     | [|- LL2N _ _ _] => eapply @ll2_fx with (FX:=CF) (M:=CTX) ;[try perm | auto | intros ] end;auto.
