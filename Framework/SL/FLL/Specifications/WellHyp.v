Require Export LL.Framework.SL.FLL.Specifications.CutCoherence.
Require Export LL.Framework.SL.FLL.Specifications.Requirement1.

Set Implicit Arguments.

Section OLCutHyp.

  Context `{OLR: OORules}.
 
  (** As a general hypothesis, we assume that the Object logic is cut-coherent *)
  Variable LTWell1 : wellFormedTheory.
  Variable LTCutCoherence: CutCoherence cutR1.
   
  Definition ctWellFormed := proj1 LTWell1.
  Definition unWellFormed := proj1 (proj2 LTWell1).
  Definition biWellFormed := proj1 (proj2 (proj2 LTWell1)).
  Definition quWellFormed := proj2 (proj2 (proj2 LTWell1)).

  Definition ctCutCo := proj1 LTCutCoherence.
  Definition unCutCo := proj1 (proj2 LTCutCoherence).
  Definition biCutCo := proj1 (proj2 (proj2 LTCutCoherence)).
  Definition quCutCo := proj2 (proj2 (proj2 LTCutCoherence)).

End OLCutHyp.

   (** Extracting the needed facts given that all the OL constants are well-defined *)
   Ltac wellConstant Hw HSeq :=
    let HS := type of HSeq in
    match HS with
    | FLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C)) =>
      let Side' :=
          match Side with 
          makeRRuleC => Right
           | makeLRuleC => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize (ctWellFormed Hw Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ];
          destruct bpEnum;[ apply LTWell' in HSeq; contradiction (* fail case *)
                          | generalize (LTWell' _ HSeq);intro;clear LTWell' (* axiom *)
                          | generalize (LTWell' _ HSeq);intro;clear LTWell'] (* one premise *)
    end.
 
  Ltac wellUnary Hw HSeq  :=
    let HS := type of HSeq in
    match HS with
    | (FLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with 
          makeRRuleU => Right 
          | makeLRuleU => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize  (unWellFormed Hw Rules Gamma M C Side' );
        intro LTWell';generalize (LTWell' _ _ HSeq);intro;clear LTWell'
    end.
 
  (** Extracting well-formed conditions for binary predicates *)
  Ltac wellBinary Hw HSeq :=
    let HS := type of HSeq in
    match HS with
    | (FLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F ?G))) =>
      let Side' :=
          match Side with makeRRuleB => Right | makeLRuleB => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
        generalize (biWellFormed Hw Rules Gamma M C Side' );intro LTWell';
        destruct LTWell' as [bpEnum  LTWell' ]; 
        destruct bpEnum;generalize (LTWell' _ _ _ HSeq);intro;clear LTWell'
    end.

  Ltac wellQuantifier Hw HSeq :=
    let HS := type of HSeq in
    match HS with
    | (FLLN ?Rules ?n ?Gamma ?M (DW (?Side ?C ?F))) =>
      let Side' :=
          match Side with makeRRuleQ => Right | makeLRuleQ => Left end in
        let LTWell' := fresh "LTWell'" in
        let bpEnum := fresh "bpEnum" in 
         let HUniform := fresh "HUniform" in
        generalize  (quWellFormed Hw Rules Gamma M C Side' F); intro LTWell';
      generalize (LTWell' _ HSeq); intro;clear LTWell'  
    end.
