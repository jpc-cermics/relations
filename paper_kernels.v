(* -*- Encoding : utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & datest) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot seq order boolp classical_sets contra. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".

From RL Require Import  seq1 seq2 rel paper_kernels_common 
        paper_monochromatic_f.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section CheckAsym. 
  (** * Import main result from paper_monochromatic_f *)
  Context {T : choiceType} (U: relation T).
  Hypothesis A1: (nonempty [set: T]).

  Import Asyminf2Inf(Asym2P5', allL_rc_asym).

  (* begin snippet infasym:: no-out *) 
  Lemma iic_asym_to_iic_inj:  (iic (Asym U.+)) -> (iic_inj U). 
  (* end snippet infasym *)  
  Proof. by apply: (@Asym2P5' T U A1). Qed.

  Lemma not_iic_inj_to_not_iic_asym: ~ (iic_inj U) -> ~ (iic (Asym U.+)).
  Proof. by move => ? /iic_asym_to_iic_inj ?. Qed.

End  CheckAsym. 

Module Generalized_SSW. 
  (** * Generalized SSW Theorem for infinite case*)
  Section Generalized_SSW.
    (** * Existence of a Maximal in the infinite case with Zorn Lemma *)
    (** * we need [<= O] to be a porder *)

    Context {T:choiceType} (R B O: relation T).

    Notation M := (B `|` R).
    
    Context (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O)
      (A4: Assumption4 O) (A5: Assumption5 O M) (A6: Assumption6 B M O)
      (A7: Assumption7 R B M) (A8: Assumption8 R B M) (A9: Assumption9 R B O M).
        
    (* begin snippet MainTh:: no-out *)    
    Theorem G_SSW: exists S, kernel M S.
    (* end snippet MainTh:: no-out *)    
    Proof.
      (* a Maximal set using Zorn Lemma *)
      move: (Maximal_Zorn A1 A2 A3 A4 A5 A9) => [Sm [/set_mem Hpk Hmax]].
      (* The Maximal set is absorbant using the extend Lemma *)
      have Hsmabs: ~ (absorbant M Sm) -> False.
      {
        move => Hna.
        move: (extend A2 A6 A7 A8 Hpk Hna) => [X' [/mem_set H4 [/DeltaCP Hne Hle]]]. 
        move: H4 Hle => /Hmax H4 /H4 Heq.
        by rewrite -Heq in Hne.
      }
      
      exists Sm. split;first by move: Hpk => [? _].
      by apply/not_notP => /Hsmabs.
    Qed.
  End Generalized_SSW.
End Generalized_SSW.

Export Generalized_SSW(G_SSW).

Module Generalized_SSW_fin_notcyclic.
  Section Generalized_SSW_fin_notcyclic.
    (** * Generalized_SSW for finType and no cyclicity *)
    
    Context {T: finType} (O R B: relation T).

    Definition M := B `|` R.

    Context (A2: Assumption2 R) (A6: Assumption6 B M O)
      (A7: Assumption7 R B M) (A8: Assumption8 R B M). 
    Context (A1: nonempty [set: T]) (Au: R `<=` O^-1).
    Context (Apk : forall X , RelIndep O X <-> RelIndep M X).
    Context (A_Onotcyclic: ~ (exists s, O.+ (s,s))).
    
    (* There exists a kernel or an increasing mapping for [<< O] taking values in pre_kernels *)
    Lemma kernel_or_iic_fun:
      (exists h, (iic_fun ([<< O]%O) h) /\ (forall n, (h n) \in  (pre_kernel M R M)))
      \/ (exists S, (S \in (pre_kernel M R M)) /\ S \in (absorbant M)).
    Proof.
      (* using extend lemma *)
      have Ch0 S: S \in ((pre_kernel M R M) `&` (absorbant M).^c)
                 -> exists S', S' \in (pre_kernel M R M) /\ (S [<< O] S').
      {
        rewrite inE => -[Hpk Hna].
        move: (@extend T R B O S A2 A6 A7 A8 Hpk Hna) 
            => [S' [/mem_set Hpk' Hlt]].
        by exists S'. 
      }
      have Ch1 : exists S, S \in (pre_kernel M R M).
      {
        have Oinv_notcyclic: ~ (exists s, O^-1.+ (s,s))
          by rewrite -TclosIv.
        (* exists a sink and thus a preabsorbant node *)
        move: (@NotCyclic_exists_preabsorbant T O^-1 M A1 Oinv_notcyclic) => [v Hpa].
        (* [set v] is in (pre_kernel M R M). *)
        exists [set v]%classic;rewrite inE. 
        have Hinc:  (v)_:#R  `<=` (v)_:#O^-1 
          by rewrite /Aset;apply: Fset_inc;apply: inverseS.
        split;first by apply: RelIndep_set1.
        split;first by apply: (subset_trans Hinc _).
        + apply/negP => /eqP H.
          have Hv: [set v]%classic v by [].
          by rewrite H /= in Hv.
      }
      move: (@choose_sub _ ([<< O]%O) (pre_kernel M R M) (absorbant M).^c Ch0 Ch1)
          => [Hiic | [S [Hpk Hna]]].
      by left.
      by right;exists S;split;[| move: Hna;rewrite 2!inE /= => /contrapT].
    Qed.
    
    (* we prove that the existence of an increasing mapping for [<< O]
       taking values in pre_kernels would contradict acyclicity
     *)
    
    Lemma iic_to_allL  (h : nat -> (set T)):  
      (iic_fun ([<< O]%O) h) -> (forall n, (h n) \in  (pre_kernel O R M)) ->
      exists n p, h n = h (n+p+1)
             /\ allL ([<< O]%O) (mkseq (fun i => h (n + i+1)) p) (h n) (h n)
             /\ ((h n)::(mkseq (fun i => h (n + i+1)) p)) [\in] (pre_kernel O R M).
    Proof. 
      move => Hiic_fun Hpk.
      (* non injectivity prop as T is finType *)
      have [n [m Heq]]:  exists n p : nat, h n = h (n + p.+1)
          by apply: set_fin_codomain_prop.
      move: Hiic_fun => /f2allL /(_ n m) HallL.
      rewrite -addn1 addnA in Heq;rewrite -Heq in HallL. 
      by exists n, m;split;[|split;[|apply: f2in]].
    Qed.
    
    Lemma iic_and_prekernels_to_cyclic (h : nat -> (set T)):
      (iic_fun ([<< O]%O) h) -> (forall n, (h n) \in  (pre_kernel O R M))
      -> exists s, O.+ (s,s).
    Proof.
      move => Hiic Hpk';move: (iic_to_allL Hiic Hpk') => [n [p [Ha [HallL Hpk]]]].
      by apply: (Cyclicity_BH_lemma HallL Hpk).
    Qed.
    
    Theorem G_SSW_fin_notcyclic: exists S, kernel M S.
    Proof.
      have pre_kernelP S': pre_kernel O R M S' <-> pre_kernel M R M S'
        by rewrite /pre_kernel /= Apk.
      have: exists S, S \in (pre_kernel M R M) /\ S \in (absorbant M).
      {
        move: kernel_or_iic_fun => [[h [Hiic Hk]] | H1];last by [].
        have HpkO: (forall n, (h n) \in  (pre_kernel O R M))
          by move => n; rewrite inE pre_kernelP -inE.
        by move: (iic_and_prekernels_to_cyclic Hiic HpkO) => HOcyclic.
      }
      by move => [S [/set_mem [Hk _] /set_mem Habs]];exists S.
    Qed.
    
  End Generalized_SSW_fin_notcyclic.
End Generalized_SSW_fin_notcyclic.

Export Generalized_SSW_fin_notcyclic(G_SSW_fin_notcyclic).

Module Generalized_SSW_fin_porder.
  Section Generalized_SSW_fin_porder.
    (** * finType cases *)
    (** * Extended Champetier *)
    
    Context (T : finType) (O R B: relation T).
    Implicit Types (O R B: relation T). 
  
    Notation M := (B `|` R).

    Context (A2 : Assumption2 R) (A6 : Assumption6 B M O) 
    (A7 : Assumption7 R B M) (A8 : Assumption8 R B M).
    Context (A1: nonempty [set: T]) (Asp: sporder O) (Au: R `<=` O^-1).
    Context (Apk : forall X, RelIndep O X <->  RelIndep M X).
  
    Lemma maximal_mabsorbant S:
      (pre_kernel O R M S) /\ (forall U, pre_kernel O R M U -> S [<= O] U -> S = U)
      -> absorbant M S.
    Proof.
      contra; move => H1;rewrite /pre_kernel /= Apk => Hpk.
      have H3: ~ absorbant M S.
      {
        move: H1 => [y H1] H3.
        rewrite notin_setE in H3.
        rewrite /absorbant /mkset => /(_ y) H4. 
        by move: H1 => /H4;rewrite inE => H1.
      }
      move: (@extend T R B O S A2 A6 A7 A8 Hpk H3)
          => [S' [Hpre [/DeltaCP H7 Hne]]].
      exists S';first by rewrite (Apk S').
      by split;[| apply/negP => /eqP Heq].
    Qed.
    
    Lemma G_SSW_fin_porder: exists S, kernel M S. 
    Proof.
      (* There exist a maximal set *)
      move: (@Maximal T O R M A1 Asp Au) => [S Hm].
      move: Hm => /[dup] /maximal_mabsorbant Ma [[/Apk Hpk _] _]. 
      by (exists S).
    Qed.
  End Generalized_SSW_fin_porder.
End Generalized_SSW_fin_porder.

Export Generalized_SSW_fin_porder(G_SSW_fin_porder).

Module SSWext.
  (** * use G_SSW to prove kernel existence in infinite graphs *)
  (** * The Extended SSW Theorem and the SSW theorem as a corollary *)
  Parameter (T:choiceType) (Eb Er: relation T).

  Definition R := Er.+. 
  Definition B := Eb.+. 
  Definition O := (Asym B). 

  Definition SSW_1:= (nonempty [set: T]).
  Definition SSW_2:= ~ (iic (Asym R)).
  Definition SSW_3:= ~ (iic (Asym B)).
  
  Notation M := (B `|` R).
  
  Lemma R_trans: transitive R.
  Proof. by apply: (@TclosT _ Er). Qed.

  Lemma B_trans: transitive B.
  Proof. by apply: (@TclosT _ Eb). Qed.
  
  Lemma L4: (Assumption4 O). 
  Proof. by apply: (@Asym_sporder _ B);apply: TclosT. Qed.
  
  Lemma L5: (Assumption5 O M).
  Proof. 
    have H1: O `<=` M
      by apply: (@subset_trans _ B _ _ (@AsymI _ B)
                   (@subsetUl _ B R)).
    by pose proof (@subset_trans _ _ O _  H1 (@subsetUl _ M M^-1)).
  Qed.
  
  Lemma L6: (Assumption6 B M O).
  Proof. move => x y [? ?];split;first exact.
         move => ?; by have: M (y, x) by left.
  Qed.

  Lemma L7: (Assumption7 R B M).
  Proof. 
    move => x x' y y' H1 H2 [H3|H3] H4 H5 H6 H7 H8 H9.
    by left;apply: (B_trans H3 H4).
    by have: M (x,x') by right;apply: (R_trans H2 H3).
  Qed.
  
  Lemma L8: (Assumption8 R B M).
  Proof. 
    move => x' y y' B0 B0' B0'' H1 [H2| H2] H3 [H4 H5].
    by left;apply: (B_trans H2 H3).
    by have H11: M (y,x') by right;apply: (R_trans H1 H2).
  Qed.
  
  Lemma L9: (Assumption9 R B O M).
  Proof. 
    move =>  x y x' y' P0 P1 P2 P3 P4 P5 H1 [H2|H2] H3 H4 H5 H6.
    by move: H3 => /(@AsymI _ B) H3;left;apply: (B_trans H2 H3).
    by have: (M `|` M^-1) (x',x) by right;right;apply: (R_trans H1 H2).
  Qed.
  
  Theorem SSWext
    (A1: SSW_1) (A2: SSW_2) (A3: SSW_3):
    exists X, RelIndep M X /\  absorbant M X.
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 A3 L4 L5 L6 L7 L8 L9).
  Qed.

  Corollary SSW
    (A1: SSW_1) (A2': ~ (iic_inj Er)) (A3': ~ (iic_inj Eb)):
    exists S, RelIndep M S /\  absorbant M S.
  Proof.
    move: A2' => /(not_iic_inj_to_not_iic_asym A1) A2'.
    move: A3' => /(not_iic_inj_to_not_iic_asym A1) A3'.
    by apply: SSWext.
  Qed.
  
  (* if x \in M#S there exists y \in S such that x and y are 
   *  connected by a Eb path or a Er path 
   *  This could be elsewhere.
   *)
  Lemma M2path x (S: set T): 
    x \in M#S -> exists y, y \in S /\ exists s, ~ x \in s /\ ~ y \in s /\ uniq s 
                                /\ (allL Eb s x y \/ allL Er s x y).
  Proof.
    rewrite inE /M /Fset => -[y [[H1 | H1] /mem_set H2]];(exists y;split;first by []).
    + move: H1 => /(@TCP_uniq T Eb) [s [H3 [H4 [H5 H6]]]].
      by (exists s;have H7: (allL Eb s x y \/ allL Er s x y) by left).
    + move: H1 => /(@TCP_uniq T Er) [s [H3 [H4 [H5 H6]]]].
      by (exists s;have H7: (allL Eb s x y \/ allL Er s x y) by right).
  Qed.
  
End SSWext.

Module ABkernels.
  (** * use G_SSW to prove kernel existence in infinite graphs *)
  (** * in the AB kernels case *)
  Parameter (T:choiceType) (A1 A2: relation T).

  Definition R := A1.
  Definition B := A2.
  Definition O := (Asym B). 

  Definition AB_1:= (nonempty [set: T]).
  Definition AB_2:= ~ (iic (Asym R)).
  Definition AB_3:= ~ (iic (Asym B)).
  Definition AB_4:= transitive R.
  Definition AB_5:= transitive B.

  Notation M := (B `|` R).

  Lemma L4 (A5: AB_5) : (Assumption4 O). 
  Proof. by apply: (@Asym_sporder _ B). Qed.
  
  Lemma L5: (Assumption5 O M).
  Proof. 
    have H1: O `<=` M 
      by apply: (@subset_trans _ B _ _ (@AsymI _ B)
                   (@subsetUl _ B R)).
    by pose proof (@subset_trans _ _ O _  H1 (@subsetUl _ M M^-1)).
  Qed.
  
  Lemma L6: (Assumption6 B M O).
  Proof. move => x y [? ?];split;first exact.
         move => ?; by have: M (y, x) by left.
  Qed.

  Lemma L7 (A4: AB_4) (A5: AB_5): (Assumption7 R B M).
  Proof. 
    move => x x' y y' H1 H2 [H3|H3] H4 H5 H6 H7 H8 H9.
    by left;apply: (A5 y' x' y H3 H4).
    by have: M (x,x') by right;apply: (A4 x y' x' H2 H3).
  Qed.
  
  Lemma L8 (A4: AB_4) (A5: AB_5): (Assumption8 R B M).
  Proof. 
    move => x' y y' B0 B0' B0'' H1 [H2| H2] H3 [H4 H5].
    by left;apply: (A5 y' x' y H2 H3).
    by have H11: M (y,x') by right;apply: (A4 y y' x' H1 H2).
  Qed.
  
  Lemma L9 (A4: AB_4) (A5: AB_5) : (Assumption9 R B O M). 
  Proof. 
    move =>  x y x' y' P0 P1 P2 P3 P4 P5 H1 [H2|H2] H3 H4 H5 H6.
    by move: H3 => /(@AsymI _ B) H3;left;apply: (A5 y x' y' H2 H3).
    by have: (M `|` M^-1) (x',x) by right;right;apply: (A4 x y x' H1 H2).
  Qed.

  Theorem AB_kernels
    (A1: AB_1) (A2: AB_2) (A3: AB_3) (A4: AB_4) (A5: AB_5):
    exists S, kernel M S.
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 A3 (L4 A5) L5 L6 (L7 A4 A5)
                     (L8 A4 A5) (L9 A4 A5)).
  Qed.
  
End ABkernels.

Module MeunierLanglois. 
  (** * use G_SSW to prove kernel existence in infinite graphs *)
  (** * for a modifieed version of Meunier Langlois *)

  Parameter (T:choiceType) (R B: relation T).

  Definition O := [set xy | (Asym B) (xy.1, xy.2) /\  ~ R (xy.2,xy.1)].
  Definition AB_1:= (nonempty [set: T]).
  Definition AB_2:= ~ (iic (Asym R)).
  Definition AB_3:= ~ (iic (Asym B)).
  Definition AB_4:=  forall x y z, 
      ~ (y = x) -> ~ (y = z) -> ~ (z = x)       
      -> R (x,y) -> R (y,z) -> R (x,z) \/ ( B (y,x) /\ B (z,x) ).
  
  Definition AB_5:=  forall x y z, 
      ~ (x = y) -> ~ (z = y) -> ~ (z = x)       
      -> B (x,y) -> B (y,z) -> B (x,z) \/ ( R (z,x) /\ R (z,y) ).

  (* a transitivity property for B `&` (B^-1 `|` R^-1) *)
  Definition AB_6:=  forall x y z, 
      B (x,y) -> ~ (B^-1 (x,y)) -> ~ (R (y,x)) 
      -> B (y,z) -> ~ (B^-1 (y,z)) -> ~ (R (z,y))
      -> B (x,z) /\ ~ (B^-1 (x,z)) /\ ~ (R (z,x)).

  Notation M := (B `|` R).
  
  Lemma L3 (A3: AB_3): (Assumption3 O).
  Proof.
    move: A3. contra => -[f H].
    by exists f;move => n;move: H => /(_ n) [/= H1 _].
  Qed.
  
  Lemma L4 (A5: AB_5) (A6: AB_6) : (Assumption4 O). 
  Proof. 
    split. 
    + move => x [/= H1 _].
      by pose proof (@Asym_irreflexive T B x). 
    + move => x y z [/= [H1 H1'] H2] [/= [H3 H3'] H4].
      move: (A6 x y z H1 H1' H2 H3 H3' H4) => [H5 [H6 H7]].
      by split. 
  Qed.
  
  Lemma L5: (Assumption5 O M).
  Proof. by move => [x y] [[/= ? _] _];left;left.  Qed.
  
  Lemma L6: (Assumption6 B M O).
  Proof.
    move => x y [H1 H2].
    split. 
    split. by []. move => /= H3.
    by have H4:  M (y, x) by left.
    move => /= H3.
    by have H4:  M (y, x) by right. 
  Qed.
  
  Lemma L7 (A4: AB_4) (A5: AB_5): (Assumption7 R B M).
  Proof. 
    move => x x' y y' H1 H2 [H3|H3] H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
    + left;move: (A5  y' x' y H12 H14 H10 H3 H4) => [? // | [_ H10']]. 
      (have H11': M(y,x') by right);by move : H6 => -[_ ?].
    + move: (A4 x y' x' H11 H12 H1 H2 H3) => [H10' | [_ H10']].
      by (have H11': M(x, x') by right). 
      by (have H11': M(x', x) by left).
  Qed.
  
  Lemma L8 (A4: AB_4) (A5: AB_5): (Assumption8 R B M).
  Proof. 
    move => x' y y' P0 P0' P0'' H1 [H2| H2] H3 [H4 H5].
    + left;move: (A5 y' x' y P0 P0'' P0' H2 H3) => [? // | [_ H6]].
      by have H11: M(y,x') by right.
    + have H6: y' <> y by move => I7;rewrite I7 in P0'.
      have H7: x' <> y by move => I7;rewrite I7 in P0''.
      
      move: (A4 y y' x' H6 P0 H7 H1 H2) => [H6' | [H6' _]].
      by have H11: M(y,x') by right.
      by left.
  Qed.
  
  Lemma L9 (A4: AB_4) (A5: AB_5) : (Assumption9 R B O M).
  Proof. 
    move =>  x y x' y' P0 P1 P2 P3 P4 P5 H1 [H2|H2] [[/= H3 /=H3'] /=H3''] H4 H5 H6.
    + have P4': ~ (y' = x') by move => I1;rewrite I1 in P4.
      move: (A5 y x' y' P3 P4' P5 H2 H3) => [? | [_ ?] //];first by left.
    + have P0': ~ (y = x) by move => I1;rewrite I1 in P0.
      have P1': ~ (x' = x) by move => I1;rewrite I1 in P1.
      move: (A4 x y x' P0' P3 P1' H1 H2) => [? | [? _]].
      by have: (M (x', x) \/ M^-1 (x', x)) by right;right.
      by have: M (y,x) by left.
  Qed.
  
  Theorem ML_inf
    (A1: AB_1) (A2: AB_2) (A3: AB_3) (A4: AB_4) (A5: AB_5) (A6: AB_6):
    exists S, kernel M S.
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 (L3 A3) (L4 A5 A6) 
                  L5 L6 (L7 A4 A5) (L8 A4 A5) (L9 A4 A5)).
  Qed.
  
End MeunierLanglois. 

Definition simpleGraph (T: Type) (G:relation T) := symmetric G /\ irreflexive G.
Definition Direction (T: Type) (G D: relation T) := D `|` D^-1 = G. 
Definition Orientation (T: Type) (G O: relation T) := Direction G O /\ asymmetric O.

Module  simpleGraph. 
  Section simpleGraph. 
  (** * simpleGraph orientation direction  definitions *)
  (** * and properties *)
  Context {T : Type}.
  Implicit Types (G D O Re: relation T).

  Lemma RelIndep_sym Re S: (RelIndep Re S) <-> (RelIndep (Re `|` Re^-1) S).
  Proof.
    split => [+ x y Hx Hy Hne|+ x y Hx Hy Hne].
    have Hne': ~ (y = x). by move => H1;rewrite H1 in Hne.
    by move => /[dup] /(_ y x Hy Hx Hne') H1 /(_ x y Hx Hy Hne) H2 [H3 | H3].
    by move => /(_ x y Hx Hy Hne);contra => ?;left.
  Qed.
  
  Lemma direction_relIndep G D S: 
    Direction G D -> (RelIndep D S <-> RelIndep G S).
  Proof. by move => Hd;rewrite RelIndep_sym Hd. Qed.

  Lemma orientation_relIndep G O S: 
    Orientation G O -> (RelIndep O S <-> RelIndep G S).
  Proof. by move => [Hd _];rewrite RelIndep_sym Hd. Qed.

  Lemma directionIv G D: Direction G D -> Direction G D^-1.
  Proof. by move => Hd;rewrite /Direction (inverseK D) setUC. Qed.

  Lemma directionIr G D: (simpleGraph G) -> Direction G D -> irreflexive D.
  Proof. 
    move => [_ +] Hd x => /(_ x) Hnotgxx.
    have: D `|` D^-1 `<=` G by rewrite Hd.
    rewrite subUset => -[Hdsub _] => /Hdsub. 
    by move => ?.
  Qed.
  
  Lemma orientationIv G O: Orientation G O -> Orientation G O^-1.
  Proof. by move => [/directionIv Hd /asymmetric_inv Has]. Qed.
  
  Context (G D O: relation T).
  Context (Ag: simpleGraph G).
  Context (Ad: Direction G D).
  Context (Ao: Orientation G O).

  Definition R := D `&` O.
  Definition B := D `&` O^-1.
  
  Lemma RB: (B `|` R) = D.
  Proof.
    have H1:  R `<=` D by rewrite /R;apply: subIsetl.
    have H2:  B `<=` D by rewrite /R;apply: subIsetl.
    rewrite predeqE => -[x y].
    split => [[/H2 H0 | /H1 H0] // | H3].
    case H4: ((x,y) \in O).
    + move: H4 => /set_mem H4.
      ++ case H5: ((y,x) \in O).
         move: H5 => /set_mem H5.
         by left;split.
         by right;split.
    + case H5: ((y,x) \in O).
      move: H5 => /set_mem H5.
      by left;split.
      (** (x, y) \in O) = false /\ (y, x) \in O) = false *)
      (** is not possible *)
      have H6: D `|` D^-1 = G by [].
      have H7: O `|` O^-1 = G by move: (Ao) => [Do _].
      have H8:  D `|` D^-1 = O `|` O^-1. by rewrite H6 H7. 
      have [ //| H9]: (O `|` O^-1) (x,y) by rewrite -H8; left.
      by rewrite -inE H4.
      have: (y,x) \in O by rewrite inE.  
      by rewrite H5.
  Qed.
  
  Lemma test: O `<=` D `|` D^-1.
  Proof.
    have Heq: O `|` O^-1 = D `|` D^-1 by move: Ao => [-> _].
    have: O `|` O^-1 `<=` D `|` D^-1  by rewrite Heq.
    by rewrite subUset => -[Hoinc _].
  Qed.

  Lemma test': O^-1 `<=` D `|` D^-1.
  Proof.
    have Heq: O `|` O^-1 = D `|` D^-1 by move: Ao => [-> _].
    have: O `|` O^-1 `<=` D `|` D^-1  by rewrite Heq.
    by rewrite subUset => -[_ Hoinc].
  Qed.

  Lemma test'' x y: O(x,y) -> B(y,x) \/ R(x,y).
  Proof. by move => /[dup] ? /test [?|?];[right|left]. Qed.
  
  End simpleGraph.
End simpleGraph.

Export simpleGraph.

Module Finite_case_Kernel_Theorems.
  Section Finite_case_Kernel_Theorems.

    Context (T : finType) (G D O: relation T).
    
    Definition Three_cycles := 
      forall x y z, D (x,y) -> D(y,z) -> D(z,x) -> ~ D(x,z) -> D(y,x).

    Definition R := D `&` O.
    Definition B := D `&` O^-1.

    (* we will show that M = D *)
    Notation M := (B `|` R).

    Definition Forbiden_graph :=
      forall x y z t, R (x,y) -> D(y,z) -> B(z,t) -> 
                 D(x,t) \/ D(t,x) \/ D(x,z) \/ D (z,x) \/ D(y,t) \/ D(t,y).

    Definition M_L_Forbiden_graph := forall x y z t,
      R (x,y) -> D(y,z) -> B(z,t) -> 
      (~ (t = x) /\ (D(x,t) \/ D(t,x) \/ D(x,z) \/ D (z,x) \/ D(y,t) \/ B(y,x) \/ R(t,z)))
      \/ ( t = x /\ (D(x,z) \/ B(y,x) \/ R(x,z))).
    
    Definition M_L_Forbiden_graph2 :=
      forall x y z, R (x,y) -> D(y,z) -> B(z,x) -> 
               D(x,z) \/ B(y,x) \/ R(x,z).
    
    Context (A1: nonempty [set: T]).
    Context (Asg: simpleGraph G).
    Context (Ao: Orientation G O).
    Context (Ad: Direction G D).
    
    Lemma Au:  R `<=` O. 
    Proof. by rewrite /R;apply: subIsetr. Qed.

    Lemma Au':  R `<=` O^-1^-1. 
    Proof. by move: Au;rewrite (inverseK O). Qed.
           
    Lemma Rnotiic (Asp: sporder O): ~ (iic R).
    Proof. 
      have: ~ (iic  O) by apply: (@fin_not_iic _ O Asp).              
      by move => notHiicO /(@iic_sub T R O (Au)) HiicO.
    Qed.
    
    Lemma Apk:  forall X , RelIndep O^-1 X <->  RelIndep M X.
    Proof.
      move: Ao => [/directionIv DOm1 _] X. 
      rewrite (RB Ad Ao) (@direction_relIndep T G D X Ad).
      by rewrite (@direction_relIndep T G O^-1 X DOm1).
    Qed.
    
    Lemma Rasym : asymmetric R.
    Proof.
      move => x y /Au H1 /Au H2.
      by move: H1 Ao => + [_ /(_ x y) Ha] => /Ha H3.
    Qed.

    Lemma Om1_notcyclic: 
      ~ (exists s, O.+ (s,s)) -> ~ (exists s, O^-1.+ (s,s)).
    Proof.
      move => HOnc [s Hoc];rewrite -TclosIv in Hoc. 
      by have ?: (exists s : T, O.+ (s, s)) by (exists s).
    Qed.
    
    Lemma A2_from_Asp (Asp: sporder O): ~ (iic (Asym R)).
      by move: Rasym => /AsymEq ->;apply: Rnotiic.
    Qed.

    Lemma A2_from_Anc (Anc: ~ (exists s, O.+ (s,s))) : ~ (iic (Asym R)).
    Proof.
      have notiicO:  ~ (iic O) by move => /(@cyclic T O)/Anc.
      move: Rasym => /(AsymEq R) => -> HiicR.
      by have: (iic O) by apply: (iic_sub Au').
    Qed.
    
    Lemma haveA6 : forall x y : T, B (x, y) /\ ~ M (y, x) -> O^-1 (x, y).
    Proof. by move => x y [[_ H1] _]. Qed.

    Lemma A7_from_Asp_Atc (Asp: sporder O) (Atc: Three_cycles): Assumption7 R B M. 
    Proof.
      move: Asp => [_ Otr]. 
      move => x x' y y' _ Rxy' My'x' Bx'y nBxy [nRx'y nMyx'] [nRxy nMyx]
               nMxx' nMx'x _ _ _ _ _ nMy'x.
      move: My'x' => [[Dy'x' Ox'y'] | [_ Oy'x']].
      + move: Bx'y => [Dx'y Oyx'].
        have Oyy': O^-1 (y',y) by apply: (Otr y x' y' Oyx' Ox'y').
        move: Oyy' => /(@test'' T G D O Ad Ao) [By'y | [Dyy' _]].
        ++ by left.
        ++ (** * here we need the 3-cycle property *)
          rewrite (RB Ad Ao) in nMyx'.
          move: (@Atc y y' x' Dyy' Dy'x' Dx'y nMyx') => Dy'y.
          (** now we have Dyy' and Dy'y *)
          by rewrite (RB Ad Ao).
      + move: Rxy' => [_ Oxy'].
        have Oxx': O (x,x') by apply: (Otr x y' x' Oxy' Oy'x').
        move: Oxx' => /(@test'' T G D O Ad Ao) [Bx'x | Rxx'].
        ++ by have Hmx'x: M(x',x) by left.
        ++ by have Hmx'x: M(x,x') by right.
    Qed.

    Lemma A7_from_Afg_Atc (Afg: Forbiden_graph)(Atc: Three_cycles): Assumption7 R B M. 
    Proof.
      rewrite (RB Ad Ao).
      move => x x' y y' _ Rxy' Dy'x' Bx'y nBxy [nRx'y nDyx'] [nRxy nDyx]
               nDxx' nDx'x _ _ _ _ _ nDy'x.
      have nDxy: ~ (D (x,y))
        by rewrite -(RB Ad Ao) => /= -[Bxy| Rxy].
      have Dx'y: D(x',y) by move: Bx'y=> [? _].
      by move: (@Afg x y' x' y Rxy' Dy'x' Bx'y) =>
            [Dxy | [Dyx | [Dxx' | [ Dx'x | [ Dy'y |Dyy']]]]];
            [| | | | |move: (@Atc y y' x' Dyy' Dy'x' Dx'y nDyx')].
    Qed.

    Lemma A7_from_MLfg (MLfg: M_L_Forbiden_graph): Assumption7 R B M. 
    Proof.
      rewrite (RB Ad Ao).
      move => x x' y y' _ Rxy' Dy'x' Bx'y nBxy [nRx'y nDyx'] [nRxy nDyx]
               nDxx' nDx'x _ _ _ Hxney _ nDy'x.
      have nDxy: ~ (D (x,y))
        by rewrite -(RB Ad Ao) => /= -[Bxy| Rxy].
      have Dx'y: D(x',y) by move: Bx'y=> [? _].
      move: (@MLfg x y' x' y Rxy' Dy'x' Bx'y) => -[[_ Hd] | [Hyeqx _]].
      by move: Hd => [Dxy | [Dyx | [Dxx' | [ Dx'x | [ Dy'y | [[Dy'x _] | [Dyx' _]]]]]]].
      by [].
    Qed.
    
    Lemma A8_from_Atc (Atc: Three_cycles): Assumption8 R B M. 
    Proof.
      (* reformulate everything with D *)
      rewrite (RB Ad Ao).
      move => x' y y' _ _ _ [Dyy' _] Dy'x' [Dx'y _] [_ nDyx']. 
      by move: (@Atc y y' x' Dyy' Dy'x' Dx'y nDyx').
    Qed.

    Lemma A8_from_MLfg (MLfg: M_L_Forbiden_graph): Assumption8 R B M. 
    Proof.
      (* reformulate everything with D *)
      rewrite (RB Ad Ao).
      move => x' y y' _ _ _ Ryy' Dy'x' Bx'y [_ nDyx'].
      move: (@MLfg y y' x' y Ryy' Dy'x' Bx'y) => [[Hyney _] |[_ Hd]].
      by [].
      by move: Hd => [Dyx'|[[Dy'y _]|[Dyx']]].
    Qed.
    
    (** A stronger Champetier theorem as we use a weaker
        version of the three cycles assymption *)
    Lemma Kernel_Champetier (Asp: sporder O) (Atc: Three_cycles): 
      exists S, RelIndep M S /\ absorbant M S.
    Proof.
      by pose proof 
           (@G_SSW_fin_porder T O^-1 R B 
              (A2_from_Asp Asp) haveA6 (A7_from_Asp_Atc Asp Atc) 
              (A8_from_Atc Atc) A1 (sporder_inv Asp) Au' Apk).
    Qed.

    (** A stronger Blidia Hengel theorem as we use a weaker
        version of the three cycles assymption *)
    Lemma Blidia_Hengel_Theorem
      (Anc: ~ (exists s, O.+ (s,s))) (Afg: Forbiden_graph) (Atc: Three_cycles):
      exists S, kernel M S. 
    Proof.
      by apply: (@G_SSW_fin_notcyclic T O^-1 R B 
                   (A2_from_Anc Anc) haveA6 
                   (A7_from_Afg_Atc Afg Atc)
                   (A8_from_Atc Atc) A1 Au' Apk
                   (Om1_notcyclic Anc)).
    Qed.

    Lemma Meunier_Langlois_P2_5
      (Anc: ~ (exists s, O.+ (s,s))) (MLfg: M_L_Forbiden_graph) : exists S, kernel M S. 
    Proof.
      by apply: (@G_SSW_fin_notcyclic T O^-1 R B 
                   (A2_from_Anc Anc) haveA6 
                   (A7_from_MLfg MLfg)
                   (A8_from_MLfg MLfg) A1 Au' Apk
                   (Om1_notcyclic Anc)).
    Qed.
    
  End Finite_case_Kernel_Theorems.
End Finite_case_Kernel_Theorems.
