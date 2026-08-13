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

From RL Require Import  seq1 seq2 rel paper_kernels_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Module G_SSW. 
  (** * Generalized SSW Theorem *)
  Section G_SSW.
    (** * Existence of a Maximal in the infinite case with Zorn Lemma *)
    (** * we need [<= O] to be a porder *)

    Context {T:choiceType} (R B O: relation T).

    Notation M := (B `|` R).
    
    Context (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O)
      (A4: Assumption4 O) (A5: Assumption5 O M) (A6: Assumption6 B M O)
      (A7: Assumption7 R B M) (A8: Assumption8 R B M) (A9: Assumption9 R B O M).
        
    (* begin snippet MainTh:: no-out *)    
    Theorem G_SSW: exists S, RelIndep M S /\  absorbant M S.
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
  End G_SSW.
End G_SSW.

Export G_SSW(G_SSW).

Module SSWext.
  (** * Extended SSW Theorem *)
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
  (* end snippet MainTh:: no-out *)    
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 A3 L4 L5 L6 L7 L8 L9).
  Qed.
  
End SSWext.

Module ABkernels.
  (** * The case of AB kernels  *)
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

  Theorem SSWext
    (A1: AB_1) (A2: AB_2) (A3: AB_3) (A4: AB_4) (A5: AB_5):
    exists X, RelIndep M X /\ absorbant M X.
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 A3 (L4 A5) L5 L6 (L7 A4 A5)
                     (L8 A4 A5) (L9 A4 A5)).
  Qed.
  
End ABkernels.


Module MeunierLanglois. 
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
  
  Theorem MLinf
    (A1: AB_1) (A2: AB_2) (A3: AB_3) (A4: AB_4) (A5: AB_5) (A6: AB_6):
    exists X, RelIndep M X /\ absorbant M X.
  (* end snippet MainTh:: no-out *)    
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 (L3 A3) (L4 A5 A6) 
                  L5 L6 (L7 A4 A5) (L8 A4 A5) (L9 A4 A5)).
  Qed.
  
End MeunierLanglois. 

Module BlidiaEngel.
  (** * This is a version of Blidia and Engel for infinite graph *)
  (* O is an orientation:  Asym, irreflexive relation *)
  (* D irreflexive D est inclue dans O `|` O^-1 *)
  (* O is acycliq *)
  Section test.
  
  Parameter (T:choiceType) (O D: relation T).
  
  Definition R := D `&` O^-1. 
  Definition B := D `&` O. 
  
  Notation M := (B `|` R).

  Context (OD: O `|` O^-1 = M `|` M^-1).
  
  Definition AB_1:= (nonempty [set: T]).
  Definition AB_2:= ~ (iic R).
  Definition AB_3:= ~ (iic B).
  
  Definition AB_4:=  forall x y z t, 
      ~ (y = x) -> ~ (y = z) -> ~ (z = x) -> ~ (z = t)
      -> ~ (z = y) ->  ~ (y = t) -> ~ (x = t)
      -> O (x,y) -> (O (y,z) \/ O (z,y)) -> O (t,z) 
      -> O (x,z) \/ O (z,x) \/ O (y,t) \/ O (t,y) \/ O (x,t) \/ O (t,x).
  
  Definition AB_5:=  forall x y z, 
      ~ (x = y) -> ~ (z = y) -> ~ (z = x)       
      -> O (x,y) -> O (y,z) -> O (z,x)
      -> (O (y,x) /\ O (z,y)).

  (* O and D are both directions of a same graph *)

  Lemma haveA5: ( O  `<=` M `|` M^-1).
  Proof. by rewrite -OD;apply: subsetUl. Qed.
  
  Lemma haveA6: forall x y, B (x,y) /\ ~ (M (y, x)) -> O (x,y).
  Proof. by move => x y [[_ Hb] _]. Qed.
  
  Theorem BE 
    (A1: Assumption1 T) (A2: Assumption2 R) (A3: Assumption3 O) (A4: Assumption4 O)
    (A7: Assumption7 R B M) (A8: Assumption8 R B M)
    (A9: Assumption9 R B O M):
    exists X, RelIndep M X /\ absorbant M X.
  Proof.
    by pose proof (@G_SSW _ R B O A1 A2 A3 A4 haveA5 haveA6 A7 A8 A9).
  Qed.
  
  End test.
  
End BlidiaEngel.


Module BHExt.
  Section BHExt.
    (** * Extended Blida en Hengel Theorem *)
  
    Context {T: finType} (O R B: relation T).

    Definition M := B `|` R.

    Context (A2: Assumption2 R) (A6: Assumption6 B M O)
      (A7: Assumption7 R B M) (A8: Assumption8 R B M). 
    Context (A1: nonempty [set: T]) (Au: R `<=` O^-1).
    Context (Apk : forall X , RelIndep O X <-> RelIndep M X).
    Context (A_Onotcyclic: ~ (exists s, O.+ (s,s))).
    
    (* There exists a kernel or an increasing mapping for [<< O] taking values in preKernels *)
    Lemma kernel_or_iic_fun:
      (exists h, (iic_fun ([<< O]%O) h) /\ (forall n, (h n) \in  (preKernel M R M)))
      \/ (exists S, (S \in (preKernel M R M)) /\ S \in (absorbant M)).
    Proof.
      (* using extend lemma *)
      have Ch0 S: S \in ((preKernel M R M) `&` (absorbant M).^c)
                 -> exists S', S' \in (preKernel M R M) /\ (S [<< O] S').
      {
        rewrite inE => -[Hpk Hna].
        move: (@extend T R B O S A2 A6 A7 A8 Hpk Hna) 
            => [S' [/mem_set Hpk' Hlt]].
        by exists S'. 
      }
      have Ch1 : exists S, S \in (preKernel M R M).
      {
        have Oinv_notcyclic: ~ (exists s, O^-1.+ (s,s))
          by rewrite -TclosIv.
        (* exists a sink and thus a preabsorbant node *)
        move: (@NotCyclic_exists_preabsorbant T O^-1 M A1 Oinv_notcyclic) => [v Hpa].
        (* [set v] is in (preKernel M R M). *)
        exists [set v]%classic;rewrite inE. 
        have Hinc:  (v)_:#R  `<=` (v)_:#O^-1 
          by rewrite /Aset;apply: Fset_inc;apply: inverseS.
        split;first by apply: RelIndep_set1.
        split;first by apply: (subset_trans Hinc _).
        + apply/negP => /eqP H.
          have Hv: [set v]%classic v by [].
          by rewrite H /= in Hv.
      }
      move: (@choose_sub _ ([<< O]%O) (preKernel M R M) (absorbant M).^c Ch0 Ch1)
          => [Hiic | [S [Hpk Hna]]].
      by left.
      by right;exists S;split;[| move: Hna;rewrite 2!inE /= => /contrapT].
    Qed.
    
    (* we prove that the existence of an increasing mapping for [<< O]
       taking values in preKernels would contradict acyclicity
     *)
    
    Lemma iic_to_allL  (h : nat -> (set T)):  
      (iic_fun ([<< O]%O) h) -> (forall n, (h n) \in  (preKernel O R M)) ->
      exists n p, h n = h (n+p+1)
             /\ allL ([<< O]%O) (mkseq (fun i => h (n + i+1)) p) (h n) (h n)
             /\ ((h n)::(mkseq (fun i => h (n + i+1)) p)) [\in] (preKernel O R M).
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
      (iic_fun ([<< O]%O) h) -> (forall n, (h n) \in  (preKernel O R M))
      -> exists s, O.+ (s,s).
    Proof.
      move => Hiic Hpk';move: (iic_to_allL Hiic Hpk') => [n [p [Ha [HallL Hpk]]]].
      by apply: (Cyclicity_BH_lemma HallL Hpk).
    Qed.
    
    Lemma exists_kernel: exists S, S \in (preKernel M R M) /\ S \in (absorbant M).
    Proof.
      have preKernelP S': preKernel O R M S' <-> preKernel M R M S'
        by rewrite /preKernel /= Apk.
      move: kernel_or_iic_fun => [[h [Hiic Hk]] | H1];last by [].
      have HpkO: (forall n, (h n) \in  (preKernel O R M))
        by move => n; rewrite inE preKernelP -inE.
      by move: (iic_and_prekernels_to_cyclic Hiic HpkO) => HOcyclic.
    Qed.
    
  End BHExt.
End BHExt.

Export BHExt(exists_kernel).


Section Extended_Champetier_Theorem.
    
  Context (T : finType) (O R B: relation T).
  Implicit Types (O R B: relation T). 
  
  Notation M := (B `|` R).

  Context (A2 : Assumption2 R) (A6 : Assumption6 B M O) 
    (A7 : Assumption7 R B M) (A8 : Assumption8 R B M).
  Context (A1: nonempty [set: T]) (Asp: sporder O) (Au: R `<=` O^-1).
  Context (Apk : forall X, RelIndep O X <->  RelIndep M X).
  
  Lemma maximal_mabsorbant S:
    (preKernel O R M S) /\ (forall U, preKernel O R M U -> S [<= O] U -> S = U)
    -> absorbant M S.
  Proof.
    contra; move => H1;rewrite /preKernel /= Apk => Hpk.
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
  
  Lemma Kernel_ChampetierExt: 
    exists S, RelIndep M S /\ absorbant M S.
  Proof.
    (* There exist a maximal set *)
    move: (@Maximal T O R M A1 Asp Au) => [S Hm].
    move: Hm => /[dup] /maximal_mabsorbant Ma [[/Apk Hpk _] _]. 
    by (exists S).
  Qed.
  
End Extended_Champetier_Theorem.

Section Blidia_Engel_Ext_Theorem.
  (** * Similar to Champetier but  (Asp: sporder O) *)
  (** * is replaced by Acyclicity *)

  Context (T : finType) (O R B: relation T).
  Implicit Types (O R B: relation T).

  Notation M := (B `|` R).  

  Context (A2 : Assumption2 R) (A6 : Assumption6 B M O) 
    (A7 : Assumption7 R B M) (A8 : Assumption8 R B M).
  Context (A1: nonempty [set: T]) (Au: R `<=` O^-1).
  Context (Apk : forall (X:set T) , RelIndep O X <->  RelIndep M X).
  Context (Anc : ~ ( exists s, R.+ (s,s))).
  
End Blidia_Engel_Ext_Theorem.

Section simpleGraph. 
  (** * simpleGraph definition *)
  Context (T : Type).
  Implicit Types (G D O Re: relation T).

  Definition simpleGraph G := symmetric G /\ irreflexive G.
  Definition Direction G D := D `|` D^-1 = G. 
  Definition Orientation G O := Direction G O /\ asymmetric O.

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

  Lemma orientation_relIndep G D S: 
    Orientation G D -> (RelIndep D S <-> RelIndep G S).
  Proof. by move => [Hd _];rewrite RelIndep_sym Hd. Qed.
  
End simpleGraph.

Section Champetier_Theeorem.
  (** * The original Champetier Theorem *)
  Context (T : finType) (G D O: relation T).
  
  Context (Asg: simpleGraph G).
  Context (Ao: Orientation G O).
  Context (Ad: Direction G D).

  Definition R := D `&` O^-1.
  Definition B := D `&` O.

  Notation M := (B `|` R).

  Context 
    (A1: nonempty [set: T]) 
    (Asp: sporder O)
    (A6 : Assumption6 B M O) 
    (A7 : Assumption7 R B M)
    (A8 : Assumption8 R B M).
  
  Lemma RB: M = D.
  Proof.
    have H1:  R `<=` D. by rewrite /R;apply: subIsetl.
    have H2:  B `<=` D. by rewrite /R;apply: subIsetl.
    rewrite predeqE => -[x y].
    split => [[/H2 H0 | /H1 H0] // | H3].
    case H4: ((x,y) \in O).
    + move: H4 => /set_mem H4.
      ++ case H5: ((y,x) \in O).
         move: H5 => /set_mem H5.
         by right;split.
         by left;split.
    + case H5: ((y,x) \in O).
      move: H5 => /set_mem H5.
      by right;split.
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
  
  Lemma AspIv: sporder O^-1.
  Proof. by apply: sporder_inv. Qed.
  
  Lemma Au:  R `<=` O^-1. 
  Proof. by rewrite /R;apply: subIsetr. Qed.

  Lemma Onoticc: ~ (iic  O^-1). 
  Proof. by apply: (@fin_not_iic _ O^-1 AspIv). Qed.
  
  Lemma Rnotiic: ~ (iic R).
  Proof. by move: Onoticc => ? /(@iic_sub T R O^-1 (Au)) ?. Qed.

  Lemma Apk:  forall X , RelIndep O X <->  RelIndep M X.
  Proof.
    move => X. rewrite RB. 
    rewrite (@direction_relIndep T G D X Ad).
    by rewrite (@orientation_relIndep T G O X Ao).
  Qed.
  
  Lemma Rsym : asymmetric R.
  Proof.
    move => x y /Au H1 /Au H2.
    by move: H1 Ao => + [_ /(_ x y) Ha] => /Ha H3.
  Qed.
  
  Lemma haveA2 : ~ (iic (Asym R)).
    move: Rsym => /AsymEq ->;apply: Rnotiic.
  Qed.

  Lemma haveA6 : forall x y : T, B (x, y) /\ ~ M (y, x) -> O (x, y).
  Proof. by move => x y [[_ H1] _]. Qed.

  Lemma Kernel_Champetier: 
    exists S, RelIndep M S /\ absorbant M S.
  Proof.
    by pose proof (@Kernel_ChampetierExt T O R B (haveA2) (haveA6)
                     A7 A8 A1 Asp (Au) (Apk)).
  Qed.
  
End Champetier_Theeorem.


