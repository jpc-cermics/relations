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
From RL Require Import  seq1 seq2 rel.
From RL Require Import paper_meunier_common.

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
