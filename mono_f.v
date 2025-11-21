(* -*- Encoding : utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & datest)*)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Utilities *)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot seq order boolp classical_sets. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".

From RL Require Import seq1 rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

From Equations Require Import Equations.
From Coq  Require Import Sumbool.

Notation dec x := (sumbool_of_bool x).

Section walk.
  (** * How to encode in one function the two functions obtained above *)
  Variables (T:choiceType).
  
  Equations? decode_aux (row col: nat) (p : nat -> nat) : nat* nat  by wf col lt :=
    decode_aux row col p with dec  ((p row) < col) => {
      | left H0 => decode_aux (S row) (col - (p row).+1) p; 
      | right H0 => (row, col) ;
      }.
  Proof.
    have: 0 <= col - (p row).+1 by [].
    rewrite leq_subRL;last by rewrite H0.
    rewrite addn0 => H1.
    have H2: 1 <= col by apply: (leq_trans _ H1).
    by apply/ltP;rewrite ltn_subrL;apply/andP.
  Qed.

  Definition decode (g : nat -> seq T) (i : nat) : nat * nat :=
    decode_aux 0 i (fun n => size (g n)).

  Definition val (f: nat -> T) (g : nat -> seq T) n := 
    let (row,col):= decode g n in 
    match col with
    | 0 => f row
    | S col' => nth (f row) (g row) col'
    end.

  Fixpoint prefix_sum  (g: nat -> seq T) (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n' => (prefix_sum g n' + (size (g n')).+1)
    end.

  Definition encode (g : nat -> seq T) (row col : nat) : nat :=
    (prefix_sum g row + col)%N.
  
  Section demo.

    Variables (a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 :T).
    Definition L:= [:: a1; b1; c1; d1; e1; f1; g1; h1; i1; j1; k1; l1; m1].
    Definition g n := 
      match n with 
      | 0 => [:: b1 ; c1 ; d1]
      | 1 => [:: f1 ; g1]
      | 2 => [::]
      | _ => [:: j1]
      end.
    
    Definition f n := 
      match n with 
      | 0 => a1
      | 1 => e1
      | 2 => h1
      | 3 => i1
      |_  => k1
      end.
    
    Compute (decode g 0).
    Compute (decode g 1).
    Compute (decode g 2).
    Compute (decode g 3).
    Compute (decode g 4).
    Compute (decode g 5).
    Compute (decode g 6).
    Compute (decode g 7).
    
    (* should give a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 *)
    Compute ((val f g  0) =   (nth m1 L 0)).
    Compute ((val f g  1) =   (nth m1 L 1)).
    Compute ((val f g  2) =   (nth m1 L 2)).
    Compute ((val f g  3) =   (nth m1 L 3)).
    Compute ((val f g  4) =   (nth m1 L 4)).
    Compute ((val f g  5) =   (nth m1 L 5)).
    Compute ((val f g  6) =   (nth m1 L 6)).
    Compute ((val f g  7) =   (nth m1 L 7)).
    Compute ((val f g  8) =   (nth m1 L 8)).
    Compute ((val f g  9) =   (nth m1 L 9)).
    Compute ((val f g  10) =  (nth m1 L 10)).

    Compute (encode g (decode g 0).1 (decode g 0).2) == 0.
    Compute (encode g (decode g 1).1 (decode g 1).2) == 1.
    Compute (encode g (decode g 2).1 (decode g 2).2) == 2.
    Compute (encode g (decode g 3).1 (decode g 3).2) == 3.
    Compute (encode g (decode g 4).1 (decode g 4).2) == 4.
    Compute (encode g (decode g 5).1 (decode g 5).2) == 5.
    Compute (encode g (decode g 6).1 (decode g 6).2) == 6.
    Compute (encode g (decode g 7).1 (decode g 7).2) == 7.

  End demo.
  
  Lemma decode_aux_id (g : nat -> seq T) :
    forall (row col : nat),
      ((size (g row)).+1 <= col = false) -> 
      decode_aux row col (fun n => size (g n)) = (row, col).
  Proof.
    by move => row col H1;rewrite decode_aux_equation_1 /decode_aux_unfold_clause_1 H1 /=. 
  Qed.
  
  Lemma decodeP (g : nat -> seq T): 
    forall n, let d:= decode g n in ((size (g d.1)).+1 <= d.2 = false).
  Proof.
    elim;first by []. 
    move => n Hr.
    rewrite /decode decode_aux_equation_1 /decode_aux_unfold_clause_1 // .
    rewrite /decode decode_aux_equation_1 /decode_aux_unfold_clause_1 in Hr.
    case H2: (size (g 0) < n.+1); last by rewrite /=.
    rewrite /=.
    case H3: (size (g 0) == n).
    + move: H3 => /eqP H3.
      have H4: (n - n) = 0. by lia.
      by rewrite H3 subSS H4 //.
    + rewrite subSS.
      have H4: size (g 0) < n. by lia.
      rewrite H4 /= in Hr.
      rewrite /decode decode_aux_equation_1 /decode_aux_unfold_clause_1.
  Admitted.
  

End walk.

  
