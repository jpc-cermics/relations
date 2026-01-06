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
    decode_aux row col p with sumbool_of_bool  ((p row) < col) => {
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
  
  (* we obtain the recursive equality we wanted *)
  Lemma decode_auxP0 (row col: nat) (p : nat -> nat): 
    decode_aux row col p = 
      if (p row) < col then  decode_aux row.+1 (col - (p row).+1) p 
      else (row,col).
  Proof.
    (** other possibility: by funelim (decode_aux row col p);rewrite H0. *)
    by rewrite decode_aux_equation_1 
         /decode_aux_unfold_clause_1;case H1: ((p row) < col);rewrite /= . 
  Qed.

  Fixpoint prefix_sum (p: nat -> nat) (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n' => prefix_sum p n' + (p n').+1
    end.
  
  Lemma prefix_sumP (p: nat -> nat) n: (prefix_sum p n.+1) = (prefix_sum p n) + (p n).+1.
  Proof. by []. Qed.

  Lemma prefix_sum_strict_inc (p: nat -> nat): forall n, prefix_sum p n < prefix_sum p n.+1.
  Proof. move => n;rewrite /= ;by lia. Qed.
  
  Lemma prefix_sum_inc (p: nat -> nat) i j : i <= j -> prefix_sum p i <= prefix_sum p j.
  Proof. 
    elim: j i => [i | n Hn i H1];first by rewrite leqn0 => /eqP ->.
    case H2: (i == n.+1). 
    + by move: H2 => /eqP ->.
    + move: H1. rewrite leq_eqVlt H2 orFb => /Hn H3.
      by apply: ltnW;apply: (leq_ltn_trans H3 (prefix_sum_strict_inc p n)). 
  Qed.

  Lemma prefix_sumP1 (p: nat -> nat) n j: 
    j <= n ->  prefix_sum p j + p j <= prefix_sum p n + p n.
  Proof.
    elim: n j => [j |n Hn j H1]; first by rewrite leqn0 => /eqP ->.
    have H2:  j.+1 <= n.+2. by lia.
    by move: (prefix_sum_inc p H2); rewrite 2!prefix_sumP; lia. 
  Qed.

  Lemma prefix_sumP2 (p: nat -> nat) n: 
    prefix_sum p n + p n <  prefix_sum p n.+1 + p n.+1.
  Proof. rewrite prefix_sumP. lia. Qed.
  
  Lemma decode_auxP1 (p: nat -> nat) j col: 
    decode_aux j (col - prefix_sum p j) p
    = if p j < col - prefix_sum p j then 
      decode_aux j.+1 (col - (prefix_sum p j.+1)) p 
    else (j, col - prefix_sum p j).
  Proof.
    elim: j col => [col | j _ col];first by rewrite prefix_sumP /= subn0;apply: decode_auxP0.
    rewrite decode_auxP0. 
    have ->: col - prefix_sum p j.+2 = col - prefix_sum p j.+1 - (p j.+1).+1
      by  rewrite [in LHS]prefix_sumP;lia.
    exact.
  Qed.
  
  Lemma decode_auxP2 (p: nat -> nat) n col: 
    prefix_sum p n + p n < col -> 
    forall j, j < n -> decode_aux j (col - prefix_sum p j) p = 
                   decode_aux j.+1 (col - prefix_sum p j.+1) p.
    move => H1 j H2.
    have H3: prefix_sum p j + p j < col.
    by apply/(leq_ltn_trans _ H1)/prefix_sumP1/ltnW.
    by rewrite decode_auxP1;have ->: p j < col - prefix_sum p j by lia.
  Qed.

  Definition P (p: nat -> nat) n j col := 
    decode_aux j (col - prefix_sum p j) p = decode_aux n (col - prefix_sum p n) p.
  
  Lemma decode_auxP3 (p: nat -> nat) n col j:
    prefix_sum p n + p n < col -> j < n -> P p n j.+1 col -> P p n j col.
  Proof. by rewrite /P;move => H1 H2 <-;apply: (decode_auxP2 H1). Qed.
  
  Lemma decode_auxP4 (p: nat -> nat) n col: P p n n col.
  Proof. by []. Qed.
  
  Lemma decode_auxP5 (p: nat -> nat) n col:
    prefix_sum p n + p n < col -> ~ (P p n 0 col) -> forall j, j <= n -> ~(P p n j col).
  Proof.
    move => H1 H2.
    elim => [// | j Hr H3 /(@decode_auxP3 p n col j H1 H3)H4].
    by have H5: ~ P p n j col by apply: Hr;lia.
  Qed.
  
  Lemma decode_auxP6 (p: nat -> nat) n col:
    prefix_sum p n + p n < col -> ~ (P p n 0 col) -> False. 
  Proof.  move => H1 H2; move: (decode_auxP5 H1 H2) => /(_ n) H3.
          by (have /H3 H4: n <= n by lia);have H5: P p n n col by [].
  Qed.
  
  Lemma decode_auxP7 (p: nat -> nat) n col:
    prefix_sum p n + p n < col -> (P p n 0 col). 
  Proof.
    by move => H1;move: (decode_auxP6 H1) => H2;apply: contrapT => /H2 ?.
  Qed.

  Lemma decode_auxP8 (p: nat -> nat) n col:
    prefix_sum p n + p n < col ->
    decode_aux 0 col p = decode_aux n (col - prefix_sum p n) p.
  Proof. by move => H1;move: (decode_auxP7 H1);rewrite /P /= subn0. Qed.
  
  Lemma decode_auxP9 (p: nat -> nat) n col:
    prefix_sum p n + p n < col -> col <= (prefix_sum p n.+1) + (p n.+1) 
    -> decode_aux 0 col p = (n.+1, col - (prefix_sum p n.+1)).
  Proof. 
    rewrite prefix_sumP; move => H1 H2;move: (decode_auxP8 H1) => ->.
    rewrite  decode_auxP0.
    have ->: p n < col - prefix_sum p n by lia.
    rewrite  decode_auxP0.
    have ->: ( p n.+1 < col - prefix_sum p n - (p n).+1 )= false by lia.
    have ->: col - prefix_sum p n - (p n).+1 = col - (prefix_sum p n + (p n).+1) by lia.
    exact.
  Qed.
  
  Definition decode' (p : nat -> nat) (n : nat): nat * nat := decode_aux 0 n p.
  
  Definition encode' (p : nat -> nat) (rc : nat * nat) : nat := (prefix_sum p rc.1 + rc.2).
  
  Section exists_sandwich.
    
    Definition x (p : nat -> nat) (n : nat) := prefix_sum p n + p n.
  
    Lemma x_incr (p : nat -> nat) (n : nat): x p n < x p n.+1.
    Proof. rewrite /x prefix_sumP. lia. Qed.

    Lemma x_gt_id (p : nat -> nat) n : x p n >= n + x p 0.
    Proof. by elim: n => [|n Hr];[rewrite add0n | move: x_incr => /(_ p n) H1;lia].
    Qed.
    
    Theorem exists_sandwich (p : nat -> nat) n :
      x p 0 < n -> exists j, (x p j < n) && (n <= x p j.+1).
    Proof.
      move=> H1.
      have hex: exists k, n <= x p k
          by (exists n);pose proof (x_gt_id p n) as H2;(have H3: n <= n + x p 0 by lia);
                     apply: (leq_trans H3 H2).
      pose  k0 := ex_minn hex.
      have H2: ~(0 = k0)
        by rewrite /k0; case: ex_minnP  => k H3 H4;move => H5;rewrite -H5 in H3;lia.
      have H3: 0 < k0 by lia.
      exists k0.-1.
      have ->: k0.-1.+1 = k0 by lia.
      move: H3. rewrite /k0. case: ex_minnP => // k -> H5 H6.
      rewrite andbT. 
      have H7: n <= x p k.-1 -> False by move => /H5 H7; lia.
      by lia.
    Qed.
    
  End exists_sandwich.
  

  Definition p n := 
      match n with 
      | 0 => 3
      | 1 => 2
      | 2 => 0
      | _ => 1
      end.
  
  Compute (decode' p 0).
  Compute (decode' p 1).
  Compute (decode' p 2).
  Compute (decode' p 3).
  Compute (decode' p 4).
  Compute (decode' p 5).
  Compute (decode' p 6).
  Compute (decode' p 7).
  Compute (decode' p 8).
  Compute (decode' p 9).
  Compute (decode' p 10).
  Compute (decode' p 11).

  Compute (encode' p (decode'  p 0)) == 0.
  Compute (encode' p (decode'  p 1)) == 1.
  Compute (encode' p (decode'  p 2)) == 2.
  Compute (encode' p (decode'  p 3)) == 3.
  Compute (encode' p (decode'  p 4)) == 4.
  Compute (encode' p (decode'  p 5)) == 5.
  Compute (encode' p (decode'  p 6)) == 6.
  Compute (encode' p (decode'  p 7)) == 7.
  Compute (encode' p (decode'  p 8)) == 8.
  Compute (encode' p (decode'  p 9)) == 9.
  Compute (encode' p (decode'  p 10)) == 10.
  Compute (encode' p (decode'  p 11)) == 11.
  
  Definition decode (g : nat -> seq T) (i : nat) : nat * nat := decode' (fun n' => (size (g n'))) i.

  Definition encode (g : nat -> seq T) (rc : nat * nat) : nat := encode' (fun n' => (size (g n'))) rc.
  
  Definition val (f: nat -> T) (g : nat -> seq T) n := 
    let (row,col):= decode g n in 
    if col == 0 then (f row) else nth (f row) (g row) col.-1.
  
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
    
    Compute (encode g (decode g 0)) == 0.
    Compute (encode g (decode g 1)) == 1.
    Compute (encode g (decode g 2)) == 2.
    Compute (encode g (decode g 3)) == 3.
    Compute (encode g (decode g 4)) == 4.
    Compute (encode g (decode g 5)) == 5.
       
  End demo.

End walk.

  
Section Test.

  Definition strict_inc (f : nat -> nat) := forall n, f n < f n.+1.

  Definition unbounded (f : nat -> nat) := forall n, exists p, n <= f p.

  Lemma strict_inc_unbounded  (f : nat -> nat): strict_inc f -> unbounded f.
  Proof. by move=> H1 n;exists n;elim: n => [// |n Hn];apply: (leq_ltn_trans Hn (H1 n)).
  Qed.



End Test.
