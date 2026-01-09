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
  
  Variables (T:choiceType).

  Section prefix_sum. 

    Definition prefix_sum  (p: nat -> nat) (n : nat) : nat:=
      let fix loop m := if m is i.+1 then (loop i) + (p i).+1 else 0 in loop n.
    
    Lemma prefix_sumP (p: nat -> nat) n: (prefix_sum p n.+1) = (prefix_sum p n) + (p n).+1.
    Proof. by []. Qed.

    Lemma prefix_sum_strict_inc (p: nat -> nat): forall n, prefix_sum p n < prefix_sum p n.+1.
    Proof. move => n;rewrite /= ;by lia. Qed.

    Lemma prefix_sum_gt_id (p : nat -> nat) n : prefix_sum p n >= n.
    Proof. elim: n => [// |n Hr];apply: (leq_ltn_trans Hr (prefix_sum_strict_inc p n)). Qed.
    
    Lemma prefix_sum_inc (p: nat -> nat) i j : i < j -> prefix_sum p i < prefix_sum p j.
    Proof. 
      elim: j i => [i // | n Hn i H1]. 
      case H2: (i == n);first by move: H2 => /eqP ->;apply: prefix_sum_strict_inc.
      move: H1;rewrite leq_eqVlt => /orP [H3 | H3];first by lia.
      have /Hn H4: i < n by lia.
      have H5:  prefix_sum p i <= prefix_sum p n by lia. 
      by rewrite prefix_sumP;apply: (leq_ltn_trans H5 _);lia.
    Qed.
    
    Theorem exists_sandwich (p : nat -> nat) n :
      exists j, ((prefix_sum p j) <= n) && (n < prefix_sum p j.+1).
    Proof.
      case H1: (n <= p 0);
        first by move: H1;rewrite /prefix_sum => H1;exists 0;rewrite /prefix_sum add0n;lia.
      move: H1;rewrite leqNgt => /negP/negP H1.
      have hex: exists k, n < prefix_sum p k
          by  (exists n.+1);apply: (leq_ltn_trans (prefix_sum_gt_id p n) (prefix_sum_strict_inc p n)).
      pose  k0 := ex_minn hex.
      have H2: ~(0 = k0) by rewrite /k0;case: ex_minnP  => k H3 ?;move => H5;rewrite -H5 in H3.
      have H3: 0 < k0 by lia.
      exists k0.-1.
      have ->: k0.-1.+1 = k0 by lia.
      move: H3. rewrite /k0. case: ex_minnP => // k -> H5 H6.
      rewrite andbT. 
      have H7: n < prefix_sum p k.-1 -> False  by move => /H5 H7; lia.
      by lia.
    Qed.
    
    Lemma gamma (p : nat -> nat): exists (gamma : nat -> nat), 
      forall n, ((prefix_sum p (gamma n)) <= n) && (n < prefix_sum p (gamma n).+1).
    Proof.
      pose R:= [set ij | ((prefix_sum p ij.2) <= ij.1) && (ij.1 < prefix_sum p (ij.2).+1)].
      have Tr: total_rel R by move => n;move: (exists_sandwich p n) => [j H1];exists j.
      by pose proof (choice'  Tr) as [gamma H1];exists gamma.
    Qed.
    
    Definition decode1 (p : nat -> nat) (gamma:  nat -> nat) n := 
      ((gamma n), n - (prefix_sum p (gamma n))).
    
    Definition encode1 (p : nat -> nat) (rc : nat * nat) : nat := (prefix_sum p rc.1 + rc.2).

    Lemma encode_decode (p : nat -> nat): 
      exists (gamma : nat -> nat), forall n, encode1 p (decode1 p gamma n) = n.
    Proof.
      pose proof (gamma p) as [gamma H1].
      by exists gamma;move => n;move: H1 => /(_ n) /andP [H1 H2];rewrite  /decode1 /encode1 /=;lia.
    Qed.

  End prefix_sum.
  
  Section encode_decode. 

    Equations? decode_aux (row col: nat) (p : nat -> nat) : nat* nat  by wf col lt :=
      decode_aux row col p with sumbool_of_bool (col <= (p row)) => {
        | left  H0 => (row, col) ;
        | right H0 => decode_aux row.+1 (col - (p row).+1) p; 
        }.
    Proof. by lia. Qed.
    
    (* we obtain the recursive equality we wanted *)
    Lemma decode_auxP0 (row col: nat) (p : nat -> nat): 
      decode_aux row col p = 
        if col <= (p row) then (row,col)
        else decode_aux row.+1 (col - (p row).+1) p.
    Proof. by funelim (decode_aux row col p);rewrite H0. Qed.
    
    Lemma decode_auxP1 (p: nat -> nat) j col: 
      decode_aux j (col - prefix_sum p j) p
      = if (col - prefix_sum p j) <= (p j) then (j, col - prefix_sum p j)
        else decode_aux j.+1 (col - (prefix_sum p j.+1)) p.
    Proof.
      elim: j col => [col | j _ col];
                    first by rewrite prefix_sumP /= subn0 add0n;apply: decode_auxP0.
      rewrite decode_auxP0. 
      have ->: col - prefix_sum p j.+2 = col - prefix_sum p j.+1 - (p j.+1).+1
        by  rewrite [in LHS]prefix_sumP;lia.
      exact.
    Qed.
    
    Lemma decode_auxP2 (p: nat -> nat) n col: 
      prefix_sum p n.+1 <= col -> 
      forall j, j < n -> decode_aux j (col - prefix_sum p j) p = 
                     decode_aux j.+1 (col - prefix_sum p j.+1) p.
    Proof.
      move => H1 j H2.
      have H3:  j.+1 < n.+1 by lia.
      have H4: prefix_sum p j.+1 < col 
        by pose proof (@prefix_sum_inc p j.+1 n.+1 H3);lia.
      rewrite prefix_sumP in H4.
      have H5: (col - prefix_sum p j) <= (p j) = false by lia.
      by rewrite decode_auxP1 H5.
    Qed.
    
    Definition P (p: nat -> nat) n j col := 
      decode_aux j (col - prefix_sum p j) p = decode_aux n (col - prefix_sum p n) p.
    
    Lemma decode_auxP3 (p: nat -> nat) n col j:
      prefix_sum p n.+1 <= col -> j < n -> P p n j.+1 col -> P p n j col.
    Proof. by rewrite /P;move => H1 H2 <-;apply: (decode_auxP2 H1). Qed.
    
    Lemma decode_auxP4 (p: nat -> nat) n col: P p n n col.
    Proof. by []. Qed.
    
    Lemma decode_auxP5 (p: nat -> nat) n col:
      prefix_sum p n.+1 <= col -> ~ (P p n 0 col) -> forall j, j <= n -> ~(P p n j col).
    Proof.
      move => H1 H2.
      elim => [// | j Hr H3 /(@decode_auxP3 p n col j H1 H3)H4].
      by have H5: ~ P p n j col by apply: Hr;lia.
    Qed.
    
    Lemma decode_auxP6 (p: nat -> nat) n col:
      prefix_sum p n.+1 <= col -> ~ (P p n 0 col) -> False. 
    Proof.  move => H1 H2; move: (decode_auxP5 H1 H2) => /(_ n) H3.
            by (have /H3 H4: n <= n by lia);have H5: P p n n col by [].
    Qed.
    
    Lemma decode_auxP7 (p: nat -> nat) n col:
      prefix_sum p n.+1 <= col -> (P p n 0 col). 
    Proof.
      by move => H1;move: (decode_auxP6 H1) => H2;apply: contrapT => /H2 ?.
    Qed.

    Lemma decode_auxP8 (p: nat -> nat) n col:
      prefix_sum p n.+1 <= col -> 
      decode_aux 0 col p = decode_aux n (col - prefix_sum p n) p.
    Proof. by move => H1;move: (decode_auxP7 H1);rewrite /P /= subn0. Qed.
    
    Lemma decode_auxP9 (p: nat -> nat) n col:
      col < prefix_sum p n.+1 ->
      decode_aux n (col - prefix_sum p n) p = (n, col - (prefix_sum p n)).
    Proof. 
      move => H1. 
      rewrite decode_auxP1.
      have H2: col - prefix_sum p n <= p n by rewrite prefix_sumP in H1; lia.
      by rewrite H2.
    Qed.
    
    Lemma decode_auxP10 (p: nat -> nat) n col:
      prefix_sum p n.+1 <= col < prefix_sum p n.+2 -> 
      decode_aux 0 col p = (n.+1, col - (prefix_sum p n.+1)).
    Proof. 
      move => /andP [/[dup] H0 /decode_auxP8 -> /decode_auxP9 <-]. 
      rewrite decode_auxP1.
      by have -> : col - prefix_sum p n <= p n = false by rewrite prefix_sumP in H0; lia.
    Qed.

    Lemma decode_auxP11 (p: nat -> nat) n col:
      prefix_sum p n <= col < prefix_sum p n.+1 -> 
      decode_aux 0 col p = (n, col - (prefix_sum p n)).
    Proof. 
      case H1: (n== 0);first by move: H1 => /eqP -> /=;rewrite add0n subn0 ltnS decode_auxP0 => ->.
      move: H1 => /neq0_lt0n H1.
      have H2: n.-1.+1 = n by lia.
      by rewrite -H2 => /decode_auxP10 H3.
    Qed.
    
    Definition decode2 (p : nat -> nat) (n : nat): nat * nat := decode_aux 0 n p.
  
    Definition p n := 
      match n with 
      | 0 => 3
      | 1 => 2
      | 2 => 0
      | _ => 1
      end.
    
    (** we can preform computations with decode2 version *)
    
    Compute (decode2 p 0).
    Compute (decode2 p 1).
    Compute (decode2 p 2).
    Compute (decode2 p 3).
    Compute (decode2 p 4).
    Compute (decode2 p 5).
    Compute (decode2 p 6).
    Compute (decode2 p 7).
    Compute (decode2 p 8).
    Compute (decode2 p 9).
    Compute (decode2 p 10).
    Compute (decode2 p 11).
  
    Lemma decodeP (p : nat -> nat) col: exists gamma: nat ->nat,  (decode2 p col) = (decode1 p gamma col).
    Proof.
      pose proof (gamma p) as [gamma H1]; exists gamma;rewrite /decode2 /decode1.
      by move: H1 => /(_ col) => /(@decode_auxP11 p (gamma col) col) ->.
    Qed.
    
  End encode_decode. 
  
  Definition decode (g : nat -> seq T) (i : nat) : nat * nat := decode2 (fun n' => (size (g n'))) i.

  Definition encode (g : nat -> seq T) (rc : nat * nat) : nat := encode1 (fun n' => (size (g n'))) rc.
  
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
