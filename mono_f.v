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
Require Import Arith. 

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
  
  (* we obtain the recursive equality we wanted *)
  Lemma decode_auxP0 (row col: nat) (p : nat -> nat): 
    decode_aux row col p = 
      if (p row) < col then  decode_aux row.+1 (col - (p row).+1) p 
      else (row,col).
  Proof.
    (** other possibility: by funelim (decode_aux row col p);rewrite H0. *)
    by rewrite decode_aux_equation_1 /decode_aux_unfold_clause_1;case H1: ((p row) < col);rewrite /= . 
  Qed.

  Fixpoint prefix_sum (p: nat -> nat) (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n' => prefix_sum p n' + (p n').+1
    end.
  
  Lemma prefix_sumP (p: nat -> nat) n: (prefix_sum p n.+1) = (prefix_sum p n) + (p n).+1.
  Proof. by []. Qed.

  Lemma prefix_sum_strict_inc (p: nat -> nat): forall n, prefix_sum p n < prefix_sum p n.+1.
  Proof. move => n;rewrite prefix_sumP;by lia. Qed.

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
  
  Lemma decode_auxP1 (p: nat -> nat) n col: 
    decode_aux n (col - prefix_sum p n) p
    = if p n < col - prefix_sum p n then 
      decode_aux n.+1 (col - (prefix_sum p n.+1)) p 
    else (n, col - prefix_sum p n).
  Proof.
    elim: n col => [col | n _ col];first by rewrite prefix_sumP /= subn0;apply: decode_auxP0.
    rewrite decode_auxP0. 
    have ->: col - prefix_sum p n.+2 = col - prefix_sum p n.+1 - (p n.+1).+1
      by  rewrite [in LHS]prefix_sumP;lia.
    exact.
  Qed.

  Lemma decode_auxP2 (p: nat -> nat) n col: 
    prefix_sum p n + p n < col -> 
    forall j, j < n -> decode_aux j (col - prefix_sum p j) p = 
                   decode_aux j.+1 (col - prefix_sum p j.+1) p.
    move => H1 j H2.
    have H3: prefix_sum p j + p j < col.
    apply: (leq_ltn_trans _ H1).
    apply: prefix_sumP1.
    by apply: ltnW.
    rewrite decode_auxP1.
    by have ->: p j < col - prefix_sum p j by lia.
  Qed.

  Lemma decode_auxP3 (p: nat -> nat) n col j:
    prefix_sum p n + p n < col -> 
    j < n -> 
    decode_aux j.+1 (col - prefix_sum p j.+1) p = decode_aux n (col - prefix_sum p n) p
    -> decode_aux j (col - prefix_sum p j) p = decode_aux n (col - prefix_sum p n) p.
  Proof. by move => H1 H2 <-; apply: (decode_auxP2 H1). Qed.

  Definition P (p: nat -> nat) n j col := 
    decode_aux j (col - prefix_sum p j) p = decode_aux n (col - prefix_sum p n) p.
  
  Fixpoint Q (p: nat -> nat) n j col := 
    match j with 
    | 0 => P p n n col 
    | j.+1 => if (j < n) then Q p n j col else (Q p n j col) /\ P p n (n - j.+1) col
    end. 

  Lemma Q_fact (p: nat -> nat) n j col: j < n -> Q p  n j col.
    elim: j => [ _ | j Hr H1];first by rewrite /Q/P.
    have -> : j < n by lia.
    by rewrite /= H2;apply: Hr.
    
  
                          
                            






  (*   Require Import Arith Wellfounded Lia. *)
  (* 
Definition Q (P: nat-> Prop) n := forall j, j  <= n -> P j.

Theorem downward_induction (P: nat-> Prop):
  forall n,
    (forall j, j < n -> P (S j) -> P j) ->
    P n ->
    forall j, j <= n -> P j.
Proof.
  move =>  n Hstep Hn.
  pose proof (well_founded_induction lt_wf).
  

  apply (well_founded_induction lt_wf).
  + intros j IH j'.
    case H1: (n < j). 
    ++ move: IH => /(_ n) IH.
       have H2:  forall j : nat, j <= n -> P j by apply: IH; lia.
       apply: H2.
    ++ have H2: j <= n by lia.
       rewrite leq_eqVlt => /orP [/eqP -> // | H3].
       case H4: (j' < j). 
       +++ move: IH => /(_ j') IH.
           have H5:  forall j : nat, j <= n -> P j by apply: IH; lia.
           apply: H5. by lia.
       +++ have H5: (j < n) by lia.
           apply: Hstep. by [].
           apply: IH.
           
       apply: IH. 
       
       move: IH => /(_ 0).
       
    destruct (Nat.eq_dec j n).
    ++ subst j. 
       rewrite leq_eqVlt => /orP [/eqP -> // | H4].
       move: IH => /(_ j') IH.
       have H5: forall j : nat, j <= n -> P j by apply: IH;lia.
       by apply: H5; apply: ltnW.
    ++  
      rewrite leq_eqVlt => /orP [/eqP ? // | H4].
      assert (j' < n) by lia.
    apply Hstep.
    + exact H.
    + apply IH.
      lia.
Qed.

  
  Lemma down_coq (P: nat-> Prop):
    forall n j,
      j <= n ->
      P n ->
      (forall k, k < n -> P (S k) -> P k) ->
      P j.
  Proof.
    move=> n j Hj Hn Hstep.
    pose proof (lt_wf_ind n (fun j => j <= n -> P j)).
    move=> k IH Hk.
    have [->|Hlt] := Nat.eq_dec k n.
    - exact Hn.
    - apply Hstep; lia.
  Qed.
  
  Lemma decode_auxP4 (p: nat -> nat) n col:
    prefix_sum p n + p n < col -> 
    forall j, j < n -> decode_aux j (col - prefix_sum p j) p = decode_aux n (col - prefix_sum p n) p.
  Proof.
    move => H1.
    
    
    + move => col H1 j. rewrite leqn0 =>/eqP ->. rewrite decode_auxP0. 
      by have ->: p 0 < col - prefix_sum p 0 = false by lia.
    + move => n Hn col H1 j H2.
      case H3: (j == n.+1).
      ++ move: H3 => /eqP ->.
         pose proof decode_auxP1 p n.+1 col as ->.
         by have ->:  p n.+1 < col - prefix_sum p n.+1 = false by lia.
      ++ have H4: j <= n by lia.
  Admitted.
  
*)

  Definition decode' (p : nat -> nat) (n : nat): nat * nat := decode_aux 0 n p.

  Definition encode' (p : nat -> nat) (rc : nat * nat) : nat := (prefix_sum p rc.1 + rc.2).
  
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
