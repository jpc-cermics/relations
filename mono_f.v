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
  
  Context (T:Type) (f: nat -> T) (g: nat -> seq T).
  
  Section cum_sum. 

    Context (p: nat -> nat).
    
    Definition csum (n : nat) : nat:=
      let fix loop m := if m is i.+1 then (loop i) + (p i).+1 else 0 in loop n.
    
    Lemma csumP n: (csum n.+1) = (csum n) + (p n).+1.
    Proof. by []. Qed.

    Lemma csum_strict_inc n: csum n < csum n.+1.
    Proof. rewrite /= ;by lia. Qed.

    Lemma csum_gt_id n : csum n >= n.
    Proof. elim: n => [// |n Hr];apply: (leq_ltn_trans Hr (csum_strict_inc n)). Qed.
    
    Lemma csum_inc  i j : i < j -> csum i < csum  j.
    Proof. 
      elim: j i => [i // | n Hn i H1]. 
      case H2: (i == n);first by move: H2 => /eqP ->;apply: csum_strict_inc.
      move: H1;rewrite leq_eqVlt => /orP [H3 | H3];first by lia.
      have /Hn H4: i < n by lia.
      have H5:  csum i <= csum n by lia. 
      by rewrite csumP;apply: (leq_ltn_trans H5 _);lia.
    Qed.
    
    Lemma csum_inc1  i j : i <= j -> csum i <= csum j.
    Proof.
      by move => H1;case H2: (i == j );[move: H2 => /eqP ->|apply/ltnW/csum_inc;lia].
    Qed.
    
    Lemma csum_up  i: exists k, i < csum k.
    Proof.
      by  (exists i.+1);apply: (leq_ltn_trans (csum_gt_id i) (csum_strict_inc i)).
    Qed.

    Definition csumI n := (ex_minn (csum_up n)).-1.

    Lemma exists_sandwich n:
      (csum (csumI n)) <= n < csum (csumI n).+1.
    Proof.
      pose j:= (ex_minn (csum_up n)).-1; rewrite /csumI -/j. 
      case H1: (n <= p 0).
      + have H2: (ex_minn (csum_up n)).-1 = 0
          by case: ex_minnP => m _ /(_ 1);rewrite /csum add0n ltnS H1;lia.
        by rewrite /j H2 /= add0n ltnS H1.
      + move: H1;rewrite leqNgt => /negP/negP H1.
        pose  k0 := (ex_minn (csum_up n)).
        have H2: ~(0 = k0) 
          by rewrite /k0;case: ex_minnP  => k H3 ?;move => H5;rewrite -H5 in H3.
        have H3: 0 < k0 by lia.
        have H4: k0.-1.+1 = k0 by lia.
        move: H3 H4;rewrite /j /k0;case: ex_minnP => // k H3 H5 H6 ->. 
        rewrite H3 andbT. 
        have: n < csum  k.-1 -> False by move => /H5 H4; lia.
        by lia.
    Qed.
    
    Lemma uniq_sandwich n j k:
      ((csum j) <= n < csum j.+1) -> ((csum k) <= n < csum k.+1) ->  j = k.
    Proof.
      move => H1 H2.
      case H3: ( j == k);first by move: H3 => /eqP ->.
      case H4: (j < k).
      + have H6: csum j.+1 <= csum k by apply: csum_inc1.
        have H7: n < n by lia.  
        by have H8: false by rewrite -(ltnn n).
      + have H5: k < j by lia.
        have H6: csum k.+1 <= csum j by apply: csum_inc1.
        have H7: n < n by lia.  
        by have H8: false by rewrite -(ltnn n).
    Qed.
    
    Lemma csumI0 n j: ((csum j) <= n < csum j.+1) -> (csumI n) = j.
    Proof.
      move => H1;pose proof (exists_sandwich n) as H2.
      by apply: (@uniq_sandwich n (csumI n) j).
    Qed.
    
    Lemma csumI0' n j: ((csum j) < n < csum j.+1) -> (n - (csum j)).-1 < (p j).
    Proof. by rewrite csumP => H1;lia. Qed.

    Lemma csumI1 n j: ((csum j) <= n < csum j.+1)
                      -> if (n.+1 < csum j.+1) then (csumI n.+1) = j
                        else (csumI n.+1) = j.+1. 
    Proof.
      move => /andP [H1 H2].
      case H3: (n.+1 < csum j.+1).
      + have H4: (csum j) <= n.+1 < (csum j.+1) by lia.
        pose proof (exists_sandwich n.+1) as H5.
        by apply: (@uniq_sandwich n.+1 (csumI n.+1) j).
      + pose proof (exists_sandwich n.+1) as H5.
        have H6: csum j.+1 <= n.+1 by lia.
        have H7: n.+1 < csum j.+2 by rewrite csumP;lia.
        have H8: csum j.+1 <= n.+1 < csum j.+2 by rewrite H6 H7.
        by apply: (@uniq_sandwich n.+1 (csumI n.+1) j.+1).
    Qed.
    
    Lemma csumI2 n: if (n.+1 < csum (csumI n).+1) then (csumI n.+1) = (csumI n) 
                    else (csumI n.+1) = (csumI n).+1.
    Proof. by  move: (exists_sandwich n) => /csumI1. Qed.
    
    Lemma csumI3 n: n.+1 = csum (csumI n).+1 -> (csumI n.+1) = (csumI n).+1.
    Proof.
      by move: (csumI2 n) => + H1;have ->: (n.+1 < csum (csumI n).+1) = false by lia.
    Qed.

    Definition decode0 n := (csumI n, n - (csum (csumI n))).

    Lemma decode0P n j: ((csum j) <= n < csum j.+1) -> (decode0 n)= (j, n -(csum j)).
    Proof. by move => /(@csumI0 n j) <-. Qed.
    
    Lemma decode_next n j k: 
      (decode0 n) = (j,k) 
      -> (decode0 n.+1) = if (n.+1 < csum j.+1) then (j, k.+1) else (j.+1,0).
    Proof.
      rewrite /decode0 => -[H1 H2].
      pose proof (exists_sandwich n) as H3.
      move: H2 H3;rewrite H1 => H2 /[dup] /andP [H3 H3'] /csumI1. 
      case H4: (n.+1 < csum j.+1). 
      + move => ->. 
        by have ->: n.+1 - csum j = k.+1 by lia. 
      + move => ->.
        case H5: (n.+1 == csum j.+1);last by lia.
        by move: H5 => /eqP H5;rewrite -H5 subnn.
    Qed.
    
  End cum_sum.
  
  Section cum_sum1.

    (** we specialize previous section to the case when p is (fun n' => (size (g n')) *)
    Definition p := (fun n => (size (g n))).
    
    Definition val n := 
      let (row,col):= decode0 p n in 
      if col == 0 then (f row) else nth (f row) (g row) col.-1.

    Lemma valP3 n j: ((csum p j) <= n < csum p j.+1)
                     -> val n = (if n - csum p j == 0
                                then f j
                                else nth (f j) (g j) (n - csum p j).-1).
    Proof. by move => /(@csumI0 p n j) H1; rewrite  /val /decode0 H1. Qed.
    
    Lemma valP1 n j: n = csum p j -> val n = f j.
    Proof.
      move => H1.
      have H2: ((csum p j) <= n < csum p j.+1) by rewrite H1 csumP; lia.
      by move: (valP3 H2); rewrite -H1 subnn /=.
    Qed.
    
    Lemma valP2 n j: ((csum p j) < n < csum p j.+1)
      -> val n = nth (f j) (g j) (n - (csum p j)).-1.
    Proof.
      move => H1. 
      have H2: ((csum p j) <= n < csum p j.+1) by lia.
      move: (valP3 H2).
      by have ->: (n - csum p j == 0)= false by lia.
    Qed.

    Lemma test (R: relation T): 
      (forall n, allL R (g n) (f n) (f n.+1))  -> forall n, R ((val n), (val n.+1)).
    Proof.
      move => H1 n.
      move: (@exists_sandwich p n) => H2.
      pose j:= (csumI p n);rewrite -/j in H2.
      pose proof (@allL_nth T R (g j) (f j) (f j.+1) (f j)) as H3.
      move: H1 => /(_ j) /H3 [H3' [H4 H5]].
      clear H3.
      case H6: (csum p j == n).
      + move: H6 => /eqP H6.
        have H7: (val n) = f j. by apply: valP1.
        (** we have to explore n.+1 **)
        admit.
      + have H7: ((csum p j ) < n < csum p j.+1) by lia.
        have H8: (val n) = nth (f j) (g j ) (n - (csum p j)).-1 
          by apply: valP2.
        admit.
    Admitted.


  End cum_sum1.
  
  Section encode_decode. 
    (* using equations to obtain a computable function *)

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
      decode_aux j (col - csum p j) p
      = if (col - csum p j) <= (p j) then (j, col - csum p j)
        else decode_aux j.+1 (col - (csum p j.+1)) p.
    Proof.
      elim: j col => [col | j _ col];
                    first by rewrite csumP /= subn0 add0n;apply: decode_auxP0.
      rewrite decode_auxP0. 
      have ->: col - csum p j.+2 = col - csum p j.+1 - (p j.+1).+1
        by  rewrite [in LHS]csumP;lia.
      exact.
    Qed.
    
    Lemma decode_auxP2 (p: nat -> nat) n col: 
      csum p n.+1 <= col -> 
      forall j, j < n -> decode_aux j (col - csum p j) p = 
                     decode_aux j.+1 (col - csum p j.+1) p.
    Proof.
      move => H1 j H2.
      have H3:  j.+1 < n.+1 by lia.
      have H4: csum p j.+1 < col 
        by pose proof (@csum_inc p j.+1 n.+1 H3);lia.
      rewrite csumP in H4.
      have H5: (col - csum p j) <= (p j) = false by lia.
      by rewrite decode_auxP1 H5.
    Qed.
    
    Definition P (p: nat -> nat) n j col := 
      decode_aux j (col - csum p j) p = decode_aux n (col - csum p n) p.
    
    Lemma decode_auxP3 (p: nat -> nat) n col j:
      csum p n.+1 <= col -> j < n -> P p n j.+1 col -> P p n j col.
    Proof. by rewrite /P;move => H1 H2 <-;apply: (decode_auxP2 H1). Qed.
    
    Lemma decode_auxP4 (p: nat -> nat) n col: P p n n col.
    Proof. by []. Qed.
    
    Lemma decode_auxP5 (p: nat -> nat) n col:
      csum p n.+1 <= col -> ~ (P p n 0 col) -> forall j, j <= n -> ~(P p n j col).
    Proof.
      move => H1 H2.
      elim => [// | j Hr H3 /(@decode_auxP3 p n col j H1 H3)H4].
      by have H5: ~ P p n j col by apply: Hr;lia.
    Qed.
    
    Lemma decode_auxP6 (p: nat -> nat) n col:
      csum p n.+1 <= col -> ~ (P p n 0 col) -> False. 
    Proof.  
      move => H1 H2; move: (decode_auxP5 H1 H2) => /(_ n) H3.
      by (have /H3 H4: n <= n by lia);have H5: P p n n col by [].
    Qed.
    
    Lemma decode_auxP7 (p: nat -> nat) n col:
      csum p n.+1 <= col -> (P p n 0 col). 
    Proof.
      by move => H1;move: (decode_auxP6 H1) => H2;apply: contrapT => /H2 ?.
    Qed.

    Lemma decode_auxP8 (p: nat -> nat) n col:
      csum p n.+1 <= col -> 
      decode_aux 0 col p = decode_aux n (col - csum p n) p.
    Proof. by move => H1;move: (decode_auxP7 H1);rewrite /P /= subn0. Qed.
    
    Lemma decode_auxP9 (p: nat -> nat) n col:
      col < csum p n.+1 ->
      decode_aux n (col - csum p n) p = (n, col - (csum p n)).
    Proof. 
      move => H1. 
      rewrite decode_auxP1.
      have H2: col - csum p n <= p n by rewrite csumP in H1; lia.
      by rewrite H2.
    Qed.
    
    Lemma decode_auxP10 (p: nat -> nat) n col:
      csum p n.+1 <= col < csum p n.+2 -> 
      decode_aux 0 col p = (n.+1, col - (csum p n.+1)).
    Proof. 
      move => /andP [/[dup] H0 /decode_auxP8 -> /decode_auxP9 <-]. 
      rewrite decode_auxP1.
      by have -> : col - csum p n <= p n = false by rewrite csumP in H0; lia.
    Qed.

    Lemma decode_auxP11 (p: nat -> nat) n col:
      csum p n <= col < csum p n.+1 -> 
      decode_aux 0 col p = (n, col - (csum p n)).
    Proof. 
      case H1: (n== 0);first by move: H1 => /eqP -> /=;rewrite add0n subn0 ltnS decode_auxP0 => ->.
      move: H1 => /neq0_lt0n H1.
      have H2: n.-1.+1 = n by lia.
      by rewrite -H2 => /decode_auxP10 H3.
    Qed.
    
    Definition decode2 (p : nat -> nat) (n : nat): nat * nat := decode_aux 0 n p.

    (* 
    Lemma decodeP (p : nat -> nat) col: exists gamma: nat ->nat,  (decode2 p col) = (decode0 p col).
    Proof.
      pose proof (gamma p) as [gamma H1]; exists gamma;rewrite /decode2 /decode1.
      by move: H1 => /(_ col) => /(@decode_auxP11 p (gamma col) col) ->.
    Qed.
    *)
    
    Section Example.
      
      Definition p' n := 
        match n with 
        | 0 => 3
        | 1 => 2
        | 2 => 0
        | _ => 1
        end.
      
      (** we can preform computations with decode2 version *)
      
      Compute (decode2 p' 0).
      Compute (decode2 p' 1).
      Compute (decode2 p' 2).
      Compute (decode2 p' 3).
      Compute (decode2 p' 4).
      Compute (decode2 p' 5).
      Compute (decode2 p' 6).
      Compute (decode2 p' 7).
      Compute (decode2 p' 8).
      Compute (decode2 p' 9).
      Compute (decode2 p' 10).
      Compute (decode2 p' 11).
      
    End Example.
    
  End encode_decode. 
  
  (*

  Definition decode' (g : nat -> seq T) (i : nat) : nat * nat := decode2 (fun n' => (size (g n'))) i.

  Definition encode' (g : nat -> seq T) (rc : nat * nat) : nat := encode0 (fun n' => (size (g n'))) rc.
  
  Definition val' (f: nat -> T) (g : nat -> seq T) n := 
    let (row,col):= decode' g n in 
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

    Compute (decode' g 0).
    Compute (decode' g 1).
    Compute (decode' g 2).
    Compute (decode' g 3).
    Compute (decode' g 4).
    Compute (decode' g 5).
    Compute (decode' g 6).
    Compute (decode' g 7).
    
    (* should give a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 *)
    Compute ((val' f g  0) =   (nth m1 L 0)).
    Compute ((val' f g  1) =   (nth m1 L 1)).
    Compute ((val' f g  2) =   (nth m1 L 2)).
    Compute ((val' f g  3) =   (nth m1 L 3)).
    Compute ((val' f g  4) =   (nth m1 L 4)).
    Compute ((val' f g  5) =   (nth m1 L 5)).
    Compute ((val' f g  6) =   (nth m1 L 6)).
    Compute ((val' f g  7) =   (nth m1 L 7)).
    Compute ((val' f g  8) =   (nth m1 L 8)).
    Compute ((val' f g  9) =   (nth m1 L 9)).
    Compute ((val' f g  10) =  (nth m1 L 10)).
    
    Compute (encode' g (decode' g 0)) == 0.
    Compute (encode' g (decode' g 1)) == 1.
    Compute (encode' g (decode' g 2)) == 2.
    Compute (encode' g (decode' g 3)) == 3.
    Compute (encode' g (decode' g 4)) == 4.
    Compute (encode' g (decode' g 5)) == 5.
       
  End demo.
  *)


End walk.

    (** version obsolete avec gamma construite avec choix dependent *)
    (** 
    Theorem exists_sandwich' n:
      exists j, ((csum j) <= n < csum j.+1).
    Proof.
      case H1: (n <= 0);
        first by move: H1;rewrite /csum => H1;exists 0;rewrite /csum add0n;lia.
      move: H1;rewrite leqNgt => /negP/negP H1.
      have hex: exists k, n < csum k
          by  (exists n.+1);apply: (leq_ltn_trans (csum_gt_id n) (csum_strict_inc n)).
      pose  k0 := ex_minn hex.
      have H2: ~(0 = k0) by rewrite /k0;case: ex_minnP  => k H3 ?;move => H5;rewrite -H5 in H3.
      have H3: 0 < k0 by lia.
      exists k0.-1.
      have ->: k0.-1.+1 = k0 by lia.
      move: H3. rewrite /k0. case: ex_minnP => // k -> H5 H6.
      rewrite andbT. 
      have H7: n < csum k.-1 -> False  by move => /H5 H7; lia.
      by lia.
    Qed.
    

    (** build a function using choice on exists_sandwich theorem *)
    Lemma gamma: exists (gamma : nat -> nat), 
      (forall n, ((csum (gamma n)) <= n < csum (gamma n).+1)) 
      /\ (forall n j, (csum (gamma n)) <= j < csum (gamma n).+1
                -> gamma j = gamma n).
    Proof.
      pose R:= [set ij | ((csum ij.2) <= ij.1) && (ij.1 < csum (ij.2).+1)].
      have Tr: total_rel R by move => n;move: (exists_sandwich' n) => [j H1];exists j.
      pose proof (choice'  Tr) as [gamma H1];exists gamma.
      by split;[| move => n j;apply: uniq_sandwich; apply: H1].
    Qed.

    Definition decode1 (gamma:  nat -> nat) n := ((gamma n), n - (csum (gamma n))).
    
    Definition encode1 (rc : nat * nat) : nat := (csum rc.1 + rc.2).
    
    Lemma encode_decode (gamma' : nat -> nat) (n:nat): 
      (n >= csum (gamma' n)) -> encode1 (decode1 gamma' n) = n.
    Proof. by rewrite  /decode1 /encode1 /=;lia. Qed.

    Lemma encode_decode':
      exists (gamma : nat -> nat), forall n, encode1 (decode1 gamma n) = n.
    Proof.
      pose proof gamma as [gamma [H1 H1']].
      by exists gamma;move => n;move: H1 => /(_ n) /andP [H1 H2];rewrite  /decode1 /encode1 /=;lia.
    Qed.
    
     *)
