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
From mathcomp Require Import all_boot seq order boolp classical_sets contra. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".

From RL Require Import rel seq1 seq2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** What is done here: 
    given a path (f 0) -> (g 0) -> (f 1) -> g(1) -> f(2) in a graph 
    defined by a relation R, where the function f and g are given.
    for each i, (f i) is a node in T and (g i) is a sequence in T (giving a path).
    We want to build a function val such that the path is given by 
    (val 0) -> (val 1) -> (val 2) -> .....
    Moreover, using properties of f and g with respect to the relation R, 
    we want to prove that val is injective. 
*)

Section val_construction.
  (** utilities *)
  
  Context (T:eqType) (f: nat -> T) (g: nat -> seq T).
  
  Section prelude.
    (** utilities *)
    Context (p: nat -> nat).
    
    Definition csum (n : nat) : nat:=
      let fix loop m := if m is i.+1 then (loop i) + (p i).+1 else 0 in loop n.
    
    Lemma csumP n: (csum n.+1) = (csum n) + (p n).+1.
    Proof. by []. Qed.

    Lemma csum_strict_inc n: csum n < csum n.+1.
    Proof. rewrite /= ;by lia. Qed.

    Lemma csum_gt_id n : csum n >= n.
    Proof. elim: n => [// |n Hr];apply: (leq_ltn_trans Hr (csum_strict_inc n)). Qed.
    
    Lemma csum_inc  n m : n < m -> csum n < csum  m.
    Proof. 
      elim: m n => [n // | m' Hn n H1]. 
      case H2: (n == m');first by move: H2 => /eqP ->;apply: csum_strict_inc.
      move: H1;rewrite leq_eqVlt => /orP [H3 | H3];first by lia.
      have /Hn H4: n < m' by lia.
      have H5:  csum n <= csum m' by lia. 
      by rewrite csumP;apply: (leq_ltn_trans H5 _);lia.
    Qed.
    
    Lemma csum_inc1 n m: n <= m -> csum n <= csum m.
    Proof. 
      by move => ?;case H2: (n == m);[move: H2 => /eqP ->|apply/ltnW/csum_inc;lia].
    Qed.
    
    Lemma csum_up  n: exists k, n < csum k.
    Proof.
      by  (exists n.+1);apply: (leq_ltn_trans (csum_gt_id n) (csum_strict_inc n)).
    Qed.
    
    Definition csumI n:= (ex_minn (csum_up n)).-1.

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
    
    Lemma incr_sandwich n j: (csumI n) < j -> n <= (csum j).
    Proof.
      move: (exists_sandwich n) => /andP [H1 H2] H3.
      have H4: csum (csumI n).+1 <= csum j by apply: csum_inc1.
      by lia.
    Qed.
    
    Lemma incr_sandwich1 n j: (csum j) < n -> j <= (csumI n).
    Proof. contra. apply: incr_sandwich.
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
      + have H6': n.+1 = csum j.+1 by lia.
        by apply: csumI0; rewrite H6' [csum j.+2]csumP; lia.
    Qed.

    Lemma csumI1' n j: n= (csum j) -> (n.+1 < csum j.+1) = false -> (p j)=0.
    Proof.
      move => H1 H2.
      have H3: n < csum j.+1 by rewrite H1;apply: csum_inc.
      have: n.+1 = csum j.+1 by lia.
      by rewrite csumP -H1;lia.
    Qed.
    
    Lemma csumI2 n: if (n.+1 < csum (csumI n).+1) then (csumI n.+1) = (csumI n) 
                    else (csumI n.+1) = (csumI n).+1.
    Proof. by  move: (exists_sandwich n) => /csumI1. Qed.
    
    Lemma csumI3 n: n.+1 = csum (csumI n).+1 -> (csumI n.+1) = (csumI n).+1.
    Proof.
      by move: (csumI2 n) => + H1;have ->: (n.+1 < csum (csumI n).+1) = false by lia.
    Qed.

    Definition decode n := (csumI n, n - (csum (csumI n))).

    Lemma decodeP n j: ((csum j) <= n < csum j.+1) -> (decode n)= (j, n -(csum j)).
    Proof. by move => /(@csumI0 n j) <-. Qed.
    
    Lemma decode_next n j k: 
      (decode n) = (j,k) 
      -> (decode n.+1) = if (n.+1 < csum j.+1) then (j, k.+1) else (j.+1,0).
    Proof.
      rewrite /decode => -[H1 H2].
      pose proof (exists_sandwich n) as H3.
      move: H2 H3;rewrite H1 => H2 /[dup] /andP [H3 H3'] /csumI1. 
      case H4: (n.+1 < csum j.+1). 
      + move => ->. 
        by have ->: n.+1 - csum j = k.+1 by lia. 
      + move => ->.
        case H5: (n.+1 == csum j.+1);last by lia.
        by move: H5 => /eqP H5;rewrite -H5 subnn.
    Qed.
    
    (** unused: we just use decode 
        Definition encode (rc : nat * nat) : nat := (csum rc.1 + rc.2).
     *)

  End prelude.
  
  Section val_def_and_properties.

    (** we specialize previous section to the case when p is (fun n' => (size (g n')) *)
    Definition p := (fun n => (size (g n))).

    (** unused: we just use decode 
        Definition encode' (g : nat -> seq T) (rc : nat * nat) : nat := encode (fun n' => (size (g n'))) rc.
    *)

    Definition val n := 
      let (row,col):= decode p n in 
      if col == 0 then (f row) else nth (f row.+1) (g row) col.-1.

    Lemma valP n j: ((csum p j) <= n < csum p j.+1)
                     -> val n = (if n - csum p j == 0
                                then f j
                                else nth (f j.+1) (g j) (n - csum p j).-1).
    Proof. by move => /(@csumI0 p n j) H1; rewrite  /val /decode H1. Qed.

    Lemma valP' n j z: ((csum p j) <= n < csum p j.+1)
                       -> val n = nth z ((f j)::(rcons (g j) (f j.+1))) (n - csum p j).
    Proof. 
      move => /[dup] H1 /valP.
      case H2: (n - csum p j == 0);first by move: H2 => /eqP -> /=.
      have H3: csum p j < n by lia.
      move: H1;rewrite csumP [(p j)]/p => [H1 H1'].
      have H6: 0 < n - csum p j <=  (size (g j)) by lia.
      case H7: (n - csum p j == (size (g j))).
      by move: H7 H1' => /eqP ->;rewrite nth_L1 => ->;apply: nth_dv; lia.
      have H8:  0 < n - csum p j <  (size (g j)) by lia.
      rewrite (@nth_L2 T (g j) (f j) (f j.+1) z (n -csum p j) H8) H1'.
      by apply: nth_dv; lia.
    Qed.
    
    Lemma valP'' n j: n = (csum p j) -> val n = (f j).
    Proof.
      move => H1.
      have H2: ((csum p j) <= n < csum p j.+1) by rewrite csumP H1;lia.
      by move: H2 => /(@valP' n j (f j.+1));rewrite H1 subnn /=.
    Qed.

    Lemma valP''' n j: ((csum p j) < n < csum p j.+1) -> (val n) \in (g j).
    Proof.
      move => H1;have /(@valP n j):((csum p j) <= n < csum p j.+1) by lia.
      have ->: (n - csum p j == 0) = false by lia.
      move => H2.
      apply/nthP.
      exists (n - csum p j).-1. 
      by move: H1;rewrite csumP [(p j)]/p => /andP [H1 H1'];lia.
      by rewrite H2.
    Qed.

    Lemma valP4 n j: (csum p j) < n -> exists j', (j <= j') /\ ((val n) \in (g j') \/ (val n) = (f j')).
    Proof.
      move => H1.
      move: (@exists_sandwich p n) => H2.
      pose proof (@incr_sandwich1 p n j H1) as H3. 
      exists (csumI p n);split;first exact. 
      case H4: (n == csum p (csumI p n)). 
      by move: H4 => /eqP/valP'' H4;right.
      by (have /valP''' H5: csum p (csumI p n) < n < csum p (csumI p n).+1 by lia);left.
    Qed.
    
    Section val_path.

      Lemma allL2val (R: relation T): 
        (forall n, allL R (g n) (f n) (f n.+1)) -> forall n, R ((val n), (val n.+1)).
      Proof.
        move => H1 n.
        move: (@exists_sandwich p n) => H2.
        pose j:= (csumI p n);rewrite -/j in H2.
        pose proof (@allL_nth' T R (g j) (f j) (f j.+1) (f j.+1)) as H3.
        move: H1 => /(_ j) {}/H3 /(_ (n -csum p j)) H1.
        have H3: n - csum p j <= size (g j) by rewrite csumP [(p j)]/p in H2; lia.
        move: H3 => /H1.
        move: (H2) => /(@valP' n j (f j.+1)) <-.
        case H3: (n.+1 < csum p j.+1). 
        + have H2': csum p j <= n.+1 < csum p j.+1 by lia.
          have H4: (n.+1 - csum p j) = (n - csum p j).+1 by lia.
          by move: H2' => /(@valP' n.+1 j (f j.+1));rewrite H4 => <-.
        + have H4: n.+1 = csum p j.+1 by lia.
          have H5: (n - csum p j).+1 = csum p j.+1 -csum p j by lia.
          have H6: (n - csum p j).+1 = (p j).+1 by rewrite csumP in H5;lia.
          rewrite H6 [(p j)]/p nth_L1'.
          have H7: csum p j.+1 <= n.+1 < csum p j.+2
            by apply/andP;split;rewrite H4;[|apply: csum_strict_inc].
          pose proof (@valP' n.+1 j.+1 (f j.+1) H7) as H8.
          by rewrite H8 H4 subnn /=.
      Qed.
      
    End val_path.

    Section val_injective.

    Lemma Asym2P12 (R: relation T):
      (forall n, allLu R (g n) (f n) (f n.+1) /\ ~ R.+ (f n.+1, f n) /\ uniq ((g n) ++ (g n.+1)))
      -> ( forall n, forall n', n < n' -> ~ R.+ (f n', f n)).
    Proof.
      move => H0 n.
      elim => [// | n' Hr H1].
      case H2: (n < n'); 
        last by (have <-: n = n' by lia);move: H0 => /(_ n) [_ [? _]].
      move: H2 => /Hr H2 H3.
      move: H0 => /(_ n') [[+ _] _] => /(@allL_to_clos_t T) H4.
      by pose proof (@TclosT T R (f n') (f n'.+1) _ H4 H3).
    Qed.
    
    Lemma Asym2P9 (R: relation T): 
      (forall n, allL R (g n) (f n) (f n.+1)) 
      -> ( forall n, forall n', n < n' -> R.+ ((f n), (f n'))).
    Proof.
      move => H0 n;elim => [//| n' Hr H1].
      move: H0 => /(_ n') /(@allL_to_clos_t T R) H0.
      case H2: (n < n');first by move: H2 => /Hr H2;apply: (@TclosT T R (f n) (f n') _).
      by have /eqP ->: (n == n') by lia.
    Qed.

    Lemma Asym2P10 (R: relation T): 
      (forall n, allLu R (g n) (f n) (f n.+1)) 
      -> ( forall n, forall n', forall x, n <= n' -> x \in (g n') -> R.+ ((f n), x)).
    Proof.
      move => H0 n n' x H1' H2. 
      case H0': (n == n' ); last first.
      + have H1: ( n < n') by lia.
        have H1'': (forall n, allL R (g n) (f n) (f n.+1))
          by move: H0 => + n1 => /(_ n1) [H0 _].
        move: H1'' => /Asym2P9/(_ n n' H1) H3.
        move: H0 => /(_ n') [H4 _].
        pose proof (@allL_to_clos_t_left T _ _ _ _ x H2 H4). 
        by apply: (@TclosT T R (f n) (f n') _).
      + move: H0' => /eqP ->.
        move: H0 => /(_ n') [H0 _].
        by pose proof (@allL_to_clos_t_left T R (g n') (f n') (f n'.+1) x H2 H0). 
    Qed.
    
    Lemma Asym2P11 (R: relation T): 
      (forall n, allL R (g n) (f n) (f n.+1)) 
      -> ( forall n, forall n', forall x, n < n' -> x \in (g n) -> R.+ (x, (f n'))).
    Proof.
      move => H0 n n' x H1 H2. 
      case H3: (n.+1 < n').
      + move: H3 => /(@Asym2P9 R H0) H3.
        move: H0 => /(_ n) H4.
        pose proof (@allL_to_clos_t_right T _ _ _ _ x H2 H4). 
        by apply: (@TclosT T R x (f n.+1) _).
      + have /eqP <-: (n.+1 == n') by lia.
        move: H0 => /(_ n) H4.
        by pose proof (@allL_to_clos_t_right T _ _ _ _ x H2 H4). 
    Qed.
    
    Lemma Asym2P6 (R: relation T) z n: 
      allL R (g n) (f n) (f n.+1)
      <-> forall j, j <= size (g n) ->
             R ((nth z ((f n)::(rcons (g n) (f n.+1))) j),
                 (nth z ((f n)::(rcons (g n) (f n.+1))) j.+1)).
    Proof. by rewrite (@allL_nth' T R (g n) (f n) (f n.+1) z). Qed.

    
    Lemma Asym2P6' (R: relation T):
      (forall n, allLu R (g n) (f n) (f n.+1) /\ ~ R.+ (f n.+1, f n) /\ uniq ((g n) ++ (g n.+1)))
      -> ( forall n, forall n', n < n' -> uniq ((g n) ++ (g n'))).
    Proof.
      move => H0 n n' H1.
      move: (H0) => /[dup] /(_ n) [[H2 H3] [H4 H5]] /(_ n') [[H6 H7] [H8 H9]].
      case C1: (n' == n.+1);first by move: C1 => /eqP ->. 
      have H10: n.+1 < n' by lia.
      move: H3 H7;rewrite 2!uniq_crc => -[_ [_ [H3 _]]] -[_ [_ [H7 _]]].
      rewrite uniq_catE H3 H7;split;[exact |split;[exact|]].
      move => x H11 H12.
      pose proof (@allL_to_clos_t_left T _ _ _ _ x H12 H6) as T0.
      pose proof (@allL_to_clos_t_right T _ _ _ _ x H11 H2) as T1.    
      have H13: R.+ (f n', f n.+1) by apply: (@TclosT T R _ _ _ T0 T1).
      by pose proof (@Asym2P12 R H0 _ _ H10).
    Qed.
    
    Lemma allL2valu (R: relation T): 
      (forall n, @allLu T R (g n) (f n) (f n.+1) /\ ~ R.+ (f n.+1, f n) /\ uniq ((g n) ++ (g n.+1)))
      -> forall n, forall n', n < n' -> (val n) = (val n') -> False.
    Proof.
      move => H1 n n' H2 H3.
      move: (@exists_sandwich p n) => H4.
      pose j:= (csumI p n);rewrite -/j in H4.
      case H5: (n' < csum p j.+1).
      + (* n and n' are in the same interval csum p j <= . < csum p j.+1 *)
        move: H1 => /(_ j) [[H6 H6'] [H7 H8]].
        move: (H4) => /(@valP' n j (f j.+1)) H9.
        have H4':  csum p j <= n' < csum p j.+1 by lia.
        move: (H4') => /(@valP' n' j (f j.+1)) H9'.
        move: H3;rewrite H9 H9'.
        pose proof (@uniq_nth3 T (f j :: rcons (g j) (f j.+1)) (f j.+1)) as H10.
        move: H6' => {}/H10 /(_ (n - csum p j) (n' - csum p j)) H6'.
        have H10: n - csum p j < n' - csum p j  by lia.
        have H11: n' - csum p j < size (f j :: rcons (g j) (f j.+1))
          by rewrite /= size_rcons;rewrite csumP [(p j)]/p in H5; lia.
        move: H10 => /H6' H10.
        move: H11 => /H10 H11.
        by move => H12;rewrite H12 in H11.
      + (* csum p j <= n < csum p j.+1 and csum p j.+1 <= n' *)
        case H5': (n' == csum p j.+1).
        ++ move: H1 => /(_ j) [[H6 H6'] [H7 H8]].
           move: (H4) => /(@valP' n j (f j.+1)) H9.
           move: H5' => /eqP/[dup] H5' /(@valP''  n' j.+1).
           pose proof (@uniq_nth3 T (f j :: rcons (g j) (f j.+1)) (f j.+1)) as H10.
           move: H6' => {}/H10 /(_ (n - csum p j) (n' - csum p j)) H6'.
           have H10: n - csum p j < n' - csum p j  by lia.
           have H11: n' - csum p j < size (f j :: rcons (g j) (f j.+1))
             by rewrite /= size_rcons H5' csumP [(p j)]/p;lia. 
           move: H10 => {}/H6' H10.
           move: H11 => {}/H10 H11 H12.
           move: H11;rewrite H5' csumP [(p j)]/p.
           have ->: (csum p j + (size (g j)).+1 - csum p j) = (size (g j)).+1 by lia.
           by rewrite  nth_L1' -H9 -H12 H3.
        ++ (* now csum p j <= n < csum p j.+1 and csum p j.+1 < n' *)
          have H6: csum p j.+1 < n' by lia.
          move: (@valP4 _ _ H6) => [j' [H7 [H8 | H8]]].
          +++ (* val n' \in g j' *) 
            case H9: (n == csum p j).
            ++++ (** val n = f j and val n' \in g j' *)
              move: H9 => /eqP/valP'' H9.
              have H10:  forall n : nat, allLu R (g n) (f n) (f n.+1)
                  by move: H1 => + n1 => /(_ n1) [H1 _].
              pose proof (@Asym2P10 R H10 j' j' (val n') (leqnn j') H8) as H11.
              move: H11;rewrite -H3 H9 => H11.
              by pose proof (@Asym2P12 R H1 j j' H7).
            ++++ (** val n = g j and val n' = g j' *)
              have H10:  csum p j < n < csum p j.+1 by lia.
              move: H10 => /valP''' H10. 
              move: H1 => /(@Asym2P6') /(_ j j' H7) /uniq_catE [_ [_ H1]].
              apply: H1. apply: H10. rewrite H3. apply: H8.
          +++ (** val n' = f j' *)
            case H9: (n == csum p j).
            ++++  (** val n= (f j) et val n'= (f j') *)
              move: H9 => /eqP/valP'' H9.
              pose proof (@Asym2P12 R H1 j j' H7) as H10.
              move: H10;rewrite -H8 -H9 -H3 => H10.
              have H11: (forall n, allL R (g n) (f n) (f n.+1))
                by move: H1 => + n1 => /(_ n1) [[H1 _] _].
              pose proof (@Asym2P9 R H11 j j' H7) as H12.
              move: H12; rewrite  -H8 -H9 -H3 => H12.
              exact.
            ++++ (** val n= (g j) et val n'= (f j') *)
              have H10:  csum p j < n < csum p j.+1 by lia.
                 move: H10 => /valP''' H10. 
                 move: (H1) => /(_ j) [[H01 H1'] _].
                 case H12: (j' == j.+1). 
                 +++++ move: H12 => /eqP H12.
                 rewrite H12 -H3 in H8.
                 move: H1' => /(@uniqE T (g j) (f j) (f j.+1) (val n)) [_ [H1' _]].
                 move: H1' => /(_ (index (val n) (g j))) H1'.
                 rewrite nth_index in H1'.
                 move: (H10); rewrite -index_mem => /H1'.
                 by rewrite -H8.
                 exact.
                 +++++ 
                 pose proof (@allL_to_clos_t_right T R (g j) (f j) (f j.+1) (val n) H10 H01) as H11. 
                 move: H11;rewrite H3 H8 => H11.
                 have H13: j.+1 < j' by lia.
                 pose proof (@Asym2P12 R H1 _ _ H13).
                 exact.
    Qed.

    Lemma is_inj: 
      (forall n, forall n', n < n' -> (val n) = (val n') -> False) -> injective val.
    Proof.
      move => H1 n n' H2.
      case H3: ((n < n') || (n' < n));
        first by move: H3 => /orP [/H1 /[!H2] ? |/H1 /[!H2] ?] //.
      lia.
    Qed.
    
    Lemma allL2val_inj (R: relation T): 
      (forall n, @allLu T R (g n) (f n) (f n.+1) /\ ~ R.+ (f n.+1, f n) /\ uniq ((g n) ++ (g n.+1)))
      -> injective val. 
    Proof. by move => /allL2valu H1;apply: is_inj. Qed.
    
    End val_injective .

  End val_def_and_properties.

End val_construction.

