(* -*- Encoding : utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect seq order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets order.
Set Warnings "parsing coercions".

From RL Require Import  seq1 ssrel rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Reserved Notation "R [Set<=] S" (at level 4, no associativity). 

Section Seq1_plus. 
  (** * extensions of results from seq1 and rel using eqType *)

  Variables (T:eqType) (R: relation T).

  (** * utilities for uniq *)
  Lemma uniq_subseq: forall (st st': seq T) (x:T),
      uniq (x :: st) -> subseq st' st -> uniq (x:: st').
  Proof.
    move => st st' x;rewrite /uniq -/uniq => /andP [H2 H3] H4.
    have -> : uniq st' by apply subseq_uniq with st.
    rewrite andbT.
    move: H4 => /subseqP [m H4 H5].
    have H6: x \in st' -> x \in st by rewrite H5; apply mem_mask.
    have H7: x \notin st -> x \notin st'. by apply contra in H6.
    by apply H7. 
  Qed.

  (** * properties of \in for eqType *)
  
  Lemma allset_in: forall (st: seq T) (x:T) (X:set T),
      x \in st -> st [\in] X -> x \in X.
  Proof.
    elim => [ x X // | y st Hr x X ].
    rewrite in_cons allset_cons.
    move => /orP [/eqP -> | H1] [/inP H2 H3];[exact | by apply Hr].
  Qed.
    
  Lemma in_non0: forall (st:seq T) (x:T), x \in st -> size(st) > 0.
  Proof.
    move => st x H1.
    by case H3: (size st);[apply size0nil in H3;rewrite H3 in_nil in H1|].
  Qed.

  Lemma in_rev: forall (st: seq T) (x:T), 
      x \in st <-> x \in (rev st).
  Proof.
    move => st1 x. 
    have H1: forall st, (x \in st) -> (x \in (rev st)).
    move => st.
    elim: st x =>  [ x // | z st' H1 x ].
    rewrite in_cons rev_cons -cats1 mem_cat.
    move => /orP [ /eqP H2 | H2].
    by rewrite -H2 mem_seq1;have /eqP -> : x = x by [];rewrite orbT.
    by apply H1 in H2;rewrite H2 orbC orbT.
    (* main *)
    by split;[ apply H1 | move => /H1 H2; rewrite revK in H2].
  Qed.
  
  Lemma head_in: forall (st:seq T) (x y:T), size(st) > 0 -> head x (rcons st y) \in st.
  Proof.
    elim => [x y // | z st Hr x y _ /=].
    by rewrite in_cons eq_refl orbC orbT.
  Qed.
  
  Lemma in_rcons: forall (st:seq T) (x y:T), (x \in rcons st y) = (x \in st) || (x == y).
  Proof.
    elim => [x y /= | z st Hr x y]; first by rewrite mem_seq1.
    by rewrite rcons_cons 2!in_cons Hr /= orbA.
  Qed.
 
  Lemma Lift_in_FF: forall (st: seq T) (x y: T),
      (rcons st y) [L\in] R -> y \in R.+#_(x) -> st [\in] R.+#_(x).
  Proof.
    move => st x y H1 H2.
    pose proof Lift_in_F H1 as H3.
    have H4:  R.+#_(y) `<=` R.+#_(x) by apply Fset_t5. 
    by apply allset_subset with R.+#_(y). 
  Qed.
  
  Lemma Lxx: forall (st: seq T) (y z: T),
      y \in st -> (rcons st z) [L\in] R -> R.+ (y, z).
  Proof.
    move => st' y z H2 . 
    pose proof in_non0 H2 as H1. 
    pose proof seq_c H1 as [st [x ->]]. 
    move => H3.
    pose proof Lift_in_F H3 as H4.
    pose proof allset_in H2 H4 as H5.
    by rewrite inP -Fset_t0 in H5.
  Qed.
  
  Lemma Lxx8: forall (st: seq T) (x y: T),
      y \in st -> (x::st) [L\in] R -> R.+ (x, y).
  Proof.
    move => st' x y H2.
    pose proof in_non0 H2 as H1.
    pose proof seq_c H1 as [st [x' ->]]. 
    move => H3.
    pose proof Lift_in_A H3 as H4.
    pose proof allset_in H2 H4 as H5.
    by rewrite inP -Fset_t0 in H5.
  Qed.
  
  Lemma Lxx3: forall (st: seq T) (x y z: T),
      (y \in st) -> (rcons (rcons st x) z) [L\in] R -> R.+ (y,x).
  Proof.
    move => st x y z;rewrite Lift_rcrc allset_rcons => [H1 [H2 _]].
    by pose proof Lxx H1 H2.
  Qed.

  Lemma Lxx10: forall (st: seq T) (x y:T),
      y \in rcons st x -> (rcons st x)  [L\in] R -> R (x,y) -> x \in Aset R.+ [set y].
  Proof.
    move => st x y.
    rewrite in_rcons => /orP [H1 | /eqP ->] H2 H3.
    by pose proof Lxx H1 H2 as H4;rewrite inP /mkset /=;(exists y).
    by rewrite inP /mkset /=;(exists x);split;[apply t_step|].
  Qed.

  Lemma Lxx9: forall (st: seq T) (t x y:T),
      (t \in x :: st) -> (x :: rcons st y) [L\in] R -> 
      t= (last y st) \/  R.+ (t, last y st).
  Proof.
    move => st t x y.
    rewrite in_cons => /orP [/eqP -> | H1].
    - case H2: (size st).
      + move: H2 => /size0nil -> /= => /andP [/inP H2 _].
        by right;apply t_step.
      + rewrite Lift_crc allset_cons.
        have H3: size st > 0 by rewrite H2.
        pose proof seq_rc H3 as [st' [u ->]].
        case H4: (size st').
        ++ move: H4 => /size0nil -> /= => [[H4 _]].
           by right;apply t_step.
        ++ move => [H5 H6].
           have H7: size st' > 0 by rewrite H4.
           have H8: head y (rcons st' u) \in st' by apply head_in. 
           pose proof Lxx3 H8 H6 as H9.
           rewrite last_rcons. 
           by right;apply t_trans with (head y (rcons st' u));[ apply t_step|].
    - pose proof in_non0 H1 as H2.
      pose proof seq_rc H2 as [st' [u ->]].
      rewrite last_rcons.
      move: H1;rewrite in_rcons => /orP [H1 | /eqP H1].
      by rewrite Lift_crc allset_cons => [[H3 H4]];pose proof Lxx3 H1 H4;right.
      by move => H3;left.
  Qed.
  
  Lemma Lyy: forall (st st': seq T) (v0 vn vnp1 t:T),
      (t \in v0 :: st) -> (t \in rcons st' vnp1) ->
      (v0 :: rcons st vn) [L\in] R 
      ->  (vn :: rcons st' vnp1) [L\in] R
      -> R.+ (vn, last v0 st).
  Proof.
    move => st st' v0 vn vnp1 t H1 H2 H3 H4. 
    pose proof Lxx8 H2 H4 as H5. 
    case H21: (size st).
    + move: H21 => /size0nil H21.
      by move: H1; rewrite H21 mem_seq1 /= => /eqP <-.
    + have H23: size st > 0 by rewrite H21.
      pose proof seq_rc H23 as [st1 [zz H24]].
      pose proof Lxx9 H1 H3 as [H22 | H22];
        rewrite H24 /= last_rcons in H22 *.
      by rewrite last_rcons -H22. 
      by rewrite last_rcons;apply t_trans with t.
  Qed.
  
End Seq1_plus. 


Section allL_uniq.
  (** * The aim of this section is to prove allL_uniq *)

  Variables (T:eqType) (R: relation T).
  
  Lemma allL_drop: forall (st:seq T) (x y z:T),
      z \in st -> allL R st x y -> allL R (drop ((index z st).+1) st) z y.
  Proof.
    elim => [x y z H1 H2 // | t st Hr x y z H1 H2].
    case H3: (t == z). 
    + rewrite /drop //= H3 -/drop drop0.
      move: H3 => /eqP H3.
      by move: H2;rewrite H3 allL_c => /andP [_ H2'].
    + rewrite /drop //= H3 -/drop.
      apply Hr with t.
      - move: H1; rewrite in_cons => /orP [/eqP H1| H1].
        by move: H3; rewrite H1 => /eqP H3.
        by [].
      - by move: H2; rewrite allL_c => /andP [_ H2]. 
  Qed.
  
  Lemma drop_cons': forall (st: seq T) (x:T),
      x \in st -> x::(drop (index x st).+1 st) = (drop (index x st) st).
  Proof.
    elim => [// | y st Hr x H1].
    case H2: (y == x);
      first by move: H2 => /eqP ->; rewrite /= eq_refl drop0.
    rewrite /drop /= H2 -/drop.
    move: H1 H2; rewrite in_cons => /orP [/eqP -> H2 | H1 _].
    by rewrite eq_refl in H2. 
    by pose proof (Hr x) H1. 
  Qed.
  
  Lemma allL_uniq_tail: forall (U: relation T) (st: seq T) (x y: T),
      allL U st x y -> exists st', subseq st' st /\  ~( y \in st') /\ allL U st' x y.
  Proof.
    move => U.
    elim => [// x y H1 | a st H1 x y]; first by (exists [::]).
    case H2: (y == a).
    + move: (H2) => /eqP H2'.
      rewrite allL_c -H2' => /andP [H3 _].
      by (exists [::]); rewrite allL0.
    + rewrite allL_c => /andP [H3 /H1 [st' [ H4 [H5 H6]]]].
      exists [::a & st'].
      split. 
      by rewrite -cat1s -[a::st]cat1s; rewrite subseq_cat2l.
      rewrite in_cons H2 /=.
      split. 
      by [].
      by rewrite allL_c H3 H6.
  Qed.
  
  Lemma allL_uniq_head: forall (st: seq T) (x y: T),
      allL R st x y -> exists st', subseq st' st /\ ~( x \in st') /\ allL R st' x y.
  Proof.
    move => st x y; rewrite allL_rev => H1.
    pose proof allL_uniq_tail H1 as [st' H2].
    move: H2; rewrite  allL_rev inverse_inverse => [[H2 [H3 H4]]].
    exists (rev st');split. 
    have H5: st = (rev (rev st)) by rewrite revK.
    by rewrite H5 subseq_rev.
    by rewrite in_rev revK. 
  Qed.

  Lemma allL_uniq_internals: forall (st: seq T) (x y: T),
      allL R st x y -> exists st', subseq st' st /\  @uniq T st' /\ allL R st' x y.
  Proof.
    elim => [// x y H1 | a st H1 x y]; first by (exists [::]).
    rewrite allL_c => /andP [H3 /H1 [st' [H4 [H5 H6]]]].
    case H2: (a \in st'); last first.
    + exists [::a&st'].
      split. 
      by rewrite -cat1s -[a::st]cat1s; rewrite subseq_cat2l.
      split.
      by rewrite /uniq -/uniq H2 H5.
      by rewrite allL_c H3 H6.
    + exists (drop (index a st') st').
      split.
      have H7: subseq (drop (index a st') st') st' by apply drop_subseq.
      have H8: subseq st' (a::st') by apply subseq_cons.
      have H9: subseq (drop (index a st') st') (a :: st')
        by apply subseq_trans with st'.
      have H10: subseq (a:: st') (a::st)
        by rewrite -cat1s -[a::st]cat1s; rewrite subseq_cat2l.      
      by apply  subseq_trans with [::a &st'].
      split.
      by apply drop_uniq.
      pose proof allL_drop H2 H6 as H7.
      have H8: a::(drop (index a st').+1 st') = (drop (index a st') st').
      apply drop_cons'.
      by [].
      by rewrite -H8 allL_c H3 H7.
  Qed.

  Lemma in_subseq_1: forall (st1 st2: seq T) (x:T),
      subseq [::x & st1] st2 -> x \in st2.
  Proof.
    elim => [st2 x | y st1 Hr st2 x H1]; first by rewrite sub1seq. 
    elim: st2 H1 Hr => [// H1 _ |  z st2 Hr' H1 H2].
    case H3: (x == z).
    - move: (H3) => /eqP <-.
      by rewrite in_cons //= eq_refl orbC orbT.
    - rewrite /subseq H3 -/subseq in H1.
      apply Hr' in H1.
      by rewrite in_cons H1 orbT.
      by [].
  Qed.
  
  Lemma in_subseq': forall (st2 st1: seq T) (x:T),
      subseq st1 st2 -> (x \in st1) -> (x \in st2).
  Proof.
    elim => [st1 x | y st1 Hr st2 x H1 H2].  
    by rewrite subseq0 => /eqP -> H2.
    elim: st2 H1 H2 Hr => [// |  z st2 Hr' H1 H2 H3].
    case H4: (z == y).
    - move: H1; rewrite /subseq H4 -/subseq => H1.
      move: (H4) => /eqP <-.
      rewrite in_cons. 
      move: H2; rewrite in_cons => /orP [H2 | H2].
      by rewrite H2 orbC orbT.
      by (have ->:  x \in st1 by apply H3 with st2); rewrite orbT.
    - move: H1; rewrite /subseq H4 -/subseq => H1.
      move: H2; rewrite in_cons => /orP [/eqP H2 | H2].
      apply in_subseq_1 in H1.
      by rewrite in_cons H2 H1 orbT.
      apply cons_subseq in H1. 
      have H5: x \in st1. by apply: (H3 st2 x).
      by rewrite in_cons H5 orbT. 
  Qed.

  Lemma in_subseq: forall (st1 st2: seq T) (x:T),
      subseq st1 st2 -> ~ (x \in st2) -> ~ (x \in st1).
  Proof.
    move => st1 st2 x H1.
    apply contraPP.
    move => /contrapT H2 H3.
    have H4:  x \in st2. by apply in_subseq' with st1.  
    by [].
  Qed.
  
  Lemma allL_uniq: forall (st: seq T) (x y: T),
      allL R st x y -> exists st', subseq st' st /\ ~( x \in st') /\  ~(y \in st') /\
                               @uniq T st' /\ allL R st' x y. 
  Proof.
    move => st x y H1.
    pose proof allL_uniq_tail H1 as [st2 [S2 [I2 H2]]].
    pose proof allL_uniq_head H2 as [st3 [S3 [I3 H3]]].
    have J3: ~ (y \in st3) by  apply in_subseq with st2.
    pose proof allL_uniq_internals H3 as [st4 [S4 [K4 H4]]].
    have J4: ~ (y \in st4) by apply in_subseq with st3.
    have I4: ~ (x \in st4) by apply in_subseq with st3.
    exists st4. 
    split.
    have HH1: subseq st4 st2 by apply subseq_trans with st3.
    have HH2: subseq st4 st by apply subseq_trans with st2.
    by [].
    by [].
  Qed.

  Lemma TCP_uniq: forall (x y:T), 
      R.+ (x,y)
      <-> exists st, ~( x \in st) /\ ~(y \in st) /\ @uniq T st /\ allL R st x y. 
  Proof.
    move => x y;split. 
    - rewrite TCP' /mkset => [[st H1]].
      apply allL_uniq in H1.
      by move: H1 => [st' [H1 [H2 [H3 [H4 /= H5]]]]];(exists st').
    - by move => [st [_ [_ [_ H1]]]];rewrite TCP' /mkset; exists st.
  Qed.
  
  Lemma TCP_uniq': forall (x y:T), 
      R.+ (x,y) 
      -> ~ ( R.+ (y,x))
      -> exists st, uniq (x::(rcons st y)) /\ (x::(rcons st y)) [L\in] R.
  Proof.
    move => x y H1 H2. 
    move: (H1) => /TCP_uniq [st [H3 [H4 [H5 H6]]]].
    have H7: ~ (x = y) by move => H7;rewrite H7 in H1 H2.
    have H8: uniq (rcons st y)
      by move: H4 => /negP H4;rewrite rcons_uniq H4 H5. 
    have H9: x \in (rcons st y) -> False
        by rewrite -[rcons st y]cats0 cat_rcons mem_cat mem_seq1
         => /orP [ H9 | /eqP H9].
    have H10: uniq (x :: rcons st y) by rewrite /uniq -/uniq;
      move: H9 => /negP H9;rewrite H8 andbT.

    by exists st.
  Qed.

End allL_uniq.

Section Hn.
  (** * prove that 
      (exists v0, v0 \in (@setT T))
      /\ (forall v, exists w, R.+ (v,w) /\ ~ (R.+ (w,v)))
      gives the existence of an infinite outward R-path 
   *)
  
  Variables (T:eqType) (R: relation T).
  
  Lemma RedBack: forall (st:seq T) (x y:T),
      (x::(rcons st y)) [L\in] R 
      -> ~ ( R.+ (y,x))
      -> exists st', exists y',
          subseq (rcons st' y') (rcons st y) /\ st' [\in] R.+#_(x) 
          /\ (x::(rcons st' y')) [L\in] R /\ ~ (R.+ (y',x)).
  Proof.
    have H0: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim.
    elim/last_ind => [x y H1 H2| st z Hr x y H1 H2];first by (exists [::]; exists y).
    case H3: ((z,x) \in R.+).
    - exists (rcons st z); exists y.
      have H4: (rcons st z) [\in] R.+#_(x).
      move: H1; rewrite Lift_crc Lift_rcrc allset_cons allset_rcons => [[_ [H1 _]]].
      rewrite allset_rcons.
      split. 
      apply Lift_in_FF with z. by [].
      by rewrite inP -Fset_t0 -inP H3.
      by rewrite -Fset_t0 -inP H3.
      (* end of H4 *)
      by [].
      
    - rewrite Lift_crc Lift_rcrc allset_cons allset_rcons in H1.
      move: (H1); rewrite H0 => [[H10 [H10' H10'']]].
      have H5: (x :: rcons st z) [L\in] R by rewrite Lift_crc allset_cons.
      apply Hr in H5; last by move => /inP H6; rewrite H6 in H3.
      move: H5 => [st' [y' [H5 [H6 [H7 H8]]]]].
      have H9: subseq (rcons st' y') (rcons (rcons st z) y) 
        by apply subseq_trans with (rcons st z);[ | apply subseq_rcons].
      by (exists st', y').
  Qed.
  
  Lemma RedBack': forall (st:seq T) (x y:T),
      (x::(rcons st y)) [L\in] R 
      -> uniq (x::(rcons st y))
      -> ~ ( R.+ (y,x))
      -> exists st', exists y',
          uniq (x::(rcons st' y')) /\ st' [\in] R.+#_(x) /\ (x::(rcons st' y')) [L\in] R /\ ~ (R.+ (y',x)).
  Proof.
    move => st x y H1 H2 H3.
    pose proof  RedBack H1 H3 as [st' [y' [H4 [H5 [H6 H7]]]]].
    exists st';exists y'.
    have H8: uniq (x :: rcons st' y') by apply uniq_subseq with (rcons st y).
    by [].
  Qed.
  
  Lemma RedBack'': forall (st:seq T) (x y:T),
      (x::(rcons st y)) [L\in] R 
      -> uniq (x::(rcons st y))
      -> ~ ( R.+ (y,x))
      -> exists st', exists y',
          st' [\in] R.+#_(x) /\ uniq (x::(rcons st' y')) /\ (x::(rcons st' y')) [L\in] R /\ ~ (R.+ (y',(last x st'))).
  Proof.
    move => st x y H1 H2 H3.
    pose proof  RedBack' H1 H2 H3 as [st' [y' [H4 [H5 [H6 H7]]]]].
    exists st';exists y'.
    have H8: size st' > 0 -> ~ R.+ (y', last x st').
    move => H9 H10. 
    pose proof seq_c H9 as [s' [x' H11]].
    have H12: (last x st') \in st' by rewrite H11 /=; apply mem_last.
    have H13: (last x st') \in  R.+#_(x) by apply allset_in with st'. 
    have H14: R.+ (y',x) 
      by apply t_trans with (last x st');[ | move: H13; rewrite inP -Fset_t0 /=].
    by [].
    have H9: size(st') = 0 -> ~ R.+ (y', last x st') by move => /size0nil ->.
    have H10:  ~ R.+ (y', last x st')
      by case H11: (size st');[apply H9 | apply H8;rewrite H11].
    
    by [].
  Qed.

  Lemma RedBackF: forall (x y:T),
      R.+ (x,y) -> ~ ( R.+ (y,x))
      -> exists st', exists y',
          st' [\in] R.+#_(x) /\ uniq (x::(rcons st' y')) /\ (x::(rcons st' y')) [L\in] R /\ ~ (R.+ (y',(last x st'))).
  Proof.
    move => x y H1 H2.
    pose proof TCP_uniq' H1 H2 as [st [H3 H4]]. 
    pose proof RedBack'' H4 H3 H2 as [st' [y' [H6 [H7 [H8 H9]]]]].
    by exists st', y'.
  Qed.
  
  Definition H (n: nat) :=
    exists (st: seq T), exists (x y:T), size(x::(rcons st y)) > n
                              /\ uniq((x::(rcons st y)))  
                              /\ (x::(rcons st y)) [L\in] R
                              /\ ~ (R.+ (y, (last x st))).
  
  Lemma Infinite_R_path0: forall (n: nat),
      (exists v0, v0 \in (@setT T))
      -> (forall v, exists w, R.+ (v,w) /\ ~ (R.+ (w,v)))
      -> H n -> H n.+1.
  Proof.
    elim. 
    - move => [v0 _] H2 _. 
      pose proof H2 v0 as [v1 [H7 H8]].
      pose proof RedBackF H7 H8 as [st [v1' [_ H10]]].
      by exists st, v0, v1';split;[rewrite -rcons_cons size_rcons| exact].
    - move => n Hr H1 H2 [st [v0 [vn [H3 [H4' [H5' H6']]]]]].
      pose proof H2 vn as [vnp [H4 H5]].
      pose proof RedBackF H4 H5 as [st' [vnp1 [H8 [H9 [H10 H11]]]]].
      exists ((rcons st vn) ++ st'), v0, vnp1.
      
      have H12: n.+2 < size (v0 :: rcons (rcons st vn ++ st') vnp1)
        by rewrite rcons_cat -cat_cons size_cat size_rcons -addn1;apply leq_add.
      
      have H13: (v0 :: rcons (rcons st vn ++ st') vnp1) [L\in] R
        by rewrite rcons_cat Lift_cat_crc allset_cat.

      have H14:  ~ R.+ (vnp1, last v0 (rcons st vn ++ st'))
        by rewrite last_cat last_rcons.
      
      have H15: uniq (rcons st' vnp1)
        by (have H15': subseq (rcons st' vnp1) (vn::(rcons st' vnp1))
             by apply subseq_cons;
            have H15'': uniq (rcons st' vnp1));
        pose proof subseq_uniq H15' H9.
      
      have H17: forall t, (t \in [::v0 & st]) -> (t \in (rcons st' vnp1))
                     -> R.+ (vn, last v0 st)
          by move => t H18 H19; pose proof Lyy H18 H19 H5' H10.
      
      move: (H9);rewrite cons_uniq => /andP [_ H9'].
      
      have H20: has (in_mem^~ (mem (v0 :: rcons st vn))) (rcons st' vnp1) -> False.
      move => /hasP [t H21 H22]. 
      move: H22;rewrite -rcons_cons in_rcons => /orP [H22 | /eqP H22].
      by pose proof (H17 t) H22 H21 as H23.
      rewrite H22 in H21; move: H9; rewrite /uniq => /andP [H9 _].
      by rewrite H21 in H9.
      move: H20 => /negP H20.
      
      have H23: uniq (v0 :: rcons (rcons st vn ++ st') vnp1)
        by rewrite rcons_cat -cat_cons cat_uniq H4' H9' andbC 2!andbT.
      
      by [].
  Qed.
    
  Lemma XX: forall v : T,
    (exists w : T, R.+ (v, w) /\ ~ R.+ (w, v)) = ~ ~ (exists w : T, R.+ (v, w) /\ ~ R.+ (w, v)) .
  Proof.
    move => v; by rewrite notE.
  Qed.
  
  Definition P (x:T):= exists w, R.+ (x,w) /\ ~ (R.+ (w,x)).
  Definition Q (x:T):= forall w, not (R.+ (x,w) /\ ~ (R.+ (w,x))).
  Definition Q1 (x:T):= forall w, R.+ (x,w) -> R.+ (w,x).

  Lemma PQ: forall (x:T), P x <-> not (Q x).
  Proof.
    move => x;rewrite /P /Q; by rewrite not_existsP.
  Qed.

  Lemma PQ1: forall (x:T), P x <-> not (Q1 x).
  Proof.
    move => x;rewrite /P /Q1; rewrite not_existsP.
    split. 
    apply contraPP. rewrite !notE.
    by move => H1 x0 [/H1 H2 H3].
    apply contraPP. rewrite !notE.
    move => H1 w H2.
    specialize H1 with w.
    rewrite not_andP notE in H1.
    move: H1 => [H1 | H1].
    by [].
    by [].
  Qed.
  
  Lemma PQ2: (forall v, P(v)) <-> not (exists v, Q1(v)).
    split. 
    - move => H1.
      rewrite not_existsP notE.
      move => x.
      by rewrite -PQ1.
    - move => H1.
      rewrite not_existsP notE in H1.
      move => v.
      by rewrite PQ1.
  Qed.

  Lemma PQ3: (exists v, Q1(v)) <-> not (forall v, P(v)).
    split. 
    - move => [v H1] H2.
      by have H3: not (Q1 v) by apply PQ1.
    - rewrite not_existsP.
      apply contraPP. rewrite 2!notE.
      move => H1 v.
      by rewrite PQ1.
  Qed.
  
  Lemma Hyp: 
    (exists v, forall w,  R.+ (v,w) -> R.+ (w,v))
    <-> ~ (forall v, exists w, R.+ (v,w) /\ ~ (R.+ (w,v))).
  Proof.
    apply PQ3.
  Qed.
      
End Hn.

Section Paper.

  Variables (T:eqType) (Eb Er: relation T).

  (* Three relations *) 
  Definition Bpath := [set xy | Eb.+ (xy.1, xy.2) \/ Eb.+ (xy.2,xy.1)].
  Definition Rpath := [set xy | Er.+ (xy.1, xy.2) \/ Er.+ (xy.2,xy.1)].
  Definition Mpath := [set xy | Bpath (xy.1, xy.2) \/ Rpath (xy.1, xy.2)].

  (* Inclusions *)
  Lemma BIM: Bpath `<=` Mpath.
  Proof. 
    by move => [x y];rewrite /Mpath /Bpath /mkset /= => ?; left.
  Qed.

  Lemma EbpIM: Eb.+ `<=` Mpath.
  Proof.
    have H1: Eb.+ `<=` Bpath 
      by move => [x y]; rewrite /Bpath /mkset /= => ?;left.
    by apply subset_trans with Bpath;[ | apply: BIM].
  Qed.
  
  Lemma RIM: Rpath `<=` Mpath.
  Proof. 
    by move => [x y];rewrite /Mpath /Bpath /mkset /= => ?; right.
  Qed.

  Lemma ErpIM: Er.+ `<=` Mpath.
  Proof.
    have H1: Er.+ `<=` Rpath 
      by move => [x y]; rewrite /Rpath /mkset /= => ?;left.
    by apply subset_trans with Rpath;[ | apply: RIM].
  Qed.
    
  Lemma SR: forall (S: set T) (R: relation T),
      ((S`*`S) `&` R) = [set z| z.1 \in S /\ z.2 \in S /\  R z].
  Proof.
    move => S R; rewrite /setI /setM /mkset predeqE => [[x y]]. 
    by split => /= [ [[/inP ? /inP ?] ?] | [/inP ? [/inP ? H3]] ].
  Qed.
  
  (** * Independent sets : two equivalent definitions *)
  Definition RIndep (S: set T) (R: relation T):= (S`*`S) `&` R = set0.
  
  Definition RIndep' (S: set T) (R: relation T):=
    forall (x y:T),  x \in S -> y \in S -> R (x,y) -> False.

  Lemma RIndep_eq: forall (S: set T) (R: relation T), RIndep S R <-> RIndep' S R.
  Proof.
    move => S R. 
    split. 
    + rewrite /RIndep SR empty_notexists => H1.
      rewrite /RIndep' => x y H2 H3 H4.
      by apply H1;exists (x,y);rewrite inP /mkset /=.
    + rewrite /RIndep' => H1.
      rewrite /RIndep SR empty_notexists /mkset => [[[x y] H2]].
      move: H2; rewrite inP /= => [[H2 [H3 H4]]].
      by apply (H1 x y).
  Qed.
  
  Lemma RIndep_I: forall (R U: relation T) (S: set T),
      R `<=` U -> RIndep S U -> RIndep S R.
  Proof.
    move => R U S H1.
    rewrite 2!RIndep_eq /RIndep'.
    move => H2 x y H3 H4 H5.
    by apply (H2 x y);[ | | apply H1].
  Qed.
  
  (* Independent set 
   * forall (x,y) in S there does not exists a monochromatic path 
   * between x and y.
   *)

  Definition Independent (S: set T) := RIndep S Mpath. 
  
  Definition IndependentSets := [set S | Independent S ].
  
  Definition Independent' (S: set T):= RIndep' S Mpath.
  
  Definition IndependentSets' := [set S | Independent' S].
  
  Lemma Indep: Independent = Independent'.
  Proof.
    rewrite /Independent /setI /Independent' /mkset predeqE => S.
    by rewrite RIndep_eq.
  Qed.
  
  Lemma Indep_B: forall (S: set T),
      IndependentSets S -> RIndep S Eb.+.
  Proof.
    by move => S;rewrite /IndependentSets /Independent /mkset;apply RIndep_I;apply EbpIM.
  Qed.

  Lemma Indep_R: forall (S: set T), 
      IndependentSets S -> RIndep S Er.+. 
  Proof.
    by move => S;rewrite /IndependentSets /Independent /mkset;apply RIndep_I;apply ErpIM.
  Qed.

  (** * [Set<=]  Order relation on sets *)
  Definition leset (S R: set T):= 
    forall (s:T), s \in S -> exists r, r \in R /\ ( s = r \/
                                      ((Eb.+ (s,r) /\ ~(Eb.+ (r,s))))).

  Definition leSet := [set SR | (leset SR.1 SR.2)].
  
  Notation "S [Set<=] R" := (leSet (S,R)).
  
  Lemma Ile: forall (R S: set T), R `<=`S -> R [Set<=] S.
    move => R S H1 /= => [s /inP/H1 H2].
    by exists s; split;[ rewrite inP | left].
  Qed.
  
  (** * [Set<=] is a partial order on IndependentSets  *)

  Lemma le_trans: transitive leSet.
  Proof.
    move => R S U /= => [H1 H2]. 
    move => r /= /H1 /= [s [H3 [-> | [H4 H5]]]].
    by move: H3 => /H2 /= [u [H4 [-> | [H5 H6]]]];(exists u);split;[| left| |right].
    move: H3 => /H2 /= [u [H6 [H7 | [H7 H8]]]].
    by (exists u);split;[|right;rewrite -H7].
    (exists u);split;first by []. 
    right;split. 
    by (have H9: (Eb.+ `;` Eb.+) (r,u) by (exists s));apply clos_tI.
    move => H9.
    have H10: (Eb.+ `;` Eb.+) (s,r) by (exists u).
    have H11: Eb.+ (s,r) by apply clos_tI.
    by [].
  Qed.
  
  Lemma le_refl: reflexive leSet.
  Proof.
    by move => R;rewrite /leset /mkset /= => r /= H1;exists r;split;[| left].
  Qed.

  Lemma le_antisym: forall R S, 
      (S \in IndependentSets) -> R [Set<=] S -> S  [Set<=] R -> S `<=` R.
  Proof.
    move => R S;rewrite inP /IndependentSets /leset /mkset /= => [H1 H2 H3 s H4].
    move: (H4) => /inP /H3 /= [r [/inP H5 [-> // | [H6 H7]]]]. 
    move: (H5) => /inP /H2 /= [s' [/inP H8 H9]].
    pose proof Indep_B H1 as H10.
    rewrite RIndep_eq /RIndep' in H10.
    have H11: Eb.+ (s, s') -> False by apply H10;rewrite inP.
    move: H9 => [H9 | [H9 H12]]; first by rewrite H9 in H6.
    have H13: (Eb.+ `;` Eb.+) (s,s') by (exists r).
    by have H14: Eb.+ (s,s') by apply clos_tI.
  Qed.
  
  (** * The {\cal S} set *) 

  Definition ScalP (S: set T) := 
    forall s, s \in S -> exists t, Er.+ (s,t) -> exists s', s' \in S /\ Mpath (t,s').

  Definition ScalP' (S: set T) := 
    forall t, t \in (Aset Er.+ S) -> ~( S `&` Mpath#_(t) = set0).
  
  (* L'ensemble S caligraphique du papier *)
  Definition Scal := [ set S | Independent S /\ ScalP S /\  ~ (S = set0) ].

  Lemma ScalInIndependent: Scal `<=` Independent. 
  Proof.
    by rewrite /Scal /mkset => S [? _].
  Qed.
  
  Section Scal_not_empty. 
    
    (** * Il faut ici montrer que Scal contient au moins un ensemble de la forme {v} *)
    
    Hypothesis A1: (exists (v0:T), (v0 \in setT)).

    Definition Infinite_red_outward:=
      forall (n: nat), exists s, uniq(s) /\ s [L\in] Er /\ size s = n.+2.

    Definition S0:=
      [set v | ~(exists w, Er (v,w)) \/ (forall w, Er (v,w) -> v \in (Aset Er.+ [set w]))].
    
    Hypothesis A2: ~ (S0 = set0). 

    (** L1 is the proof that we have Infinite_red_outward 
     * under a stronger assumption 
     * the correct assumtion is studied below 
     *) 
    Lemma L1: 
      (forall (v:T), (exists w, Er (v,w) /\ ~ (v \in (Aset Er.+ [set w]))))
      -> forall (n: nat), exists s, uniq(s) /\ s [L\in] Er /\ size s = n.+2.
    Proof.
      move => H2.
      move: A1 => [v0 _].
      elim. 
      - pose proof (H2 v0) as [v1 [H3 H4]].
        have H5: (rcons [::v0] v1) [L\in] Er by rewrite /= /Lift /all andbT inP. 
        have H6: v0 \in (rcons [::v0] v1) by rewrite /= mem_seq2 /= eq_refl orbC orbT. 
        have H7: v0 = v1 -> False.
        move => H8;rewrite H8 in H3 H4 H5 H6.
        by pose proof Lxx10 H6 H5 H3.
        exists [::v0;v1];split; last by [].
        rewrite /uniq /= andbT.
        case H8: (v0 == v1); first by move: H8 => /eqP H8.
        by rewrite mem_seq1;move: H8 => /eqP/eqP H8.
      - move => n [s [H1 [H3 H4]]].
        have [s' [vn H5]]:  exists (s':seq T) (x:T), s = (rcons s' x)
            by apply seq_rc;rewrite H4. 
        pose proof (H2 vn) as [vnp1 [H6 H7]].
        have H8: (rcons s vnp1) [L\in] Er by rewrite H5 Lift_rcrc allset_rcons -H5.
        have H9: size (rcons s vnp1) = n.+3  by rewrite size_rcons H4.
        have H10: (rcons s' vn) [L\in] Er by rewrite H5 in H3.
        have H11: vnp1 \in s -> vn \in Aset Er.+ [set vnp1]
              by rewrite H5 => H12;pose proof Lxx10 H12 H10 H6 as H13.
        have /negP H12:  vnp1 \in s -> False by move => /H11 H13.
        exists (rcons s vnp1).
        by rewrite rcons_uniq H1 andbT.
    Qed.
    
  End  Scal_not_empty.
  
  (* On veut montrer que Scal a un element maximal *)
  
  (* Les chaines dans Scal *)
  Definition Chains := [set C | 
                         C `<=` Scal /\ ~ (C = set0) 
                         /\ (forall (c1 c2: set T), c1 \in C -> c2 \in C -> c1 [Set<=] c2 \/ c2 [Set<=] c1)].

  Lemma Chains_in_Scal: 
    forall (C: set (set T)) (S: set T), (C \in Chains) -> (S \in C) -> S \in Scal. 
  Proof. 
    move => C S H1 /inP H2.
    have H3: C `<=` Scal by move: H1; rewrite inP /Chains /mkset => [[? _]].
    apply H3 in H2.
    by rewrite inP.
  Qed.
  
  (* L'ensemble Sinf associé a une chaine *)
  Definition Sinf (C: set (set T)) := 
    [ set v | exists (S: set T), S \in C /\ v \in S /\ (forall (T: set T), T \in C -> S [Set<=] T -> v \in T)].

  (* *)
  Lemma Test: forall (C: set (set T)) (S: set T) (s:T),
      (C \in Chains) -> (S \in C) -> (s \in S)
      -> ~ (s \in Sinf C) 
      -> exists (S1: set T), S1 \in C /\ S [Set<=] S1 /\ ~ (s \in S1).
  Proof.
  Admitted.
  
  Lemma Sinf_indep: forall (C: set (set T)), 
      (C \in Chains) -> (Sinf C) \in IndependentSets.
  Proof.
    move => C H1.
    rewrite inP /IndependentSets Indep /Independent' /mkset => [x y /inP H2 /inP H3 H4].
    move: H2; rewrite /Sinf /mkset => [[S [H5 [/= H6 H7]]]].
    move: H3; rewrite /Sinf /mkset => [[U [H5' [/= H6' H7']]]].
    move: H1; rewrite inP /Chains /mkset => [[H8 [H9 H10]]].

    have H15: C `<=` [set S| Independent S]
      by apply subset_trans with Scal;[ | apply ScalInIndependent].
    have H16: [set S| Independent S] U
      by rewrite inP in H5'; apply H15 in H5'.
    move: H16; rewrite Indep /mkset /Independent' /RIndep'=> H16.
    have H17: [set S| Independent S] S
      by rewrite inP in H5; apply H15 in H5.
    move: H17; rewrite Indep /mkset /Independent' /RIndep'=> H17.
    have [H11 | H11]: S [Set<=] U \/ U [Set<=] S by apply H10.
    + have H13: x \in U  by apply (H7 U).
      by apply (H16 x y).
    + have H13: y \in S  by apply (H7' S).
      by apply (H17 x y).
  Qed.
  
  Lemma Sinf_in_Scal: 
    forall (C: set (set T)) (s y:T),
      (C \in Chains) -> s\in (Sinf C) -> s \in (Eb.+)#_(y) -> y \in  (Sinf C).
  Proof.
    move => C s y H1 H2 H3.
    move: H2; rewrite inP /Sinf /mkset => [[S [H4 [H5 H6]]]].
    pose proof Chains_in_Scal H1 H4 as H7.
    
    move: H7; rewrite inP /Scal /mkset.
  Admitted.

End Paper.


