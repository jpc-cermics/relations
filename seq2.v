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

(******************************************************************************)
(* some extensions of seq1.v when the type is an eqType                       *)
(******************************************************************************)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect seq order boolp classical_sets. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".

From RL Require Import  seq1 ssrel rel.

(* Require Import ClassicalChoice. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section learn. 
  (** * to keep in mind *) 
  Variables (T:eqType) (R: relation T).

  (* negP: on reste dans Prop *)
  Lemma test0 (st:seq T) x: (x \in st ) = false <-> ~ (x \in st ).
  Proof. by split;[move => /negP ?|move => ?;apply/negP]. Qed.
  
  (* eqP: on passe de Prop <-> bool *)
  Lemma test1 (st:seq T) x: (x \in st ) = false <-> (x \in st ) == false.
  Proof. split;[by move => ->;rewrite eq_refl|by move => ?; apply/eqP]. Qed.

  (* negP: on reste dans Prop *)
  Lemma test2 (st:seq T): ( 0 \in [:: 1] ) = false.
  Proof. by apply/negP => ?. Qed.
  
  (* eqP: on passe dans Prop puis negP *)
  Lemma test3 (st:seq T): ( 0 \in [:: 1] ) == false.
  Proof. by apply/eqP/negP => ?. Qed.
  
  (* on reste dans les booleens *)
  Lemma test4 (st:seq T): ( 0 \in [:: 1] ) == false.
  Proof. by rewrite mem_seq1 eq_refl. Qed.
  
  (* x != y : boolean. *)
  Lemma test5 (x y: T) :
    x != y <-> (x == y) = false.
  Proof. by split;[move=> /negPf| move => ?;apply/negPf]. Qed.

  (* x <> y : Prop <-> ~ ( x = y) *)
  Lemma test6 (x y: T) :
    ~ (x = y) <-> x <> y.
  Proof. exact. Qed.

End learn.

Section nat_util. 

  (** * we can use lia with mathcomp thanks to zify *)
  Lemma P6 n: n.+1 < n = false. Proof. by lia. Qed.
  Lemma P8 n: (n.+1 == n) = false. Proof. by lia. Qed.
  Lemma P9 n: n.+2 < n = false. Proof. by lia. Qed.
  Lemma P10 n: n.+2 == n = false. Proof. by lia. Qed. 
  Lemma P4 n i: i.+1 < n.+1 -> i < n. Proof. by lia. Qed.
  Lemma P5 n i: i < n.+1 -> (i == n) = false -> i < n. Proof. by lia.  Qed.
  Lemma P7 n i: i < n -> (i.+1 < n) = false -> i.+1 = n. Proof. by lia. Qed.
  Lemma P11 n i: i < n -> i.+1 = n -> (i = n.-1)%N. Proof. by lia. Qed.
  
  Lemma P6': forall n, n.+1 < n = false.
      by move => n;apply/negP => H6;move: (leq_ltn_trans (leqnSn n) H6);
                               rewrite ltnn. 
  Qed.
  
  Lemma P8': forall n, (n.+1 == n) = false.
    by move => n;apply/negP => /eqP H0;move: (ltnSn n);rewrite -{1}H0 ltnn.
  Qed.
  
  Lemma P9': forall n, n.+2 < n = false.
  Proof. 
    by move => n;apply/negP => H9;move: (leq_ltn_trans (leqnSn n.+1) H9);
                             rewrite P6.
  Qed.
  
  Lemma P10': forall n, n.+2 == n = false.
  Proof.
    by move => n;apply/negP  => /eqP H0;move: (ltnSn n.+1);
                              rewrite [X in n.+1 < X]H0 P6. 
  Qed.
  
  Lemma P4': forall n i, i.+1 < n.+1 -> i < n. 
  Proof. by move => n i; rewrite ltnS. Qed. 

  Lemma P5': forall n i, i < n.+1 -> (i == n) = false -> i < n.
  Proof. 
    by move => n i;rewrite leq_eqVlt eqSS => /orP [-> // | ? _];apply: P4.
  Qed.
  
  Lemma P7': forall n i, i < n -> (i.+1 < n) = false -> i.+1 = n.
  Proof.
    move => n i H1 /negP/negP H2; move: H2; rewrite -ltnNge => H2.
    case H3: (i.+1 == n);first by move: H3 =>/eqP H3.
    move: H2;rewrite ltnS leq_eqVlt ltnS => /orP [/eqP -> // | H2].
    by move: (leq_ltn_trans H2 H1);rewrite ltnn.
  Qed.
  
  Lemma P11': forall n i, i < n -> i.+1 = n -> (i = n.-1)%N.
  Proof.
    move => n i H0 H1; pose proof (ltn_predK H0) as H2.
    by move: H1; rewrite -{1}H2 => /eqP H1; move: H1; rewrite eqSS => /eqP H1.
  Qed.
  
End nat_util. 

Section Seq1_plus. 
  (** * extensions of results from seq1 and rel using eqType *)
  Variables (T:eqType) (R: relation T).

  Definition uniq_path (st: seq T) x y :=
    (~ x \in st /\ ~ y \in st /\ uniq st).
  
  Lemma in_rcons: forall (st:seq T) (x y:T), 
      (x \in rcons st y) = (x \in st) || (x == y).
  Proof. by move => st x y;rewrite -cats1 mem_cat mem_seq1. Qed.

  (** 
  Lemma last0: forall(st:seq T) t,
      ((last t st) \in st ) = false <-> st = [::].
  Proof.
    split; last by move => -> /=.
    elim: st t => [t // | t' st Hr t1 /=]. 
    rewrite in_cons => /orP;rewrite not_orE => -[+ H2].
    by have ->: st = [::] by apply/(Hr t')/negP.
  Qed.
  *)

  Lemma last0: forall(st:seq T) t,
      ~ ( st = [::]) -> (last t st) \in st.
  Proof. 
    by elim/last_ind => [//| st x _ ? _ /=]; 
                    rewrite last_rcons in_rcons eq_refl orbT.
  Qed.
  
  Lemma head0: forall(st:seq T) t,
      ~ ( st = [::]) -> (head t st) \in st.
  Proof. by elim => [//| x st _ ? _ /=];rewrite in_cons eq_refl. Qed.
  
  Lemma nth_dv: forall (st: seq T) x y i, i < size st -> nth x st i = nth y st i.
  Proof.
    elim/last_ind => [// | st z Hr x y i].
    rewrite size_rcons ltnS leq_eqVlt 2!nth_rcons => /orP [/eqP H1 | H1].
    by rewrite -H1 eq_refl ltnn.
    by rewrite H1; apply: Hr.
  Qed.

  (* XXX this is mem_nth *)
  Lemma nth_in: forall (st: seq T) x i, i < size st -> (nth x st i) \in st.
    Proof. by move => st x i; apply: mem_nth. Qed.
  
  Lemma last_dv: forall (st: seq T) x y i, i < size st -> last x st = last y st.
  Proof.
    elim/last_ind => [// | st z Hr x y i].
    by rewrite size_rcons ltnS leq_eqVlt 2!last_rcons => /orP [/eqP ?|?].
  Qed.
  
  Lemma allL_lastR: forall st x y z i, i < size st -> allL R st x y -> R (last z st, y).
  Proof.
    move => st x y z i H1;rewrite allL_split => -[_ H2].
    by have <- : last x st = last z st by apply: last_dv;apply:H1. 
  Qed.
  
  Lemma allL_nth : forall st x y, 
      allL R st x y -> forall i, i <= size st -> R (nth (last x st) st i, nth y st i.+1).
  Proof.
    elim/last_ind => [/= x y + i | st x0 Hr x y H1 i H2];
                    first by rewrite leqn0 allL0 => /inP H0 /eqP ->. 
    move: (H1);rewrite allL_rc => /andP [/inP H1' H3].
    move: H2;rewrite size_rcons leq_eqVlt => /orP [/eqP H2 | H2].
    + have H4: size (rcons st x0) = i by rewrite size_rcons -H2.
      rewrite -H4 nth_rcons nth_rcons /= H4 H2 // P6 P8 P9 P10.
      by move: H1;rewrite (@allL_split T R (rcons st x0) x y) => -[_ H1].
    + rewrite nth_rcons.
      case H4: (i == size st).
      ++ move: H4 => /eqP H4.
         have H5: i < size st = false by apply/negP;rewrite H4 ltnn.
         by rewrite H5 H4 nth_rcons P6 P8.
      ++ have H5: i < (size st) by apply: P5.
         rewrite H5 last_rcons nth_rcons.
         case H6: ( i.+1 < size st).
         +++ have <- : nth (last x st) st i = nth x0 st i by apply nth_dv.
             have -> :  nth y st i.+1 =  nth x0 st i.+1 by apply nth_dv.
             by apply: Hr. 
         +++ have H9: i.+1 = size st by pose proof @P7 (size st) i H5 H6.
             have H10: (i = (size st).-1)%N by pose proof @P11 (size st) i H5 H9.
             rewrite H9 H10 nth_last eq_refl.
             by pose proof (@allL_lastR st x x0 x0 i H5 H3).
  Qed.
  
  Lemma allL_nth' : forall st x y, 
      allL R st x y -> forall i, i < size st -> R (nth y st i, nth y st i.+1).
  Proof.
    move => st x y H0 i H1.
    have H2:  i <= size st by rewrite leq_eqVlt H1 orbT. 
    pose proof (@allL_nth st x y H0 i H2) as H3.
    by pose proof (@nth_dv st y (last x st) i H1) as ->.
  Qed.
  
  (** * utilities for uniq *)
  Lemma uniq_subseq: forall (st st': seq T) (x:T),
      uniq (x :: st) -> subseq st' st -> uniq (x:: st').
  Proof.
    move => st st' x; rewrite cons_uniq => /andP [H2 H3] H4.
    rewrite cons_uniq;move: (subseq_uniq H4 H3) => ->;rewrite andbT.
    move: H4 => /subseqP [m H4 H5].
    have /contra H6: x \in st' -> x \in st by rewrite H5;apply: mem_mask.
    by apply: H6.
  Qed.

  Lemma uniq_cat:  forall (stl str: seq T),
      uniq(stl) -> uniq(str) -> (forall s, s \in stl -> s \in str -> False) 
      -> uniq(stl ++ str).
  Proof.
    move => stl str H1 H2 H3.
    rewrite cat_uniq H1 H2 andbT andTb; apply: negbT.
    have: has (in_mem^~ (mem stl)) str -> False
      by move => /hasP [s H4 H5];pose proof (H3 s H5 H4).
    by apply: contra_notF.
  Qed.

  Lemma uniq_catE : forall (stl str: seq T),
      uniq(stl ++ str) <-> 
      uniq(stl) /\ uniq(str) /\ (forall s, s \in stl -> s \in str -> False).
  Proof.
    move => stl str.
    split;last by move => [H1 [H2 H3]];apply: (uniq_cat H1 H2 H3).
    rewrite cat_uniq => /andP [H0 /andP [/hasP H1 H2]].
    split;[exact | split;[exact|]] => s H3 H4.
    move: H1 => /not_exists2P/contrapT/(_ s)/not_andP H1.
    have H5:  s \in str /\ s \in stl by [].
    exact.
  Qed.
  
  Lemma uniq_subseq': forall (str stl stl': seq T),
      uniq (stl ++ str) -> subseq stl' str -> uniq (stl ++ stl').
  Proof.
    move => str stl stl' /uniq_catE [H1 [H2 H3]] H4.
    rewrite uniq_catE.
    split;first exact;split;first by apply: (subseq_uniq H4 H2).
    move: H4 => /subseqP [m H4 H4'] s H5 H6.
    have H7: has [predI [in stl'] & [in stl]] stl'
      by apply/hasP;(exists s);[ | apply/andP].
    move: H7; rewrite [stl' in (has _ stl')]H4' => /has_mask/hasP [x H7 H8].
    move: H8 => /andP [_ H8].
    by pose proof (H3 x H8 H7).
  Qed.
  
  (** * properties of \in for eqType *)
  
  Lemma allset_in: forall (st: seq T) (x:T) (X:set T),
      x \in st -> st [\in] X -> x \in X.
  Proof.
    elim => [ x X // | y st Hr x X ].
    rewrite in_cons allset_cons.
    move => /orP [/eqP -> | H1] [/inP H2 H3];[exact | by apply: Hr].
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
    have Impl: forall st, (x \in st) -> (x \in (rev st)).
    move => st;elim: st x =>  [ x // | z st' H1 x ].
    rewrite in_cons rev_cons -cats1 mem_cat => /orP [ /eqP H2 | H2].
    by rewrite -H2 mem_seq1;have /eqP -> : x = x by [];rewrite orbT.
    by apply H1 in H2;rewrite H2 orbC orbT.
    (* end Impl *)
    by split;[ apply Impl | move => /Impl H2; rewrite revK in H2].
  Qed.
  
  Lemma head_in: forall (st:seq T) (x y:T), size(st) > 0 -> head x (rcons st y) \in st.
  Proof.
    by elim => [x y //| z st Hr x y _ /=];rewrite in_cons eq_refl orbC orbT.
  Qed.
  
 
  Lemma Lxx: forall (st: seq T) (y z: T),
      y \in st -> (rcons st z) [L\in] R -> R.+ (y, z).
  Proof.
    move => st y z H1 H2;move: (Lift_in_F H2) => H3. 
    by move: (allset_in H1 H3);rewrite inP Fset_t0.
  Qed.
  
  Lemma Lxx'': forall (st: seq T) (x y z: T),
      y \in (x::st) -> (x::(rcons st z)) [L\in] R -> R.+ (y, z).
  Proof.
    move => st x y z;rewrite in_cons => /orP [/eqP -> H1| H1 H2].
    by move: (allL_to_clos_t H1).
    by move: (Lxx H1 (allL_Lift_in_rc H2)). 
  Qed.
  
  Lemma Lxx_head: forall (st: seq T) (x y: T),
      y \in st -> (x::st) [L\in] R -> R.+ (x, y).
  Proof.
    move => st y z H1 H2;move: (Lift_in_A H2) => H3. 
    by move: (allset_in H1 H3);rewrite inP /Aset -Fset_t0.
  Qed.
  
  Lemma Lxx_head': forall (st: seq T) (x y z: T),
      y \in (rcons st z) -> (x::(rcons st z)) [L\in] R -> R.+ (x, y).
  Proof.
    move => st x y z. rewrite in_rcons => /orP [ H1 H2 | /eqP <-].
    by move: (Lxx_head H1 (allL_Lift_in_c H2)).     
    by apply:allL_to_clos_t.
  Qed.

  Lemma uniq_crc: forall (st: seq T) x y,
      uniq (x::(rcons st y)) <-> uniq_path st x y /\ ~ (x = y).
  Proof.
    move => st x y;split => [ | [[H1 [H2 H3]] H4]].
    + by rewrite cons_uniq in_rcons rcons_uniq =>
        /andP [/orP/not_orP [H1 /negP/eqP  H3] /andP [/negP H4 H5]].
    + rewrite cons_uniq;apply/andP; split. 
      by rewrite in_rcons;apply/orP/not_orP;split;[| apply/negP/eqP].
      by rewrite rcons_uniq;apply/andP;split;[apply/negP |].
  Qed.
  
  Lemma nth_in_take: forall (st:seq T) j y, j.+1 < size st -> nth y st j \in take j.+1 st.
  Proof.
    move => st j y H1;move: (@nth_take j.+1 T y j (ltnSn j) st) => <-.
    by apply: mem_nth;rewrite size_take H1 ltnSn.
  Qed.
  
  Lemma nth_in_drop:  forall (st: seq T) i y, i < size st -> nth y st i \in drop i st.  
  Proof.
    move => st i y H1.
    move: (@nth_drop i T y st 1);rewrite addn1 => ?.
    move: (@drop_nth T y i st H1) => H3.
    by rewrite H3 in_cons eq_refl orTb.
  Qed.

  Lemma nth_in_drop':  forall i (st: seq T) j y, i <= j -> j < size st  -> nth y st j \in drop i st.  
  Proof.
    elim => [st j y _ H1 // | ]. rewrite drop0. by apply: mem_nth.
    move => i Hr st j y H1 H2.
    rewrite -addn1 -drop_drop.    
    have H3:  nth y (drop 1 st) j.-1 \in drop i (drop 1 st).
    apply: Hr.
    by lia.
    rewrite size_drop. by lia.
    have H4: nth y (drop 1 st) j.-1 =  nth y st j. 

    move: (@nth_drop 1 T y st j.-1);rewrite add1n.
    have -> : j.-1.+1 = j by apply: ltn_predK H1. 
    by move => ->. 
    by rewrite -H4.
  Qed.
  
  Lemma uniq_nth:  forall (st: seq T) x y, 
      uniq (x :: rcons st y) -> 
      forall i, i < size st -> ~ (nth y st i = nth y st i.+1).
  Proof.
    have P11: forall n i, i < n -> i.+1 = n -> (i = n.-1)%N.
    move => n i H0 H1; pose proof (ltn_predK H0) as H2.
    by move: H1; rewrite -{1}H2 => /eqP H1; move: H1; rewrite eqSS => /eqP H1.
    move => st x y;rewrite uniq_crc => -[[H1 [H2 H3]] _] i H4 H5.
    case H6: (i == (size st).-1)%N.
    + move: H6 => /eqP H6.
      have H7: (size st).-1.+1 = (size st) by apply: (ltn_predK H4).
      have H8: nth y st (size st) = y by apply: nth_default.
      move: H5;rewrite H6 H7  nth_last H8 /= => H5.
      have: (last y st) \in st by apply: last0 => H10;rewrite H10 /= in H4. 
      by rewrite H5.
    + have H9: (i.+1 == size st) || (i.+1 < size st) by rewrite -leq_eqVlt.
      move: H9 => /orP [/eqP H9 | H9];
                 first by pose proof (P11 (size st) i H4 H9) as H0;rewrite -H0 eq_refl in H6.
      
      pose proof (cat_take_drop i.+1 st) as H10.
       
      have H11: nth y (take i.+1 st) i \in take i.+1 st
          by apply: mem_nth;rewrite size_take H9 ltnSn.

      pose proof (@nth_take i.+1 T y i (ltnSn i) st) as H11'.
      
      have H12:  nth y st i \in   take i.+1 st by rewrite -H11'. 

      pose proof (@nth_drop i T y st 1) as H13'.
      rewrite addn1 in H13'.
      
      have H13:  nth y (drop i st) 1 \in  drop i.+1 st
          by pose proof (@drop_nth T y i.+1 st H9) as ->;rewrite H13' in_cons eq_refl orTb.
      
      have H14: uniq(take i.+1 st ++ drop i.+1 st) by rewrite H10.
      
      have H15: (forall s, s \in take i.+1 st -> s \in drop i.+1 st -> False).
      by move: H14 => /uniq_catE [_ [_ H14]].

      have H16:  nth y st i \in drop i.+1 st by rewrite H5 -H13'.
      
      by move: H15 => /(_ (nth y st i) H12 H16) H15.
  Qed.
    
  Lemma uniq_nth'':  forall (st: seq T) x y, 
      uniq (x :: rcons st y) -> 
      forall i j, j < i -> i < size st -> ~ (nth y st j = nth y st i).
  Proof.
    move => st x y;rewrite uniq_crc => -[[H1 [H2 H3]] _] i j H4 H5 H6.
    
    have H7: uniq (take j.+1 st ++ drop j.+1 st)
      by move: H3;pose proof (cat_take_drop j.+1 st) as ->.
    have H8: j.+1 < (size st) by lia. 
    pose proof (@nth_in_take st j y H8) as H10.
    pose proof (@nth_in_drop' j.+1 st i y H4 H5) as H11.
    
    have H15: (forall s, s \in take j.+1 st -> s \in drop j.+1 st -> False)
      by move: H7 => /uniq_catE [_ [_ H14]].
    move: H15 => /(_ (nth y st j) H10);rewrite H6 H11 => H15.
    by apply: H15.
  Qed.
  
  Lemma uniq_nth': forall (st: seq T) x y, 
      uniq (x :: rcons st y) -> 
      forall i, i < size st -> ~ (x = nth y st i) /\ ~ (y = nth y st i).
  Proof.
    move => st x y /uniq_crc [[H1 [H2 _]] _] i H3.
    by pose proof (@nth_in st y i H3) as H4;split;move => H5;rewrite -H5 in H4.
  Qed.
  
End Seq1_plus. 

Section allL_uniq.
  (** * The aim of this section is to prove allL_uniq *)

  Variables (T:eqType) (R: relation T).
  
  Lemma allL_drop: forall (st:seq T) (x y z:T),
      z \in st -> allL R st x y -> allL R (drop ((index z st).+1) st) z y.
  Proof.
    elim => [x y z ? ? // | t st Hr x y z H1 H2].
    case H3: (t == z). 
    + rewrite /drop //= H3 -/drop drop0.
      move: H3 => /eqP H3.
      by move: H2;rewrite H3 allL_c => /andP [_ H2'].
    + rewrite /drop //= H3 -/drop.
      apply Hr with t.
      ++ move: H1; rewrite in_cons => /orP [/eqP H1| H1 //].
         by move: H3; rewrite H1 => /eqP H3.
      ++ by move: H2; rewrite allL_c => /andP [_ H2]. 
  Qed.
 
  Lemma allL_take: forall (st:seq T) (x y z:T),
      z \in st -> allL R st x y -> allL R (take (index z st) st) x z.
  Proof.
    elim => [x y z ? ? // | t st Hr x y z H1 H2].
    case H3: (t == z). 
    + rewrite /take //= H3 -/take allL0.
      move: H3 => /eqP H3.
      by move: H2;rewrite allL_c H3 => /andP [H2 _].
    + rewrite /take //= H3 -/take.
      rewrite allL_c.
      move: H2; rewrite allL_c => /andP [H2 H2']; rewrite H2 andTb.
      move: H1; rewrite in_cons => /orP [/eqP H4 | H4].
      by move: H3; rewrite H4 => /eqP H3.
      by move: (Hr t y z H4 H2').
  Qed.
  
  
  Lemma allL_last: forall (st:seq T) (x y:T),
      allL R st x y ->  (rcons (belast x st) (last x st)) [L\in] R.
  Proof.
    elim/last_ind => [ // | st z _ x y H2].
    rewrite belast_rcons rcons_cons. 
    by move: H2; rewrite allL_rc last_rcons => /andP [_ H2].
  Qed.
  
  Lemma in_belast: forall (st:seq T) (x z:T),
      z \in st -> ~ (z = (last x st)) -> z \in (belast x st).
  Proof.
    elim/last_ind => [x z // | st y Hr x z H1 H2].
    move: H1; rewrite in_rcons => /orP [ H1 | /eqP H1].
    by rewrite belast_rcons in_cons H1 orbT.
    by move: H2; rewrite H1 last_rcons.
  Qed.
  
  Lemma belast_head: forall (st:seq T) x,
    ~(st = [::]) -> (belast x st) = x::(drop 1 (belast x st)).
  Proof.
    elim/last_ind => [x // | st y Hr x _].
    by rewrite belast_rcons drop1 /behead.
  Qed.
  
  Lemma allL_belast: forall (st:seq T) (x s y:T),
      s \in st -> ~(s = x) -> ~ (s = (last x st)) -> allL R st x y
      -> R.+ (s, (last x st)).
  Proof.
    move => st x s y H1 H2 H3 H4;move: (in_belast H1 H3) => H5;move: (allL_last H4) => H6.
    have H7:  ~(st = [::]) by move => H8; rewrite H8 in H1.
    have H8:  (belast x st) = x::(drop 1 (belast x st)) 
      by apply: belast_head.
    move: H5; rewrite H8 in_cons => /orP [/eqP H9 // | H9].
    move: H6; rewrite H8 rcons_cons => H6.
    by pose proof (allL_to_clos_t (allL_drop H9 H6)).
  Qed.

  Lemma in_behead: forall (st:seq T) (x z:T),
      z \in st -> ~ (z = (head x st)) -> z \in (behead st).
  Proof.
    elim => [x z // | y st Hr x z H1 /= H2].
    by move: H1; rewrite in_cons => /orP [/eqP H1 //| H1 //].
  Qed.

  Lemma behead_head: forall (st:seq T) (x:T),
    ~(st = [::]) ->  st = (head x st)::(behead st).
  Proof. by elim => [// | y st Hr x _ /=]. Qed.
    
  Lemma allL_behead: forall (st:seq T) (x s y:T),
      s \in st -> ~(s = y) -> ~ (s = (head y st)) -> allL R st x y
      -> R.+ ((head y st),s).
  Proof.
    move => st x s y H1 H2 H3 H4.
    move: (in_behead H1 H3) => H5.
    have H7: ~(st = [::]) by move => H8; rewrite H8 in H1.
    have H8: st = (head y st)::(behead st) by apply: behead_head;exact.
    move: H4; rewrite H8 allL_c => /andP [_ H4].
    by pose proof (allL_to_clos_t (allL_take H5 H4)).
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
  
  Lemma drop_notin: forall (st: seq T) (x:T),
      x \in st -> uniq st -> x \notin (drop (index x st).+1 st).
  Proof.
    elim => [// | y st Hr x H1].
    case H2: (y == x);
      first by move: H2 => /eqP ->;rewrite /= eq_refl drop0 => /andP [H3 _].
    rewrite /drop /= H2 -/drop.
    move: H1 H2; rewrite in_cons => /orP [/eqP -> H2 | H1 _].
    by rewrite eq_refl in H2. 
    move => /andP [H2 H3]; by pose proof (Hr x) H1 H3. 
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
  
  Lemma in_subseq_1: forall (st2 st1: seq T) (x:T),
      subseq [::x & st1] st2 -> x \in st2.
  Proof.
    elim => [st x //| y st Hr st1 x H1].
    case H2: (x == y);first by rewrite in_cons H2 orTb.
    move: H1;rewrite /subseq H2 -/subseq => /Hr H1.
    by rewrite in_cons H1 orbT.
  Qed.

  Lemma in_subseq': forall (st2 st1: seq T) (x:T),
      subseq st1 st2 -> (x \in st1) -> (x \in st2).
  Proof.
    elim => [st1 x | y st1 Hr st2 x H1 H2].  
    by rewrite subseq0 => /eqP -> H2.
    elim: st2 H1 H2 Hr => [// |  z st2 Hr' H1 H2 H3].
    case H4: (z == y);move: H1; rewrite /subseq H4 -/subseq => H1.
    - move: (H4) => /eqP <-;rewrite in_cons. 
      move: H2; rewrite in_cons => /orP [H2 | H2].
      by rewrite H2 orbC orbT.
      by (have ->:  x \in st1 by apply H3 with st2); rewrite orbT.
    - move: H2; rewrite in_cons => /orP [/eqP H2 | H2].
      move: H1 => /in_subseq_1 H1.
      by rewrite in_cons H2 H1 orbT.
      apply cons_subseq in H1. 
      have H5: x \in st1 by apply: (H3 st2 x).
      by rewrite in_cons H5 orbT. 
  Qed.
  
  Lemma in_subseq: forall (st1 st2: seq T) (x:T),
      subseq st1 st2 -> ~ (x \in st2) -> ~ (x \in st1).
  Proof.
    move => st1 st2 x ?; apply contraPP => /contrapT ? ?.
    by have:  x \in st2 by apply in_subseq' with st1.  
  Qed.
  
  
  Lemma allL_uniq: forall (st: seq T) (x y: T),
      allL R st x y -> 
      exists st', subseq st' st /\ ~( x \in st') /\  ~(y \in st')
             /\  @uniq T st' /\ allL R st' x y. 
  Proof.
    move => st x y H1.
    pose proof allL_uniq_tail H1 as [st2 [S2 [I2 H2]]].
    pose proof allL_uniq_head H2 as [st3 [S3 [I3 H3]]].
    have J3: ~ (y \in st3) by  apply in_subseq with st2.
    pose proof allL_uniq_internals H3 as [st4 [S4 [K4 H4]]].
    have J4: ~ (y \in st4) by apply in_subseq with st3.
    have I4: ~ (x \in st4) by apply in_subseq with st3.
    by exists st4;pose proof (subseq_trans (subseq_trans S4 S3) S2).
  Qed.
  
  Lemma TCP_uniq: forall (x y:T), 
      R.+ (x,y) <-> exists st, uniq_path st x y /\ allL R st x y. 
  Proof.
    move => x y;split. 
    - rewrite TCP' /mkset => -[st /allL_uniq H1].
      by move: H1 => [st' [H1 [H2 [H3 [H4 /= H5]]]]];(exists st').
    - by move => [st [_ H1]]; move: H1;apply: allL_to_clos_t. 
  Qed.
  
  Lemma TCP_uniq'': forall (x y:T), 
      R.+ (x,y) /\ ~ (x = y) 
      <-> exists st, uniq (x::(rcons st y)) /\ (x::(rcons st y)) [L\in] R.
  Proof.
    move => x y.
    split => [[H1 H7] |].
    + move: (H1) => /TCP_uniq [st [[H3 [H4 H5]] H6]].
      by (exists st);rewrite uniq_crc.
    + by move => [st [/uniq_crc [_ H1] /(@allL_to_clos_t T)  H2]].
  Qed.
  
  Lemma TCP_uniq': forall (x y:T), 
      (Asym R.+)(x,y) 
      -> exists st, uniq (x::(rcons st y)) /\ (x::(rcons st y)) [L\in] R.
  Proof.
    move => x y /[dup] H0 [H1 H2]. 
    have H3: ~ (x = y) by move => H7;rewrite H7 in H1 H2.
    by rewrite -TCP_uniq''.
  Qed.

  Definition allLu (R: relation T) st x y :=
    (x::(rcons st y)) [L\in] R /\ uniq (x :: rcons st y).
  
  Lemma TCP_uniq1 (x y:T):
      (Asym R.+)(x,y) <-> (exists st, allLu R st x y) /\ ~ R.+ (y,x).
  Proof. split. 
    by move => /[dup] /TCP_uniq' [st [H1 H2]] [_ H4];split;[exists st;split |].
    by move => [[st [H1 H2]] H3];split;[apply: allL_to_clos_t; apply: H1|].
  Qed.

End allL_uniq.

