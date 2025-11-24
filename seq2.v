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
From mathcomp Require Import all_boot seq order boolp classical_sets. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".

From RL Require Import  seq1 rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section learn. 
  (** * just for me to keep in mind *) 
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
  
  Context (T:eqType).
  
  Implicit Types (R: relation T) (s sl sr: seq T) (x y z : T) (X : set T).

  Definition uniq_path s x y :=  (~ x \in s /\ ~ y \in s /\ uniq s).
  
  Lemma in_rcons s x y:  (x \in rcons s y) = (x \in s) || (x == y).
  Proof. by rewrite -cats1 mem_cat mem_seq1. Qed.
  
  Lemma last0' s x: ~ ( s = [::]) -> (last x s) \in s.
  Proof. elim/last_ind: s x => [// | s x' Hr x _ /=].
         by rewrite last_rcons in_rcons;apply/orP;right;apply:eq_refl.
  Qed.

  Lemma mem_last s x: last x s \in x :: s.
  Proof. by rewrite lastI mem_rcons mem_head. Qed.
 
  Lemma poo s: ~ ( s = [::]) <-> 0 < size s.
  Proof. 
    split. 
    by move: (leq0n (size s));rewrite leq_eqVlt eq_sym=> /orP [/nilP|? _].
    by move => + /nilP/eqP H1;rewrite H1. 
  Qed.
  
  Lemma poo1 s: ( s = [::]) <-> size s == 0.
  Proof. by split => [/nilP|/nilP]. Qed.

  Lemma head0 s x: ~ ( s = [::]) -> (head x s) \in s.
  Proof. by elim: s x => [//| x s _ ? _ /=];rewrite in_cons eq_refl. Qed.
   
  Lemma head_in s x y: size(s) > 0 -> head x (rcons s y) \in s.
  Proof.
    by elim: s x y => [x y //| z s Hr x y _ /=];rewrite in_cons eq_refl orbC orbT.
  Qed.
  
  Lemma in_non0 s x: x \in s -> size(s) > 0.
  Proof.
    by case H3: (size s);[apply size0nil in H3;rewrite H3 in_nil|].
  Qed.
  
  Lemma nth_dv s x y i: i < size s -> nth x s i = nth y s i.
  Proof.
    elim/last_ind: s x y i => [// | s z Hr x y i].
    rewrite size_rcons ltnS leq_eqVlt 2!nth_rcons => /orP [/eqP H1 | H1].
    by rewrite -H1 eq_refl ltnn.
    by rewrite H1; apply: Hr.
  Qed.
  
  Lemma last_dv s x y i: i < size s -> last x s = last y s.
  Proof.
    elim/last_ind: s x y i => [// | s z Hr x y i].
    by rewrite size_rcons ltnS leq_eqVlt 2!last_rcons => /orP [/eqP ?|?].
  Qed.
  
  Lemma allL_lastR R s x y z i: i < size s -> allL R s x y -> R (last z s, y).
  Proof.
    move => H1;rewrite allL_split => -[_ H2].
    by have <- : last x s = last z s by apply: last_dv;apply:H1. 
  Qed.
  
  Lemma allL_nth R s x y:
      allL R s x y -> forall i, i <= size s -> R (nth (last x s) s i, nth y s i.+1).
  Proof.
    elim/last_ind: s x y => [/= x y + i | s x0 Hr x y H1 i H2];
                    first by rewrite leqn0 allL0 => /inP H0 /eqP ->. 
    move: (H1);rewrite allL_rc => /andP [/inP H1' H3].
    move: H2;rewrite size_rcons leq_eqVlt => /orP [/eqP H2 | H2].
    + have H4: size (rcons s x0) = i by rewrite size_rcons -H2.
      rewrite -H4 nth_rcons nth_rcons /= H4 H2 // P6 P8 P9 P10.
      by move: H1;rewrite (@allL_split T R (rcons s x0) x y) => -[_ H1].
    + rewrite nth_rcons.
      case H4: (i == size s).
      ++ move: H4 => /eqP H4.
         have H5: i < size s = false by apply/negP;rewrite H4 ltnn.
         by rewrite H5 H4 nth_rcons P6 P8.
      ++ have H5: i < (size s) by apply: P5.
         rewrite H5 last_rcons nth_rcons.
         case H6: ( i.+1 < size s).
         +++ have <- : nth (last x s) s i = nth x0 s i by apply nth_dv.
             have -> :  nth y s i.+1 =  nth x0 s i.+1 by apply nth_dv.
             by apply: Hr. 
         +++ have H9: i.+1 = size s by pose proof @P7 (size s) i H5 H6.
             have H10: (i = (size s).-1)%N by pose proof @P11 (size s) i H5 H9.
             rewrite H9 H10 nth_last eq_refl.
             by pose proof (@allL_lastR R s x x0 x0 i H5 H3).
  Qed.
  
  Lemma allL_nth' R s x y:
      allL R s x y -> forall i, i < size s -> R (nth y s i, nth y s i.+1).
  Proof.
    move => H0 i H1.
    have H2:  i <= size s by rewrite leq_eqVlt H1 orbT. 
    pose proof (@allL_nth R s x y H0 i H2) as H3.
    by pose proof (@nth_dv s y (last x s) i H1) as ->.
  Qed.
  
  Lemma uniq_subseq s s' x: uniq (x :: s) -> subseq s' s -> uniq (x:: s').
  Proof.
    rewrite cons_uniq => /andP [H2 H3] H4.
    rewrite cons_uniq;move: (subseq_uniq H4 H3) => ->;rewrite andbT.
    move: H4 => /subseqP [m H4 H5].
    have /contra H6: x \in s' -> x \in s by rewrite H5;apply: mem_mask.
    by apply: H6.
  Qed.

  Lemma uniq_cat sl sr: 
      uniq(sl) -> uniq(sr) -> (forall x, x \in sl -> x \in sr -> False) 
      -> uniq(sl ++ sr).
  Proof.
    move => H1 H2 H3.
    rewrite cat_uniq H1 H2 andbT andTb; apply: negbT.
    have: has (in_mem^~ (mem sl)) sr -> False
      by move => /hasP [s H4 H5];pose proof (H3 s H5 H4).
    by apply: contra_notF.
  Qed.

  Lemma uniq_catE sl sr:
      uniq(sl ++ sr) <-> 
      uniq(sl) /\ uniq(sr) /\ (forall x, x \in sl -> x \in sr -> False).
  Proof.
    split;last by move => [H1 [H2 H3]];apply: (uniq_cat H1 H2 H3).
    rewrite cat_uniq => /andP [H0 /andP [/hasP H1 H2]].
    split;[exact | split;[exact|]] => s H3 H4.
    move: H1 => /not_exists2P/contrapT/(_ s)/not_andP H1.
    by have H5:  s \in sr /\ s \in sl by [].
  Qed.
  
  Lemma uniq_subseq' sr sl sl':
      uniq (sl ++ sr) -> subseq sl' sr -> uniq (sl ++ sl').
  Proof.
    move => /uniq_catE [H1 [H2 H3]] H4.
    rewrite uniq_catE.
    split;first exact;split;first by apply: (subseq_uniq H4 H2).
    move: H4 => /subseqP [m H4 H4'] s H5 H6.
    have H7: has [predI [in sl'] & [in sl]] sl'
      by apply/hasP;(exists s);[ | apply/andP].
    move: H7; rewrite [sl' in (has _ sl')]H4' => /has_mask/hasP [x H7 H8].
    move: H8 => /andP [_ H8].
    by pose proof (H3 x H8 H7).
  Qed.
  
  Lemma allset_in  s x X:  x \in s -> s [\in] X -> x \in X.
  Proof.
    elim: s x X => [ x X // | y s Hr x X ].
    rewrite in_cons allset_cons.
    move => /orP [/eqP -> | H1] [/inP H2 H3];[exact | by apply: Hr].
  Qed.
    
  Lemma in_rev s x: x \in s <-> x \in (rev s).
  Proof.
    have Impl: forall s', (x \in s') -> (x \in (rev s')).
    move => s1;elim: s1 x =>  [ x // | z s2 H1 x ].
    rewrite in_cons rev_cons -cats1 mem_cat => /orP [ /eqP H2 | H2].
    by rewrite -H2 mem_seq1;have /eqP -> : x = x by [];rewrite orbT.
    by apply H1 in H2;rewrite H2 orbC orbT.
    (* end Impl *)
    by split;[ apply Impl | move => /Impl H2; rewrite revK in H2].
  Qed.
 
  Lemma Lxx R s y z: y \in s -> (rcons s z) [L\in] R -> R.+ (y, z).
  Proof.
    move => H1 H2;move: (Lift_in_F H2) => H3. 
    by move: (allset_in H1 H3);rewrite inP Fset_t0.
  Qed.
  
  Lemma Lxx'' R s x y z: y \in (x::s) -> (x::(rcons s z)) [L\in] R -> R.+ (y, z).
  Proof.
    rewrite in_cons => /orP [/eqP -> H1| H1 H2].
    by move: (allL_to_clos_t H1).
    by move: (Lxx H1 (allL_Lift_in_rc H2)). 
  Qed.
  
  Lemma Lxx_head R s x y: y \in s -> (x::s) [L\in] R -> R.+ (x, y).
  Proof.
    move => H1 H2;move: (Lift_in_A H2) => H3. 
    by move: (allset_in H1 H3);rewrite inP /Aset -Fset_t0.
  Qed.
  
  Lemma Lxx_head' R s x y z: y \in (rcons s z) -> (x::(rcons s z)) [L\in] R -> R.+ (x, y).
  Proof.
    rewrite in_rcons => /orP [ H1 H2 | /eqP <-].
    by move: (Lxx_head H1 (allL_Lift_in_c H2)).     
    by apply:allL_to_clos_t.
  Qed.

  Lemma uniq_crc s x y: uniq (x::(rcons s y)) <-> uniq_path s x y /\ ~ (x = y).
  Proof.
    split => [ | [[H1 [H2 H3]] H4]].
    + by rewrite cons_uniq in_rcons rcons_uniq =>
        /andP [/orP/not_orP [H1 /negP/eqP  H3] /andP [/negP H4 H5]].
    + rewrite cons_uniq;apply/andP; split. 
      by rewrite in_rcons;apply/orP/not_orP;split;[| apply/negP/eqP].
      by rewrite rcons_uniq;apply/andP;split;[apply/negP |].
  Qed.
  
  Lemma nth_in_take s j y: j.+1 < size s -> nth y s j \in take j.+1 s.
  Proof.
    move => H1;move: (@nth_take j.+1 T y j (ltnSn j) s) => <-.
    by apply: mem_nth;rewrite size_take H1 ltnSn.
  Qed.
  
  Lemma nth_in_drop s i y: i < size s -> nth y s i \in drop i s.  
  Proof.
    move => H1.
    move: (@nth_drop i T y s 1);rewrite addn1 => ?.
    move: (@drop_nth T y i s H1) => H3.
    by rewrite H3 in_cons eq_refl orTb.
  Qed.

  Lemma nth_in_drop':  forall i (s: seq T) j y, i <= j -> j < size s  -> nth y s j \in drop i s.  
  Proof.
    elim => [s j y _ H1 // | ]. rewrite drop0. by apply: mem_nth.
    move => i Hr s j y H1 H2.
    rewrite -addn1 -drop_drop.    
    have H3:  nth y (drop 1 s) j.-1 \in drop i (drop 1 s).
    apply: Hr.
    by lia.
    rewrite size_drop. by lia.
    have H4: nth y (drop 1 s) j.-1 =  nth y s j. 

    move: (@nth_drop 1 T y s j.-1);rewrite add1n.
    have -> : j.-1.+1 = j by apply: ltn_predK H1. 
    by move => ->. 
    by rewrite -H4.
  Qed.
  
  Lemma uniq_nth s x y:
    uniq (x :: rcons s y) -> forall i, i < size s -> ~ (nth y s i = nth y s i.+1).
  Proof.
    have P11: forall n i, i < n -> i.+1 = n -> (i = n.-1)%N.
    move => n i H0 H1; pose proof (ltn_predK H0) as H2.
    by move: H1; rewrite -{1}H2 => /eqP H1; move: H1; rewrite eqSS => /eqP H1.
    rewrite uniq_crc => -[[H1 [H2 H3]] _] i H4 H5.
    case H6: (i == (size s).-1)%N.
    + move: H6 => /eqP H6.
      have H7: (size s).-1.+1 = (size s) by apply: (ltn_predK H4).
      have H8: nth y s (size s) = y by apply: nth_default.
      move: H5;rewrite H6 H7  nth_last H8 /= => H5.
      have: (last y s) \in s by apply: last0' => H10;rewrite H10 /= in H4. 
      by rewrite H5.
    + have H9: (i.+1 == size s) || (i.+1 < size s) by rewrite -leq_eqVlt.
      move: H9 => /orP [/eqP H9 | H9];
                 first by pose proof (P11 (size s) i H4 H9) as H0;rewrite -H0 eq_refl in H6.
      
      pose proof (cat_take_drop i.+1 s) as H10.
       
      have H11: nth y (take i.+1 s) i \in take i.+1 s
          by apply: mem_nth;rewrite size_take H9 ltnSn.

      pose proof (@nth_take i.+1 T y i (ltnSn i) s) as H11'.
      
      have H12:  nth y s i \in   take i.+1 s by rewrite -H11'. 

      pose proof (@nth_drop i T y s 1) as H13'.
      rewrite addn1 in H13'.
      
      have H13:  nth y (drop i s) 1 \in  drop i.+1 s
          by pose proof (@drop_nth T y i.+1 s H9) as ->;rewrite H13' in_cons eq_refl orTb.
      
      have H14: uniq(take i.+1 s ++ drop i.+1 s) by rewrite H10.
      
      have H15: (forall x, x \in take i.+1 s -> x \in drop i.+1 s -> False).
      by move: H14 => /uniq_catE [_ [_ H14]].

      have H16:  nth y s i \in drop i.+1 s by rewrite H5 -H13'.
      
      by move: H15 => /(_ (nth y s i) H12 H16) H15.
  Qed.
    
  Lemma uniq_nth'' s x y:
      uniq (x :: rcons s y) -> 
      forall i j, j < i -> i < size s -> ~ (nth y s j = nth y s i).
  Proof.
    rewrite uniq_crc => -[[H1 [H2 H3]] _] i j H4 H5 H6.
    
    have H7: uniq (take j.+1 s ++ drop j.+1 s)
      by move: H3;pose proof (cat_take_drop j.+1 s) as ->.
    have H8: j.+1 < (size s) by lia. 
    pose proof (@nth_in_take s j y H8) as H10.
    pose proof (@nth_in_drop' j.+1 s i y H4 H5) as H11.
    
    have H15: (forall x, x \in take j.+1 s -> x \in drop j.+1 s -> False)
      by move: H7 => /uniq_catE [_ [_ H14]].
    move: H15 => /(_ (nth y s j) H10);rewrite H6 H11 => H15.
    by apply: H15.
  Qed.
  
  Lemma uniq_nth' s x y:
      uniq (x :: rcons s y) -> 
      forall i, i < size s -> ~ (x = nth y s i) /\ ~ (y = nth y s i).
  Proof.
    move => /uniq_crc [[? [? _]] _] i H3.
    by pose proof mem_nth y H3 as H4;split;move => H5;rewrite -H5 in H4. 
  Qed.
  
End Seq1_plus. 

Section allL_uniq.
  (** * The aim of this section is to prove allL_uniq *)

  Variables (T:eqType) (R: relation T).

  Implicit Types x y z : T.
  Implicit Type s : seq T.
  
  Lemma allL_drop: forall s (x y z:T),
      z \in s -> allL R s x y -> allL R (drop ((index z s).+1) s) z y.
  Proof.
    elim => [x y z ? ? // | t s Hr x y z H1 H2].
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
 
  Lemma allL_take: forall s (x y z:T),
      z \in s -> allL R s x y -> allL R (take (index z s) s) x z.
  Proof.
    elim => [x y z ? ? // | t s Hr x y z H1 H2].
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
  
  Lemma allL_last: forall s (x y:T),
      allL R s x y ->  (rcons (belast x s) (last x s)) [L\in] R.
  Proof. by move => s x y /allL_split [+ _]; rewrite lastI. Qed.
  
  Lemma in_belast s x z: z \in s -> ~ (z = (last x s)) -> z \in (belast x s).
  Proof.
    move => H1 ?; have: z \in  x :: s by rewrite in_cons H1 orbT.
    by rewrite lastI in_rcons => /orP [ // | /eqP //].
  Qed.
  
  Lemma belast_head s x: ~(s = [::]) -> (belast x s) = x::(drop 1 (belast x s)).
  Proof.
    by elim/last_ind: s x => [x // | s y Hr x _];rewrite belast_rcons drop1 /behead.
  Qed.
  
  Lemma allL_belast: forall s (x z y:T),
      z \in s -> ~(z = x) -> ~ (z = (last x s)) -> allL R s x y
      -> R.+ (z, (last x s)).
  Proof.
    move => s x z y H1 H2 H3 H4;move: (in_belast H1 H3) => H5;move: (allL_last H4) => H6.
    have H7:  ~(s = [::]) by move => H8; rewrite H8 in H1.
    have H8:  (belast x s) = x::(drop 1 (belast x s)) 
      by apply: belast_head.
    move: H5; rewrite H8 in_cons => /orP [/eqP H9 // | H9].
    move: H6; rewrite H8 rcons_cons => H6.
    by pose proof (allL_to_clos_t (allL_drop H9 H6)).
  Qed.


  Lemma nth_in: forall x j s, j >= 0 -> j < size s -> nth x s j \in s.
  Proof.
    move => x j s. elim: s j => [// | y s Hr j H0 H1].
    case H2: (j == 0).
    + move: H2 => /eqP -> /=. by rewrite in_cons eq_refl orTb.
    + move: H2 => /neq0_lt0n H2.
      have H3: j.-1.+1 = j by apply: ltn_predK. 
      rewrite -H3 ltnS in H2.
      case H4: (j.-1 == size s). move: H4 => /eqP H4.
      rewrite -H3 H4. 
  Admitted.
  
  Lemma allL_belast': forall s (x z y:T),
      z \in s -> ~ (z = (last x s)) -> allL R s x y
      -> R.+ (z, (last x s)).
  Proof.
    move => s x z y H1 H2 H3.
    pose proof allL_drop H1 H3 as H4.
    have H5: last x s \in (drop (index z s).+1 s). admit. 
    pose proof allL_take H5 H4 as H6. 

    pose m := (size s).-1.
    pose p := (index z s).+1.
    have P1: last x s =  nth x s m. by rewrite -nth_last.
    have P3: nth x (drop p s) (m-p) = nth x s (p + (m-p)). by rewrite nth_drop.
    have P4: p + (m-p)= m. admit.
    have P5: last x s = nth x (drop p s) (m-p). by rewrite P3 P4 -nth_last.
    have P6: last x s \in (drop p s). rewrite P5.
    have P7: forall j, j >= 0 -> j < size s -> nth x s j \in s. 
    pose proof (allL_to_clos_t (allL_take H5 H4)).
  Admitted.
  
  
  Lemma in_behead: forall s (x z:T),
      z \in s -> ~ (z = (head x s)) -> z \in (behead s).
  Proof.
    elim => [x z // | y s Hr x z H1 /= H2].
    by move: H1; rewrite in_cons => /orP [/eqP H1 //| H1 //].
  Qed.

  Lemma behead_head: forall s (x:T),
    ~(s = [::]) ->  s = (head x s)::(behead s).
  Proof. by elim => [// | y s Hr x _ /=]. Qed.
    
  Lemma allL_behead: forall s (x z y:T),
      z \in s -> ~(z = y) -> ~ (z = (head y s)) -> allL R s x y
      -> R.+ ((head y s),z).
  Proof.
    move => s x z y H1 H2 H3 H4.
    move: (in_behead H1 H3) => H5.
    have H7: ~(s = [::]) by move => H8; rewrite H8 in H1.
    have H8: s = (head y s)::(behead s) by apply: behead_head;exact.
    move: H4; rewrite H8 allL_c => /andP [_ H4].
    by pose proof (allL_to_clos_t (allL_take H5 H4)).
  Qed.
  
  Lemma drop_cons': forall (s: seq T) (x:T),
      x \in s -> x::(drop (index x s).+1 s) = (drop (index x s) s).
  Proof.
    elim => [// | y s Hr x H1].
    case H2: (y == x);
      first by move: H2 => /eqP ->; rewrite /= eq_refl drop0.
    rewrite /drop /= H2 -/drop.
    move: H1 H2; rewrite in_cons => /orP [/eqP -> H2 | H1 _].
    by rewrite eq_refl in H2. 
    by pose proof (Hr x) H1. 
  Qed.
  
  Lemma drop_notin: forall (s: seq T) (x:T),
      x \in s -> uniq s -> x \notin (drop (index x s).+1 s).
  Proof.
    elim => [// | y s Hr x H1].
    case H2: (y == x);
      first by move: H2 => /eqP ->;rewrite /= eq_refl drop0 => /andP [H3 _].
    rewrite /drop /= H2 -/drop.
    move: H1 H2; rewrite in_cons => /orP [/eqP -> H2 | H1 _].
    by rewrite eq_refl in H2. 
    move => /andP [H2 H3]; by pose proof (Hr x) H1 H3. 
  Qed.
  
  Lemma allL_uniq_tail: forall (U: relation T) (s: seq T) (x y: T),
      allL U s x y -> exists s', subseq s' s /\  ~( y \in s') /\ allL U s' x y.
  Proof.
    move => U.
    elim => [// x y H1 | a s H1 x y]; first by (exists [::]).
    case H2: (y == a).
    + move: (H2) => /eqP H2'.
      rewrite allL_c -H2' => /andP [H3 _].
      by (exists [::]); rewrite allL0.
    + rewrite allL_c => /andP [H3 /H1 [s' [ H4 [H5 H6]]]].
      exists [::a & s'].
      split. 
      by rewrite -cat1s -[a::s]cat1s; rewrite subseq_cat2l.
      rewrite in_cons H2 /=.
      split. 
      by [].
      by rewrite allL_c H3 H6.
  Qed.
  
  Lemma allL_uniq_head: forall (s: seq T) (x y: T),
      allL R s x y -> exists s', subseq s' s /\ ~( x \in s') /\ allL R s' x y.
  Proof.
    move => s x y; rewrite allL_rev => H1.
    pose proof allL_uniq_tail H1 as [s' H2].
    move: H2; rewrite  allL_rev inverseK => [[H2 [H3 H4]]].
    exists (rev s');split. 
    have H5: s = (rev (rev s)) by rewrite revK.
    by rewrite H5 subseq_rev.
    by rewrite in_rev revK. 
  Qed.

  Lemma allL_uniq_internals: forall (s: seq T) (x y: T),
      allL R s x y -> exists s', subseq s' s /\  @uniq T s' /\ allL R s' x y.
  Proof.
    elim => [// x y H1 | a s H1 x y]; first by (exists [::]).
    rewrite allL_c => /andP [H3 /H1 [s' [H4 [H5 H6]]]].
    case H2: (a \in s'); last first.
    + exists [::a&s'].
      split. 
      by rewrite -cat1s -[a::s]cat1s; rewrite subseq_cat2l.
      split.
      by rewrite /uniq -/uniq H2 H5.
      by rewrite allL_c H3 H6.
    + exists (drop (index a s') s').
      split.
      have H7: subseq (drop (index a s') s') s' by apply drop_subseq.
      have H8: subseq s' (a::s') by apply subseq_cons.
      have H9: subseq (drop (index a s') s') (a :: s')
        by apply subseq_trans with s'.
      have H10: subseq (a:: s') (a::s)
        by rewrite -cat1s -[a::s]cat1s; rewrite subseq_cat2l.      
      by apply  subseq_trans with [::a &s'].
      split.
      by apply drop_uniq.
      pose proof allL_drop H2 H6 as H7.
      have H8: a::(drop (index a s').+1 s') = (drop (index a s') s').
      apply drop_cons'.
      by [].
      by rewrite -H8 allL_c H3 H7.
  Qed.
  
  Lemma in_subseq_1: forall (s2 s1: seq T) (x:T),
      subseq [::x & s1] s2 -> x \in s2.
  Proof.
    elim => [s x //| y s Hr s1 x H1].
    case H2: (x == y);first by rewrite in_cons H2 orTb.
    move: H1;rewrite /subseq H2 -/subseq => /Hr H1.
    by rewrite in_cons H1 orbT.
  Qed.

  Lemma in_subseq': forall (s2 s1: seq T) (x:T),
      subseq s1 s2 -> (x \in s1) -> (x \in s2).
  Proof.
    elim => [s1 x | y s1 Hr s2 x H1 H2].  
    by rewrite subseq0 => /eqP -> H2.
    elim: s2 H1 H2 Hr => [// |  z s2 Hr' H1 H2 H3].
    case H4: (z == y);move: H1; rewrite /subseq H4 -/subseq => H1.
    - move: (H4) => /eqP <-;rewrite in_cons. 
      move: H2; rewrite in_cons => /orP [H2 | H2].
      by rewrite H2 orbC orbT.
      by (have ->:  x \in s1 by apply H3 with s2); rewrite orbT.
    - move: H2; rewrite in_cons => /orP [/eqP H2 | H2].
      move: H1 => /in_subseq_1 H1.
      by rewrite in_cons H2 H1 orbT.
      apply cons_subseq in H1. 
      have H5: x \in s1 by apply: (H3 s2 x).
      by rewrite in_cons H5 orbT. 
  Qed.
  
  Lemma in_subseq: forall (s1 s2: seq T) (x:T),
      subseq s1 s2 -> ~ (x \in s2) -> ~ (x \in s1).
  Proof.
    move => s1 s2 x ?; apply contraPP => /contrapT ? ?.
    by have:  x \in s2 by apply in_subseq' with s1.  
  Qed.
  
  
  Lemma allL_uniq: forall (s: seq T) (x y: T),
      allL R s x y -> 
      exists s', subseq s' s /\ ~( x \in s') /\  ~(y \in s')
             /\  @uniq T s' /\ allL R s' x y. 
  Proof.
    move => s x y H1.
    pose proof allL_uniq_tail H1 as [s2 [S2 [I2 H2]]].
    pose proof allL_uniq_head H2 as [s3 [S3 [I3 H3]]].
    have J3: ~ (y \in s3) by  apply in_subseq with s2.
    pose proof allL_uniq_internals H3 as [s4 [S4 [K4 H4]]].
    have J4: ~ (y \in s4) by apply in_subseq with s3.
    have I4: ~ (x \in s4) by apply in_subseq with s3.
    by exists s4;pose proof (subseq_trans (subseq_trans S4 S3) S2).
  Qed.
  
  Lemma TCP_uniq: forall (x y:T), 
      R.+ (x,y) <-> exists s, uniq_path s x y /\ allL R s x y. 
  Proof.
    move => x y;split. 
    - rewrite TCP' /mkset => -[s /allL_uniq H1].
      by move: H1 => [s' [H1 [H2 [H3 [H4 /= H5]]]]];(exists s').
    - by move => [s [_ H1]]; move: H1;apply: allL_to_clos_t. 
  Qed.
  
  Lemma TCP_uniq'': forall (x y:T), 
      R.+ (x,y) /\ ~ (x = y) 
      <-> exists s, uniq (x::(rcons s y)) /\ (x::(rcons s y)) [L\in] R.
  Proof.
    move => x y.
    split => [[H1 H7] |].
    + move: (H1) => /TCP_uniq [s [[H3 [H4 H5]] H6]].
      by (exists s);rewrite uniq_crc.
    + by move => [s [/uniq_crc [_ H1] /(@allL_to_clos_t T)  H2]].
  Qed.
  
  Lemma TCP_uniq': forall (x y:T), 
      (Asym R.+)(x,y) 
      -> exists s, uniq (x::(rcons s y)) /\ (x::(rcons s y)) [L\in] R.
  Proof.
    move => x y /[dup] H0 [H1 H2]. 
    have H3: ~ (x = y) by move => H7;rewrite H7 in H1 H2.
    by rewrite -TCP_uniq''.
  Qed.

  Definition allLu (R: relation T) s x y :=
    (x::(rcons s y)) [L\in] R /\ uniq (x :: rcons s y).
  
  Lemma TCP_uniq1 (x y:T):
      (Asym R.+)(x,y) <-> (exists s, allLu R s x y) /\ ~ R.+ (y,x).
  Proof. split. 
    by move => /[dup] /TCP_uniq' [s [H1 H2]] [_ H4];split;[exists s;split |].
    by move => [[s [H1 H2]] H3];split;[apply: allL_to_clos_t; apply: H1|].
  Qed.

End allL_uniq.

