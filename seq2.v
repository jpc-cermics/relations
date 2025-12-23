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
  
  Lemma P6' n : n.+1 < n = false.
  Proof. by apply/negP => H6;move: (leq_ltn_trans (leqnSn n) H6);rewrite ltnn. Qed.
  
  Lemma P8' n: (n.+1 == n) = false.
  Proof. by apply/negP => /eqP H0;move: (ltnSn n);rewrite -{1}H0 ltnn. Qed.
  
  Lemma P9' n: n.+2 < n = false.
  Proof. by apply/negP => H9;move: (leq_ltn_trans (leqnSn n.+1) H9);rewrite P6.
  Qed.
  
  Lemma P10' n: n.+2 == n = false.
  Proof. by elim: n . Qed.
  
  Lemma P4' n i: i.+1 < n.+1 -> i < n. 
  Proof. by rewrite ltnS. Qed. 

  Lemma P5' n i: i < n.+1 -> (i == n) = false -> i < n.
  Proof. by rewrite leq_eqVlt eqSS => /orP [-> // | ? _];apply: P4.
  Qed.
  
  Lemma P7' n i: i < n -> (i.+1 < n) = false -> i.+1 = n.
  Proof.
    move => H1 /negP/negP H2; move: H2; rewrite -ltnNge => H2.
    case H3: (i.+1 == n);first by move: H3 =>/eqP H3.
    move: H2;rewrite ltnS leq_eqVlt ltnS => /orP [/eqP -> // | H2].
    by move: (leq_ltn_trans H2 H1);rewrite ltnn.
  Qed.
  
  Lemma P11': forall n i, i < n -> i.+1 = n -> (i = n.-1).
  Proof.
    move => n i H0 H1; pose proof (ltn_predK H0) as H2.
    by move: H1; rewrite -{1}H2 => /eqP H1; move: H1; rewrite eqSS => /eqP H1.
  Qed.
  
End nat_util. 

Section Seq1_plus. 
  (** * extensions of results from seq1 and rel using eqType *)
  
  Context {T:eqType}.
  
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
 
  Lemma size0P s: ~ ( s = [::]) <-> 0 < size s.
  Proof. 
    split. 
    by move: (leq0n (size s));rewrite leq_eqVlt eq_sym=> /orP [/nilP|? _].
    by move => + /nilP/eqP H1;rewrite H1. 
  Qed.
  
  Lemma ZZpoo1 s: ( s = [::]) <-> size s == 0.
  Proof. by split => [/nilP|/nilP]. Qed.

  Lemma head0 s x: ~ ( s = [::]) -> (head x s) \in s.
  Proof. by elim: s x => [//| x s _ ? _ /=];rewrite in_cons eq_refl. Qed.
   
  Lemma head_in s x y: 0 < size(s) -> head x (rcons s y) \in s.
  Proof.
    by elim: s x y => [x y //| z s Hr x y _ /=];rewrite in_cons eq_refl orbC orbT.
  Qed.
  
  Lemma in_non0 s x: x \in s -> 0 < size(s).
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
  
  Lemma uniq_subseq s s' x: uniq (x :: s) -> subseq s' s -> uniq (x:: s').
  Proof.
    rewrite cons_uniq => /andP [H2 H3] H4.
    rewrite cons_uniq;move: (subseq_uniq H4 H3) => ->;rewrite andbT.
    move: H4 => /subseqP [m H4 H5].
    have /contra H6: x \in s' -> x \in s by rewrite H5;apply: mem_mask.
    by apply: H6.
  Qed.

  Lemma uniq_cat sl sr: 
      uniq(sl) -> uniq(sr) -> (forall x, x \in sl -> x \in sr -> False) -> uniq(sl ++ sr).
  Proof.
    move => H1 H2 H3.
    rewrite cat_uniq H1 H2 andbT andTb; apply: negbT.
    have: has (in_mem^~ (mem sl)) sr -> False
      by move => /hasP [s H4 H5];pose proof (H3 s H5 H4).
    by apply: contra_notF.
  Qed.

  Lemma uniq_catE sl sr:
      uniq(sl ++ sr) <-> uniq(sl) /\ uniq(sr) /\ (forall x, x \in sl -> x \in sr -> False).
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
  
  Lemma Lxx R s y z: z \in s -> (rcons s y) [L\in] R -> R.+ (z, y).
  Proof.
    by move => H1 /(@Lift_in_F T R) H2;move: (allset_in H1 H2) => /inP ?;rewrite Fset_t0.
  Qed.
  
  Lemma Lxx_head R s x y: y \in s -> (x::s) [L\in] R -> R.+ (x, y).
  Proof.
    by move => H1 /(@Lift_in_A _ R) H3;move: (allset_in H1 H3);rewrite /Aset inP -Fset_t0.  
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
    move: (@nth_drop i T y s 1) => + H1;rewrite addn1 => ?.
    move: (@drop_nth T y i s H1) => ->.
    by rewrite in_cons eq_refl orTb.
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

  Context (T:eqType).

  Implicit Types  (R: relation T) (s: seq T) (x y z : T).

  Lemma last_in_drop s z x:
    z \in s -> ~ (z = (last x s)) -> (last x s) \in (drop ((index z s).+1) s).
  Proof.
    move => /[dup] H1 /(nth_index z) H2 H3.
    pose m := (size s).-1; pose p := (index z s).+1.
    have H4: (index z s) < size s by rewrite index_mem.
    move: H4; rewrite leq_eqVlt => /orP [/eqP H4 | H4].
    + have P1': (index z s) = (size s).-1 -> z = (last x s)
        by move => H10; rewrite -H2 H10 nth_last;
                  apply: (@last_dv _ s z x 0);apply: (@in_non0 _ s z). 
      by have H5: z = last x s by apply: P1';rewrite -H4.
    + have P4: p + (m-p)= m by lia. 
      have P5: last x s = nth x (drop p s) (m-p) by rewrite nth_drop P4 -nth_last.
      have P8: m - p < size (drop p s) by rewrite size_drop /m; lia.
      by have P6: last x s \in (drop p s)
        by rewrite P5;apply: (@mem_nth _ x (drop p s) (m-p)).
  Qed.
  
  Lemma allL_take_drop R s x y z:
      z \in s -> allL R s x y 
      -> allL R (take (index z s) s) x z /\ allL R (drop ((index z s).+1) s) z y.
  Proof.
    move: (cat_take_drop ((index z s).+1) s) => H2 H1.
    have /(@take_nth T x): (index z s) < size s by rewrite index_mem.
    move: H1 => /(nth_index x) -> H1.
    by rewrite -{1}H2 H1 allL_cat => /andP [? ?].
  Qed.
  
  Lemma allL_belast R: forall s (x z y:T),
      z \in s -> ~ (z = (last x s)) -> allL R s x y -> R.+ (z, (last x s)).
  Proof.
    move => s x z y H1 H2 H3.
    pose proof allL_take_drop H1 H3 as [_ H4].
    have H5: last x s \in (drop (index z s).+1 s) by apply: last_in_drop.
    pose proof allL_take_drop H5 H4 as [H6 _]. 
    by pose proof (allL_to_clos_t H6). 
  Qed.
  
  Lemma in_behead s x z: z \in s -> ~ (z = (head x s)) -> z \in (behead s).
  Proof.
    by elim: s x z => [x z //| y s _ x z + /= ?];rewrite in_cons => /orP [/eqP ? | ? ].
  Qed.
  
  Lemma behead_head s x z:  z \in s ->  s = (head x s)::(behead s).
  Proof. by elim: s x => [| y s _ x _ ] //. Qed.
  
  Lemma allL_behead R s x z y: 
    z \in s  -> ~ (z = (head y s)) -> allL R s x y -> R.+ ((head y s),z).
  Proof.
    move => H1 H3; move: (in_behead H1 H3) => H5.
    rewrite (@behead_head s x z H1) allL_c => /andP [_ H4].
    pose proof (allL_take_drop H5 H4) as [H6 _].
    by apply: (allL_to_clos_t H6).
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
  
  Lemma allL_uniq_tail R s x y:
    allL R s x y -> exists s', subseq s' s /\  ~( y \in s') /\ allL R s' x y.
  Proof.
    elim: s x y => [// x y ? | a s Hr x y]; first by (exists [::]).
    case H2: (y == a). 
    by move: H2 => /eqP H2;rewrite allL_c -H2 => /andP [H3 _];(exists [::]);rewrite allL0.
    rewrite allL_c => /andP [H3 /Hr [s' [H4 [H5 H6]]]].
    exists [::a & s'];split; first by rewrite -cat1s -[a::s]cat1s; rewrite subseq_cat2l.
    by rewrite in_cons H2 /=;split;[ |rewrite allL_c H3 H6].
  Qed.
  
  Lemma allL_uniq_head R s x y:
      allL R s x y -> exists s', subseq s' s /\ ~( x \in s') /\ allL R s' x y.
  Proof.
    rewrite allL_rev => H1.
    pose proof allL_uniq_tail H1 as [s' H2].
    move: H2; rewrite  allL_rev inverseK => [[H2 [H3 H4]]].
    exists (rev s');split;last by  rewrite in_rev revK.
    by (have H5: s = (rev (rev s)) by rewrite revK); rewrite H5 subseq_rev.
  Qed.

  Lemma allL_uniq_internals R: forall (s: seq T) (x y: T),
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
      pose proof allL_take_drop H2 H6 as [_ H7].
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
  
  
  Lemma allL_uniq R: forall (s: seq T) (x y: T),
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
  
  Lemma TCP_uniq R: forall (x y:T), 
      R.+ (x,y) <-> exists s, uniq_path s x y /\ allL R s x y. 
  Proof.
    move => x y;split. 
    - rewrite TCP' /mkset => -[s /allL_uniq H1].
      by move: H1 => [s' [H1 [H2 [H3 [H4 /= H5]]]]];(exists s').
    - by move => [s [_ H1]]; move: H1;apply: allL_to_clos_t. 
  Qed.
  
  Lemma TCP_uniq'' R: forall (x y:T), 
      R.+ (x,y) /\ ~ (x = y) 
      <-> exists s, uniq (x::(rcons s y)) /\ (x::(rcons s y)) [L\in] R.
  Proof.
    move => x y.
    split => [[H1 H7] |].
    + move: (H1) => /TCP_uniq [s [[H3 [H4 H5]] H6]].
      by (exists s);rewrite uniq_crc.
    + by move => [s [/uniq_crc [_ H1] /(@allL_to_clos_t T)  H2]].
  Qed.
  
  Lemma TCP_uniq' R: forall (x y:T), 
      (Asym R.+)(x,y) 
      -> exists s, uniq (x::(rcons s y)) /\ (x::(rcons s y)) [L\in] R.
  Proof.
    move => x y /[dup] H0 [H1 H2]. 
    have H3: ~ (x = y) by move => H7;rewrite H7 in H1 H2.
    by rewrite -TCP_uniq''.
  Qed.

  Definition allLu R s x y := (x::(rcons s y)) [L\in] R /\ uniq (x :: rcons s y).
  
  Lemma TCP_uniq1 R x y: (Asym R.+)(x,y) <-> (exists s, allLu R s x y) /\ ~ R.+ (y,x).
  Proof. split. 
    by move => /[dup] /TCP_uniq' [s [H1 H2]] [_ H4];split;[exists s;split |].
    by move => [[s [H1 H2]] H3];split;[apply: allL_to_clos_t; apply: H1|].
  Qed.

End allL_uniq.

