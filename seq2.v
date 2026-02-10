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
From mathcomp Require Import all_boot seq order boolp classical_sets contra. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".

From RL Require Import  seq1 rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Seq1_plus. 
  (** * extensions of results from seq1 and rel using eqType *)
  
  Context {T:eqType}.
  
  Implicit Types (R: relation T) (s sl sr: seq T) (x y z : T) (X : set T).
  
  Lemma in_rcons s x y:  (x \in rcons s y) = (x \in s) || (x == y).
  Proof. by rewrite -cats1 mem_cat mem_seq1. Qed.
  
  Lemma last_in s x: ~ ( s = [::]) -> (last x s) \in s.
  Proof.
    by elim/last_ind: s x => [//|s x' _ x _];rewrite last_rcons in_rcons eq_refl orbT.
  Qed.
  
  Lemma mem_last s x: last x s \in x :: s.
  Proof. by rewrite lastI mem_rcons mem_head. Qed.
  
  Lemma size0E s: ( s = [::]) <-> size s == 0.
  Proof. by split => [/nilP|/nilP]. Qed.

  Lemma size0P s: ~ ( s = [::]) <-> 0 < size s.
  Proof. by split =>[|/[swap] /nilP/eqP -> //];contra;rewrite leqn0 => /nilP. Qed.
         
  
  Lemma head0 s x: ~ ( s = [::]) -> (head x s) \in s.
  Proof. by elim: s x => [//| x s _ ? _ /=];rewrite in_cons eq_refl. Qed.
   
  Lemma head_in s x y: 0 < size(s) -> head x (rcons s y) \in s.
  Proof.
    by elim: s x y => [x y //| z s Hr x y _ /=];rewrite in_cons eq_refl orbC orbT.
  Qed.
  
  Lemma behead_head s x z:  z \in s -> s = (head x s)::(behead s).
  Proof. by elim: s x => [| y s _ x _ ] //. Qed.
  
  Lemma in_behead s x z: z \in s -> ~ (z = (head x s)) -> z \in (behead s).
  Proof.
    by elim: s x z => [x z //| y s _ x z + /= ?];rewrite in_cons => /orP [/eqP ?| ?].
  Qed.
  
  Lemma in_subseq s1 s2 x: subseq s1 s2 -> (x \in s1) -> (x \in s2).
  Proof. by move => /subseqP [m _ ->];apply: mem_mask. Qed.
  
  Lemma notin_subseq s1 s2 x: subseq s1 s2 -> ~ (x \in s2) -> ~ (x \in s1).
  Proof. by move => H1; apply contraPP => /contrapT /(in_subseq H1) ? ?. Qed.
  
  Lemma in_non0 s x: x \in s -> 0 < size(s).
  Proof.
    by case H3: (size s);[apply size0nil in H3;rewrite H3 in_nil|].
  Qed.
  
  Lemma allset_in s x X: x \in s -> s [\in] X -> x \in X.
  Proof.
    elim: s x X => [ x X // | y s Hr x X ].
    rewrite in_cons allset_cons.
    move => /orP [/eqP -> | H1] [/inP H2 H3];[exact | by apply: Hr].
  Qed.
  
  Lemma in_rev s x: x \in s <-> x \in (rev s).
  Proof.
    have Impl s': (x \in s') -> (x \in (rev s'))
      by elim: s' => [//| z s2 H1];
                    rewrite in_cons rev_cons -cats1 mem_cat
         => /orP [/eqP -> |/H1 ->];[rewrite mem_seq1 eq_refl orbT|rewrite orTb].
    by split;[ apply Impl | move => /Impl H2; rewrite revK in H2].
  Qed.
  
  Lemma uniq_subseq s s' x: uniq (x :: s) -> subseq s' s -> uniq (x:: s').
  Proof.
    rewrite 2!cons_uniq => /andP [H2 H3] /[dup] H4 /subseqP [m _ H5]. 
    move: (subseq_uniq H4 H3) => ->;rewrite andbT.
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
    rewrite 2!uniq_catE => -[H1 [H2 H3]] H4.
    split;first exact;split;first by apply: (subseq_uniq H4 H2).
    move: H4 => /subseqP [m H4 H4'] s H5 H6.
    have H7: has [predI [in sl'] & [in sl]] sl'
      by apply/hasP;(exists s);[ | apply/andP].
    move: H7; rewrite [sl' in (has _ sl')]H4' => /has_mask/hasP [x H7 H8].
    move: H8 => /andP [_ H8].
    by pose proof (H3 x H8 H7).
  Qed.
  
  Lemma uniq_crc s x y:
    uniq (x::(rcons s y)) <-> ~ x \in s /\ ~ y \in s /\ uniq s /\ ~ (x = y).
  Proof.
    split => [ | [H1 [H2 [H3 H4]]]].
    + by rewrite cons_uniq in_rcons rcons_uniq =>
        /andP [/orP/not_orP [H1 /negP/eqP  H3] /andP [/negP H4 H5]].
    + rewrite cons_uniq;apply/andP; split. 
      by rewrite in_rcons;apply/orP/not_orP;split;[| apply/negP/eqP].
      by rewrite rcons_uniq;apply/andP;split;[apply/negP |].
  Qed.
  
  Lemma nth_in_take s y i j: i < j -> j < size s -> nth y s i \in take j s. 
  Proof. 
    move => /[dup] H1 /(@nth_take j T y i) <- H3.
    have H4: size (take j s) = j by apply: size_takel;lia.
    by apply: mem_nth;rewrite H4.
  Qed.
  
  Lemma nth_in_drop s y i j: i <= j -> j < size s  -> nth y s j \in drop i s.  
  Proof.
    pose proof nth_drop.
    move => H1 H2;pose proof (@nth_drop i T y s (j-i)) as H3.
    have H4: size (drop i s) = size s - i by apply: size_drop.
    have [H5 [H6 <-]]: 0 <= j -i /\  (j-i) < size(drop i s) /\ (i + (j - i)) = j 
      by rewrite H4;lia.
    have H8: nth y (drop i s) (j -i) \in (drop i s) by apply: mem_nth.
    by rewrite -H3.
  Qed.
  
  Lemma uniq_nth3 s y: uniq s <-> forall i j, i < j -> j < size s -> ~ (nth y s j = nth y s i).
  Proof. 
    split. 
    + move => + i j H2 H3. 
      pose proof (nth_in_take y H2 H3) as H4.
      rewrite -{1}(cat_take_drop j s) => /uniq_catE [_ [_ /(_ (nth y s i)) H7]] H8.
      have H9: nth y s i \in drop j s by rewrite -H8;apply: nth_in_drop.
      by apply: H7. 
    + apply: contraPP => /negP/uniqPn => /(_ y) [i [j [H1 H2]]] H3.
      by apply/existsNP;exists i;apply/existsNP;exists j => /(_ H1 H2);rewrite H3.
  Qed.
  
  Lemma uniq_nth2 s x y: ~ x \in s <-> forall i, i < size s -> ~ (x = nth y s i).
  Proof. 
    split => [H1 i /(mem_nth y) + H4 | H1 H2];first by rewrite -H4 => ?.
    have H3: (nth y s (index x s)) = x by apply: nth_index.
    by move:H2;rewrite -index_mem => /H1; rewrite H3.
  Qed.
  
  Lemma uniqE s x y z: 
    uniq (x :: rcons s y) <-> (forall i, i < size s -> ~ (x = nth z s i))
                           /\ (forall i, i < size s -> ~ (y = nth z s i))
                           /\ (forall i j, i < j -> j < size s -> ~ (nth z s j = nth z s i))
                           /\ ~ ( x = y).
  Proof. by rewrite -2!uniq_nth2 -uniq_nth3 uniq_crc. Qed.
  
  (* 
  Variables (a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 x y z:T).
  Definition st1:= [:: a1; b1; c1].
  Definition st2 : seq T:= [::].

  Compute  (x,(nth y st1 0)).
  Compute  ((nth z (x::(rcons st1 y)) 0),(nth z (x::(rcons st1 y)) 0.+1)).
  
  Compute  ((nth x st1 0),(nth y st1 0.+1)).
  Compute  ((nth z (x::(rcons st1 y)) 1),(nth z (x::(rcons st1 y)) 1.+1)).

  Compute  ((nth x st1 1),(nth y st1 1.+1)).
  Compute  ((nth z (x::(rcons st1 y)) 2),(nth z (x::(rcons st1 y)) 2.+1)).
  
  Compute  ((nth x st1 2),(nth y st1 2.+1)).
  Compute  ((nth z (x::(rcons st1 y)) 3),(nth z (x::(rcons st1 y)) 3.+1)).
  
  Compute  ((nth z (x::(rcons st2 y)) 0),(nth z (x::(rcons st2 y)) 0.+1)).
   *)
        
End Seq1_plus. 

Section allL_uniq.
  (** * The aim of this section is to prove allL_uniq  *)

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
  
  Lemma allL_behead R s x z y: 
    z \in s  -> ~ (z = (head y s)) -> allL R s x y -> R.+ ((head y s),z).
  Proof.
    move => H1 H3; move: (in_behead H1 H3) => H5.
    rewrite (@behead_head T s x z H1) allL_c => /andP [_ H4].
    pose proof (allL_take_drop H5 H4) as [H6 _].
    by apply: (allL_to_clos_t H6).
  Qed.
  
  Lemma drop_index s x:
    x \in s -> x::(drop (index x s).+1 s) = (drop (index x s) s).
  Proof.
    move => /[dup] /(nth_index x) H1.
    by rewrite -index_mem => /(@drop_nth T x);rewrite H1. 
  Qed.
  
  Lemma drop_notin s x:
    x \in s -> uniq s -> x \notin (drop (index x s).+1 s).
  Proof.
    move => /drop_index H0;rewrite -{1}(@cat_take_drop (index x s) _ s).
    by rewrite uniq_catE -H0 cons_uniq => -[_ [/andP [+ _] _]].
  Qed.
  
  Lemma allL_uniq_tail R s x y:
    allL R s x y -> exists s', subseq s' s /\ ~ ( y \in s') /\ allL R s' x y.
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
      split;first by rewrite -cat1s -[a::s]cat1s; rewrite subseq_cat2l.
      by split;[rewrite /uniq -/uniq H2 H5 | rewrite allL_c H3 H6].
    + exists (drop (index a s') s').
      split.
      ++ apply subseq_trans with [::a &s']; 
           last by rewrite -cat1s -[a::s]cat1s; rewrite subseq_cat2l.
         by apply subseq_trans with s';[apply drop_subseq|];apply subseq_cons.
      ++ split;first by apply drop_uniq.
         pose proof allL_take_drop H2 H6 as [_ H7].
         by rewrite -(drop_index H2) allL_c H3 H7. 
  Qed.
  
  Lemma allL_uniq R: forall (s: seq T) (x y: T),
      allL R s x y -> 
      exists s', subseq s' s /\ ~( x \in s') /\  ~(y \in s')
             /\  @uniq T s' /\ allL R s' x y. 
  Proof.
    move => s x y H1.
    pose proof allL_uniq_tail H1 as [s2 [S2 [I2 H2]]].
    pose proof allL_uniq_head H2 as [s3 [S3 [I3 H3]]].
    have J3: ~ (y \in s3) by  apply notin_subseq with s2.
    pose proof allL_uniq_internals H3 as [s4 [S4 [K4 H4]]].
    have J4: ~ (y \in s4) by apply notin_subseq with s3.
    have I4: ~ (x \in s4) by apply notin_subseq with s3.
    by exists s4;pose proof (subseq_trans (subseq_trans S4 S3) S2).
  Qed.
  
  Lemma TCP_uniq R x y: R.+ (x,y) <-> exists s, ~ x \in s /\ ~ y \in s /\ uniq s /\ allL R s x y. 
  Proof.
    split;last by move => [s [_ [_ [_ /(@allL_to_clos_t T R s) ?]]]].
    by rewrite TCP /mkset => -[s /allL_uniq H1];move: H1 => [s' /= [_ H1]];(exists s').
  Qed.
  
  Lemma TCP_uniq'' R x y:
      R.+ (x,y) /\ ~ (x = y) 
      <-> exists s, uniq (x::(rcons s y)) /\ (x::(rcons s y)) [L\in] R.
  Proof.
    split => [[H1 H7]|].
    + by move: H1 => /TCP_uniq [s [? [? [? ?]]]];(exists s);rewrite uniq_crc.
    + by move => [s [/uniq_crc -[_[_[_ ?]]] /(@allL_to_clos_t T) ?]].
  Qed.
  
  Lemma TCP_uniq' R x y: 
    (Asym R.+)(x,y) -> exists s, uniq (x::(rcons s y)) /\ (x::(rcons s y)) [L\in] R.
  Proof.
    move => /[dup] H0 [H1 H2]. 
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

Section allL_props.
  (** * more properties of allL  *)

  Context (T:eqType).
  Implicit Types  (R: relation T) (s: seq T) (x y z : T).
  
  Lemma allL_to_clos_t_left R s x y z: z \in s -> allL R s x y -> R.+ (x, z).
  Proof.
    move => H1 H2;pose proof (@allL_take_drop T R s x y z H1 H2) as [H3 _].
    by move: H3 => /(@allL_to_clos_t T R) H3.
  Qed. 

  Lemma allL_to_clos_t_right R s x y z: z \in s -> allL R s x y -> R.+ (z, y).
  Proof.
    move => H1 H2;pose proof (@allL_take_drop T R s x y z H1 H2) as [_ H3].
    by move: H3 => /(@allL_to_clos_t T R) H3.
  Qed. 
  
End allL_props.


