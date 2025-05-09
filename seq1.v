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

(******************************************************************************)
(* some operations on sequences which are usefull for dealing with graph paths*)
(* when the graph is described by a relation (relation as sets (set T*T))     *)
(*    p [\in] X    ==  all the elements of a node path p are in X              *)
(*    spt [\in] R  ==  all the elements of an edge path spt satisfy relation R *)
(*    p [Suc\in] R ==  the successive elements of the node paths p satisfy     *)
(*                  relation R. Just for sanity check and replaced by         *)
(*                  p [L\in]  R in practice.                                   *)
(*    Lift st     == an edge path built from a node path                      *)
(*    p [L\in]  R  == same as (p [Suc\in] R) but using a Lift                   *)
(*    UnLift spt  == Left inverse of Lift (spt: seq (T*T))                    *)
(* Seq_utilities: some utilities for sequences                                *)
(* Lift_props: properties of the Lift mapping                                 *)
(* allset: utilities for st [\in] X, X: set T                                  *)
(* allset2: utilities for spt [\in] R, R: relation T                           *)
(* Lift_in: properties of [L\in]                                               *)
(* allset_Lifted: properties of st [L\in] R for st: seqT                       *) 
(*                with specified endpoints                                    *)
(* Suc_as_Lift: st [L\in] R <-> st [Suc\in] R                                   *)
(* Lift_bijective: Lift is a bijection between                                *)
(*                 D:= [set p:seq T | size(p) > 1] and Lift D                 *)
(* Endpoints_and_Deployment: endpoints and Deployments                        *)
(* seq_subsets: properties of p: seq T, p [\in] X and p [L\in] R]               *)
(* seq_pairs_subsets: p: seq (T*T), p [\in] E and p [L\in] R]                   *)
(* PathRel: transitive closure and paths                                     *)
(* pair: sequences in  seq (T*T*O)                                           *)
(* pair_lift1: pair combined with Lift                                       *)
(* Seq_lifto: Lifto that is LiftO with constant orientation along the path   *)
(* Active_relation: D_U and active relation                                  *)
(* Active: The D_separated and Active relation as a relation on TxT          *)
(* PathRel_Examples: Utilities                                               *)
(******************************************************************************)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import ssrel rel. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Reserved Notation "p [\in] X" (at level 4, no associativity). 
Reserved Notation "p [L\in] R" (at level 4, no associativity).
Reserved Notation "p [Suc\in] R" (at level 4, no associativity).

(* begin snippet allnotation:: no-out *)  
Notation "p [\in] X" := (all (fun x => x \in X) p). 
(* end snippet allnotation *)  

Section Lift_def.
  (** * Lift operation on sequences *) 
  Variables (T: Type).
  
  (* begin snippet Lift:: no-out *)  
  Fixpoint Lift (st: seq T): seq (T*T) := 
    match st with 
    | x :: [:: y & st] as st1 => (x,y)::(Lift st1)
    | _ => Nil (T*T)
    end.
  (* end snippet Lift *)  
  
  (* another equivalent definition *)
  Definition Lift' (t:T) (st: seq T) := 
    (behead (pairmap (fun x y => (x,y)) t st)).
  
  Lemma Lift_eq: forall (t:T) (st:seq T), Lift st = Lift' t st.
  Proof.
    move => t;elim => [// | t1 s _];elim: s t1 => [// | t2 s H1 t1 //]. 
    have -> : Lift [:: t1, t2 & s] = (t1,t2)::(Lift [::t2 & s]) by split.
    by rewrite H1.
  Qed.

End Lift_def.

(* begin snippet Liftnota:: no-out *)
Notation "s [L\in] R" := (Lift s) [\in] R.
(* end snippet Liftnota *)

Section Suc_def.
  (** * s [Suc\in] R: consecutive elements of s satisfy relation R *)
  (** * we later prove that: s [L\in] R <-> s [Suc\in] R *)
    
  Variables (T: Type).

  Inductive RPath (R: relation T): seq T -> Prop :=
  | pp_void : RPath R [::]
  | pp_two (t: T) (st: seq T) : 
    RPath R st ->
    st = [::] \/ (exists (t': T), exists (st': seq T), st = [::t' & st'] /\ R (t,t'))
    -> RPath R ([:: t & st]).
      
End Suc_def. 

(* begin snippet RPath:: no-out *)  
Notation "s [Suc\in] R" := (RPath R s).
(* end snippet RPath *)  

Section Seq_utilities.
  (** * some utilities for sequences *)
  Variables (T: Type).

  Lemma seq_rc: forall (s: seq T), 
      (0 < size s) -> exists (s':seq T) (x:T), s = (rcons s' x).
  Proof.
    by elim => [ // | x s _ _];exists (belast x s), (last x s);rewrite lastI.
  Qed.

  Lemma seq_c: forall (s: seq T), 
      (0 < size s) -> exists (s':seq T) (x:T), s = x::s'.
  Proof.
    by elim => [ // | x s _ _]; exists s, x. 
  Qed.
  
  Lemma seq_rcrc: forall (s: seq T), 
      1 < size s -> exists (s':seq T) (x y:T), s = (rcons (rcons s' x) y).
  Proof.
    move => s H1.
    have H2: 0 < size s by apply: (leq_ltn_trans _ H1).
    pose proof seq_rc H2 as [q [x H3]].
    have H4: 0 < size q by rewrite H3 size_rcons ltnS in H1.
    pose proof seq_rc H4 as [r [z H5]].
    by exists r,z,x;rewrite H3 H5.
  Qed.
  
  Lemma seq_crc: forall (s: seq T), 
      1 < size s -> exists (s':seq T) (x y:T), s = x::(rcons s' y).
  Proof.
    move => s H1.
    have H2: 0 < size s by apply: leq_ltn_trans _ H1.
    pose proof seq_rc H2 as [r [y H3]].
    have H4: 0 < size r by rewrite H3 size_rcons ltnS in H1.
    pose proof seq_c H4 as [q [x H5]].
    by exists q,x,y;rewrite H3 H5.
  Qed.
  
  Lemma seq_cc: forall (s: seq T), 
      1 < size s -> exists (s':seq T) (x y:T), s = [::x,y &s'].
  Proof.
    move => s H1.
    have H2: 0 < size s by apply: leq_ltn_trans _ H1.
    pose proof seq_c H2 as [r [y H3]].
    have H4: 0 < size r by rewrite H3 ltnS in H1.
    pose proof seq_c H4 as [q [x H5]].
    by exists q,y,x;rewrite H3 H5.
  Qed.
  
  Lemma seq_1: forall (s: seq T), 
      size s = 1 <-> exists (x:T), s = [::x].
  Proof.
    split; last by move => [x H1];rewrite H1.
    by elim:s => [// | x s _ /= /succn_inj/size0nil ->];exists x.
  Qed. 
  
  Lemma seq_rcrc0: forall (s: seq T), 
      size s = 2 <-> exists (x y:T), s = [::x;y].
  Proof.
    split => [H1 |[x [y H1]]];last by rewrite H1.
    - have H2: 1 < size s by rewrite -H1.
      pose proof seq_rcrc H2 as [q [x [y H3]]].
      move: H1;rewrite H3 size_rcons size_rcons => /eqP H1.
      have /nilP H4: size q == 0 by [].
      by exists x,y;rewrite H4.
  Qed.

  Lemma seq_n: forall (n:nat) (s: seq T), 
      size s = n.+1 -> exists s',exists x, s = [::x & s'] /\ size(s') = n.
  Proof.
    elim => [| n Hn s H1].
    + elim => [_ // | t s H1 /= /succn_inj/size0nil H2]. 
      by rewrite H2;exists [::], t.
    + have H2: size(s) > 0  by rewrite H1. 
      pose proof (seq_c H2) as [q [x H3]].
      move: H1;rewrite H3 /= => /succn_inj H1.
      by exists q, x. 
  Qed.
  
  Lemma seq_rcn: forall (n:nat) (s: seq T), 
      size s = n.+1 -> exists s',exists x, s = rcons s' x /\ size(s') = n.
  Proof.
    elim => [| n Hn s H1].
    + by elim => [_ // | t s _ /= /succn_inj/size0nil ->]; exists [::], t.
    + have H2: size(s) > 0  by rewrite H1. 
      pose proof (seq_rc H2) as [s' [x H3]].
      move: H1; rewrite H3 size_rcons => /succn_inj H1.
      by (exists s', x).
  Qed.
  
  Lemma seq_cases: forall (s: seq T), 
      s=[::] \/ (exists x, s=[::x]) \/ exists (s':seq T), exists (x y:T), s=x::(rcons s' y).
  Proof.
    elim => [| x s _]; first by left.
    elim: s => [ | y s _]; first by right;left;(exists x).
    right;right.
    have H1: size([:: x, y & s]) > 1 by [].
    pose proof (seq_crc H1) as [q [x' [y' H2]]].
    by exists q;exists x';exists y';rewrite H2.
  Qed.

  Lemma seq_cases1: forall (s: seq T), 
      s=[::] \/ (exists x, s=[::x]) \/ exists (s':seq T), exists (x y:T), s=[::x,y & s'].
  Proof.
    elim => [| x s _]; first by left.
    elim: s => [ | y s _]; first by right;left;(exists x).
    right;right.
    have H1: size([:: x, y & s]) > 1 by [].
    pose proof (seq_cc H1) as [q [x' [y' H2]]].
    by exists q;exists x';exists y';rewrite H2.
  Qed.

  Lemma last_rev: forall (st: seq T) (t:T),
      last t (rev st) = head t st.
  Proof.
    elim => [// | t1 st1 Hr t].
    by rewrite rev_cons last_rcons /= .
  Qed.

End Seq_utilities.

Section Lift_props. 
  (** * properties of the Lift mapping *)
  Variables (T: Type).
  
  Lemma Lift_c: forall (st:seq T) (x y: T),
      Lift [::x,y & st] = [::(x,y) & Lift [::y & st]].
  Proof.
    by move => st x y; split.
  Qed.

  Lemma Lift_crc: forall (st:seq T) (x y: T),
      Lift (x::(rcons st y)) = (x,(head y st))::(Lift (rcons st y)).
  Proof.
    by move => st x y; rewrite headI Lift_c. 
  Qed.
  
  Lemma Lift_rcrc: forall (st:seq T) (x y: T),
      Lift (rcons (rcons st x) y) =  rcons (Lift (rcons st x)) (x,y).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    elim => [ x y // | z st Hr x y ].
    rewrite [in RHS]rcons_cons [in RHS]Lift_crc [in RHS]rcons_cons -[in RHS]Hr.
    by rewrite ![in LHS]rcons_cons [in LHS]Lift_crc H1. 
  Qed.
  
  Lemma Lift_rcc: forall (st:seq T) (x y: T),
      Lift (rcons (x::st) y) = rcons (Lift (x::st)) (last x st,y).
  Proof.
    by move => st x y;rewrite lastI Lift_rcrc.
  Qed.
  
  Lemma Lift_last: forall (st:seq T) (pt: T*T) (x y: T),
      last pt (Lift (x::(rcons st y))) = (last x st, y).
  Proof.
    elim/last_ind => [pt x y // | st z _ pt x y ].
    by rewrite -2!rcons_cons Lift_rcrc 2!last_rcons.
  Qed.

  Lemma Lift_head: forall (st:seq T) (pt: T*T) (x y: T),
      head pt (Lift (x::(rcons st y))) = (x,head y st).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    elim/last_ind => [pt x y // | st z _ pt x y].
    by rewrite Lift_crc H1 /=.
  Qed.
  
  Lemma head_Lift: forall (st:seq T) (pt: T*T),
      size(st) > 1 -> (head pt (Lift st)).1 = head pt.1 st.
  Proof.
    elim => [pt // | z st _ pt H3].
    have H4: size st > 0 by rewrite /size in H3;apply leq_ltn_trans with 0. 
    clear H3.
    elim: st z H4 => [z // | u st _ z H2].
    by rewrite Lift_c /=.
  Qed.
  
  Lemma last_Lift: forall (st:seq T) (pt: T*T),
      size(st) > 1 -> (last pt (Lift st)).2 = last pt.1 st.
  Proof.
    elim/last_ind => [pt // | st z _ pt H3].
    have H4: size st > 0 by rewrite size_rcons in H3;apply leq_ltn_trans with 0. 
    clear H3.
    elim/last_ind: st z H4 => [ z // | st u _ z H2].
    by rewrite Lift_rcrc 2!last_rcons. 
  Qed.
  
  Lemma Lift_cat_rc: forall (st st':seq T) (y z: T),
      Lift ((rcons st y) ++ (rcons st' z)) =
        Lift (rcons st y) ++ Lift (y::rcons st' z).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    elim => [q y z // | t st Hr q y z].
    rewrite rcons_cons cat_cons -rcons_cat Lift_crc rcons_cat Hr. 
    have H2: head z (rcons st y ++ q) = head y st
      by elim/last_ind: q y z => [y z | q z' Hr' y z];
                                [rewrite cats0 H1 | rewrite -rcons_cat H1 Hr'].
    by rewrite H2 -cat_cons -Lift_crc.
  Qed.
  
  Lemma Lift_cat_crc: forall (st st':seq T) (x y z: T),
      Lift (x::(rcons st y) ++ (rcons st' z)) =
        Lift(x::(rcons st y)) ++ Lift (y::rcons st' z).
  Proof.
    elim => [q x y z // | t st Hr q x y z].
    by rewrite Lift_crc [in RHS]cat_cons -Lift_cat_rc.
  Qed.
  
  Lemma Lift_rev: forall (st:seq T), 
      Lift (rev st) = map (fun tt =>(tt.2, tt.1)) (rev (Lift st)). 
  Proof.
    elim => [// | x st Hr ];elim: st x Hr => [// | x' st _ x H1].
    by rewrite rev_cons rev_cons Lift_rcrc 
       -rev_cons H1 Lift_c rev_cons map_rcons.
  Qed.
  
  (** Left inverse of Lift *)
  Fixpoint UnLift (spt: seq (T*T)) (t: T):= 
    match spt with 
    | [::] => [::t]
    | [::(t1,t2) & spt1 ] => [::t1 & UnLift spt1 t2]
    end.
  
  Lemma UnLift_c: forall (spt: seq (T*T)) (x y z: T),
      UnLift ((x, y) :: spt) z = [::x & UnLift spt y].
  Proof.
    by [].
  Qed.

  Lemma UnLift_sz: forall (spt: seq (T*T)) (z: T),
      size (UnLift spt z) = size (spt) +1.
  Proof.
    elim => [z // | [t t'] spt Hr z].
    by rewrite UnLift_c /= Hr 2!addn1.
  Qed.

  Lemma Lift_inv1: forall (st : seq T) (x y z: T),
      UnLift (Lift (x::(rcons st y))) z = (x::(rcons st y)).
  Proof.
    by elim => [// | y st Hr x' x z]; rewrite Lift_c UnLift_c Hr.
  Qed.

  Lemma UnLift_left: forall (t:T) (st : seq T),
      size (st) > 1 -> UnLift (Lift st) t = st.
  Proof.
    move => t st H1.
    pose proof (seq_crc H1) as [q [x [y H2]]]. 
    rewrite H2. apply Lift_inv1. 
  Qed.
  
  Lemma Lift_inv2: forall (st : seq T) (x: T),
      st <> [::] ->  UnLift (Lift st) (head x st) = st.
  Proof.
    move => st x'.
    pose proof seq_cases st as [H1 | [[x H1] | [r [x [y H1]]]]];rewrite H1 //;
      by move => _; apply Lift_inv1.
  Qed.
  
  Lemma Lift_inv_sz2: forall (st : seq T),
      (size(st) > 1) -> (forall (x:T), UnLift (Lift st) x = st).
  Proof.
    move => st.
    pose proof seq_cases st as [H1 | [[x H1] | [r [x [y H1]]]]];rewrite H1 //.
    by move => _ x1; apply Lift_inv1.
  Qed.
  
  Lemma Lift_inv: forall (st: seq T) (x y z: T),
      UnLift (Lift [::x,y & st]) z = [::x,y & st].
  Proof.
    by move => p x y z; apply Lift_inv_sz2.
  Qed.
  
  Lemma Lift_bc: forall (st: seq T) (x:T) (y: T*T) (spt: seq (T*T)),
      Lift (x :: st) = y :: spt -> x = y.1.
  Proof.
    move => st x' [y1 y2] q.
    by pose proof seq_cases st as [H1 | [[x H1] | [r [x [y H1]]]]];
    rewrite H1; [ | rewrite /= => [[?]] |rewrite Lift_c => [[?] _ _]].
  Qed.
  
  Lemma Lift_sz: forall (st:seq T),
      size(st) > 1 -> size (Lift st) = (size st) -1.
  Proof.
    move => st H1;pose proof seq_cc H1 as [q [x [y H2]]];rewrite H2;clear H2. 
    elim: q x y => [x y // | z q Hr x y].
    have H2: size ((x, y) :: Lift [:: y, z & q]) = 1+ size(Lift [:: y, z & q]) by [].
    by rewrite Hr in H2;rewrite Lift_c H2 /= addnC [RHS]subn1 subn1 addn1 /=.
  Qed.

  Lemma Lift_sz2: forall (st:seq T),
      size(Lift st) > 0 <-> size (st) > 1.
  Proof.
    by elim => [// | x st ]; elim: st x => [// | x st Hr y H1 // H2].
  Qed.

End Lift_props. 

Section allset.
  (** * utilities for st [\in] X, X: set T *)

  Variables (T: Type).

  (* begin snippet Sn:: no-out *)  
  (* Definition Sn (n: nat) (D: set T):= [set st| st [\in] D/\size(st)=n]. *)
  (* end snippet Sn *)
  
  Lemma allsetP: forall (X: set T) (st: seq T) (x:T),
      X x /\ st [\in] X <-> (x \in X) && (st [\in] X).
  Proof.
    by split => [[/mem_set -> ->] // | /andP [/set_mem H1 H2]].
  Qed.
  
  Lemma allset_consb: forall (X: set T) (st: seq T) (x:T),
      ((x::st) [\in] X) <-> (x \in X) && st [\in] X.
  Proof. by split. Qed.

  Lemma allset_cons: forall (X: set T) (st: seq T) (x:T),
      ((x::st) [\in]  X) <->  X x /\ st [\in] X.
  Proof.
    by move=> X st x;rewrite allset_consb allsetP.
  Qed.
  
  Lemma allset_subset: forall (X Y: set T) (st: seq T), 
      (X `<=` Y) -> (st [\in]  X) -> (st [\in] Y).
  Proof.
    move => X Y;elim => [ // | x' st' H1 H2 /andP [H3 H4]]. 
    apply/andP;split.
    by apply: mem_set;apply: H2; apply set_mem. 
    by apply H1.
  Qed.
  
  Lemma allset_rcons: forall (X: set T) (st: seq T) (x:T),
      (rcons st x) [\in] X <-> st [\in] X /\ X x.
  Proof.
    by move => X st x;rewrite all_rcons andC allsetP.
  Qed. 
    
  Lemma allset_rev: forall (X: set T) (st: seq T),
      st [\in] X <->  (rev st) [\in] X.
  Proof.
    by move => X st;rewrite all_rev.
  Qed. 
  
  Lemma allset_cat: forall (X: set T) (st st': seq T),
      (st++st') [\in] X <-> st [\in] X /\ st' [\in] X.
  Proof.
    by move=> X st q;rewrite all_cat;split => [/andP | [-> ->]].
  Qed.

  Lemma allset_I: forall (X Y: set T) (st: seq T),
    st [\in] (X `&` Y) <-> st [\in] X && st [\in] Y. 
  Proof.
    move => X Y st.
    have H1: (X `&` Y) `<=` X by apply: subIsetl. 
    have H2: (X `&` Y) `<=` Y by apply: subIsetr. 
    split => [H3 | ]. 
    by apply/andP;split;[apply: (allset_subset H1 H3)
                        | apply: (allset_subset H2 H3)].
    elim: st => [// |  x spa Hr /andP H3].
    move: H3; rewrite !allset_cons => [[[H3 H4] [H5 H6]]].
    by split;[rewrite /setI /mkset | apply Hr;apply/andP].
  Qed.
  
End allset.

Section allset2.
  (** * extra utilities for spt [\in] R, R: relation T *)
  Variables (T: Type).
  
  Lemma allset_inv: forall (E: relation T) (spt: seq (T*T)), 
      spt [\in] E <-> (map (fun tt => (tt.2,tt.1)) spt) [\in] E.-1. 
  Proof.
    move => E;elim => [ // | [x y] spt Hr].
    by rewrite map_cons !allset_cons Hr.
  Qed.
  
  Lemma allset_Rr: forall (X: set T) (x y: T) (st: seq T),
      (Lift (x::(rcons st y))) [\in] R_(X) <-> (rcons st y) [\in] X.
  Proof.
    move => X x y st.
    elim: st x. 
    - rewrite /= /Rr; split => [/andP [/inP H1 _] | /andP [/inP H1 _]].
      by rewrite /mkset /= in H1;apply mem_set in H1;rewrite H1.
      by apply/andP;split;[ apply/inP;rewrite /mkset /= |].
    - move => z st Hr x; rewrite rcons_cons Lift_c 2!allset_cons.
      split => [ [? /Hr ?] // | [? ?]].
      by split;[| apply Hr].
  Qed.

  Lemma allset_Lr: forall (X: set T) (x y: T) (st: seq T),
      (Lift (x::(rcons st y))) [\in] L_(X) <-> (x::st) [\in] X.
  Proof.
    move => X x y st.
    elim: st x. 
    - rewrite /= /Lr; split => [/andP [/inP H1 _] | /andP [/inP H1 _]].
      by rewrite /mkset /= in H1;apply mem_set in H1;rewrite H1.
      by apply/andP;split;[ apply/inP;rewrite /mkset /= |].
    - move => z st Hr x; rewrite rcons_cons Lift_c 2!allset_cons.
      split => [ [? /Hr ?] // | [? ?]].
      by split;[| apply Hr].
  Qed.
  
  Lemma allset_Dl: forall (X: set T) (E: relation T) (x y: T) (st: seq T),
      (Lift (x::(rcons st y))) [\in] (Δ_(X)`;`E) -> (x::st) [\in] X.
  Proof.
    by move => X E x y st;rewrite DeltaLco allset_I => /andP [/allset_Lr H1 _].
  Qed.

  Lemma allset_Dr: forall (X: set T) (E: relation T) (x y: T) (st: seq T),
      (Lift (x::(rcons st y))) [\in] (E`;`Δ_(X)) -> (rcons st y) [\in] X.
  Proof.
    by move => X E x y st;rewrite DeltaRco allset_I => /andP [_ /allset_Rr H1].
  Qed.

End allset2.

Section Lift_in. 
  (** * properties of [L\in] *)

  Variables (T: Type) (R R': relation T).

  Lemma Lift_in_F: forall (S: relation T) (st: seq T) (y: T),
        (rcons st y) [L\in] S -> st [\in] (S.+)#_(y).
  Proof.
    move => S.
    elim => [ // | x st Hr y].
    rewrite rcons_cons. 
    elim: st Hr.
    - by move => _;rewrite /= => /andP [/inP H1 _];rewrite andbT inP;apply Fset_t1 in H1.
    - move => z st Hr' H1. 
      rewrite Lift_crc 2!allset_cons => [[H2 /H1 H3]].
      split; last by [].
      move: H3; rewrite allset_cons => [[H3 /inP H4]].
      by apply Fset_t2;exists z.
  Qed.
  
  Lemma Lift_in_rev: forall (st: seq T),
      st [L\in] R <-> (rev st) [L\in] R.-1. 
  Proof.
    by move => st;rewrite allset_rev allset_inv Lift_rev.
  Qed.

  Lemma Lift_in_A: forall (st: seq T) (x: T),
      (x::st) [L\in] R -> st [\in] (R.+.-1)#_(x).
  Proof.
    move => st x. 
    rewrite Lift_in_rev rev_cons => /Lift_in_F H1.
    by rewrite allset_rev inverse_clos_t.
  Qed.

  Lemma Lift_inI: forall (st: seq T),
      st [L\in] R /\ st [L\in] R' <-> st [L\in] (R `&` R').
  Proof.
    by move => st;rewrite allset_I;split;move => /andP H1.
  Qed.
  
End Lift_in. 

Section allset_Lifted.
  (** * properties of st [L\in] R for st: seq T  *)
  (** * with specified endpoints *)
  
  Variables (T: Type) (E: relation T).

  (* begin snippet allL:: no-out *)  
  Definition allL (R: relation T) st x y := (x::(rcons st y)) [L\in] R.
  (* end snippet allL *)    

  Lemma allL0 : forall (x y : T),
      allL E [::] x y = ((x,y) \in E).
  Proof.
    by move => x y;rewrite /allL Lift_c /andP /= andbT. 
  Qed.

  Lemma allL0' : forall (x y : T),
      allL E [::] x y <-> E (x,y).
  Proof.
    by move => x y;rewrite allL0;split=> [/set_mem H1 // | /inP H1]. 
  Qed.
  
  Lemma allL_c: forall (st: seq T) (x y z: T),
      allL E (z::st) x y <-> ((x, z) \in E) && allL E st z y.
  Proof.
    by move => st x y z;split;[rewrite /allL rcons_cons Lift_c allset_cons |].
  Qed.

  Lemma allL_rc: forall (st: seq T) (x y z: T),
      allL E (rcons st z) x y <-> ((z,y) \in E) && allL E st x z.
  Proof.
    move => st x y z;split.
    by rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons;move => [-> /inP ->].
    by move => /andP [/inP ? ?];rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons. 
  Qed.
  
  Lemma allL_cat: forall (st st': seq T) (x y z: T),
      allL E ((rcons st y) ++ st') x z <-> allL E st x y && allL E st' y z.
  Proof.
    move => st st' x y z.
    rewrite /allL cat_rcons rcons_cat rcons_cons -cat_rcons Lift_cat_crc allset_cat.
    by split => [ [? ?] | /andP [? ?]];[apply/andP |].
  Qed.
  
  Lemma allL_subset: forall (S R: relation T) (st: seq T) (x y: T),
      (S `<=` R) -> allL S st x y -> allL R st x y.
  Proof.
    by move => S R st x y H1 H2;apply allset_subset with S.
  Qed.
  
  Lemma allL_WS_iff: forall (W:set T) (st: seq T) (x y: T),
      allL (Δ_(W.^c) `;` E) st x y <-> (x::st) [\in] W.^c && allL E st x y.
  Proof.
    move => W st x y.
    have H1: (L_(W.^c) `&` E) `<=` E by apply: subIsetr.
    have H2: (L_(W.^c) `&` E) `<=` L_(W.^c) by apply: subIsetl.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) E) as H4.    
    rewrite DeltaLco /allL allset_I.
    by split => /andP [/allset_Lr H5 H6];[apply /andP | apply /andP].
  Qed.
  
  Lemma allL_SW_iff: forall (W:set T) (st: seq T) (x y: T),
      allL (E `;` Δ_(W.^c)) st x y <-> (rcons st y) [\in] W.^c && allL E st x y.
  Proof.
    move => W st x y.
    have H1: (E `&` L_(W.^c)) `<=` E by apply: subIsetl.
    have H2: (E `&` L_(W.^c)) `<=` L_(W.^c) by apply: subIsetr.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) E) as H4.    
    rewrite DeltaRco /allL allset_I; split => /andP [H5 H6]. 
    by rewrite allset_Rr in H6; apply /andP; split. 
    by apply /andP; split;[| rewrite allset_Rr].
  Qed.
  
  Lemma allL_rev: forall (st: seq T) (x y: T),
      allL E st x y <->  allL E.-1 (rev st) y x.
  Proof.
    by move => st x y;rewrite Lift_in_rev rev_cons rev_rcons. 
  Qed.
  
  Lemma allL_All: forall (st: seq T) (x y: T),
      allL E st x y -> (x::st) [\in] (E.+)#_(y).
  Proof.
    by move => st x y;rewrite /allL -rcons_cons; apply: Lift_in_F.
  Qed.
  
End allset_Lifted.

Section seq_subsets.
  (** * properties of  p: seq T, p [\in] X and p [L\in] R] *)

  Variables (T: Type) (R: relation T) (X: set T).
  
  (* begin snippet RpathLone:: no-out *)  
  Lemma Rpath_L1: forall (st: seq T), st [\in] X -> st [L\in] (X `*` X). 
  (* end snippet RpathLone *)  
  Proof.
    have H1: forall (n:nat) (p': seq T),
        size(p') = n -> ( p' [\in] X -> p' [L\in] (X `*` X)).
    elim => [p /size0nil -> //| n Hr p H1].
    pose proof (seq_n H1) as [q [x [H2 H3]]].
    rewrite H2 allset_cons.
    elim: q x H2 H3 => [// | y r _ x' H2 H3 [H4 H5]].
    rewrite Lift_c allset_cons.
    move: (H5);rewrite allset_cons => [[H6 _]].
    by split;[ | apply Hr].

    by move => p; apply H1 with (size p).
  Qed.
  
  Lemma Rpath_L2: forall (st: seq T), size(st) > 1 /\ st [L\in] (X `*` X) -> st [\in] X.
  Proof.
    move => p [H1 H2].
    pose proof (seq_cc H1) as [q [x [y H3]]]. 
    move: H2; rewrite H3 Lift_c 2!allset_cons.
    clear H3.
    elim: q y => [y [[H2 H3] _] | z q Hr y [[H2 H2'] H3]];first by rewrite allset_cons;split.  
    move: H3; rewrite Lift_c allset_cons => [[[ H3 H3'] H4]].
    have [H5 H6]: X x /\ [:: z & q] [\in] X by apply Hr.
    by rewrite allset_cons.
  Qed.

  Lemma Rpath_L3: forall (st: seq T), st [\in] X /\ st [L\in] R -> st [L\in] ((X `*` X)`&`R) . 
  Proof.
    move => st [/Rpath_L1 H1 H2].
    by apply allset_I; rewrite H1 H2.
  Qed.

  Lemma Rpath_L4: forall (st: seq T), size(st) > 1 /\ st [L\in] ((X `*` X)`&`R) -> st [\in] X /\ st [L\in] R.
  Proof.
    by move => st;rewrite allset_I;move => [H1 /andP [H2 H3]];split;[apply: Rpath_L2|].
  Qed.
  
  Lemma Rpath_iff1 : 
    [set st | size(st) > 0 /\ st [\in] X /\ st [L\in] R]
    = [set st | size(st) = 1 /\ (st [\in] X) ] `|` [set st | size(st) > 1 /\ st [L\in] ((X `*` X)`&`R)]. 
  Proof.
    rewrite /setU /mkset predeqE => [p].
    split.
    - elim: p => [[? _] // | t p _ ]. 
      elim: p => [[_ [H1 _]] // | t' q Hr [H1 [H2 H3]]];first by left.
      right. split. by []. by apply Rpath_L3.
    - elim: p => [ [[? _] // | [? _] //] | t p _].
      elim: p => [ [[_ H1] // | [? _] //] | t' p'' _ [[? _]// | [_ ?]]].
      split. by [].
      by apply Rpath_L4.
  Qed.
  
  Lemma Rpath_iff2 : 
    [set st | st [\in] X /\ st [L\in] R] 
    = [set st | st = [::]] `|` [set st | size(st) > 0 /\ st [\in] X /\ st [L\in] R].
  Proof.
    rewrite /setU /mkset predeqE => [st].
    split.
    by elim: st => [[? _] // | t st _ ];[left | right].
    elim: st => [[_ /= // | [? _] //] | t st _ [? // | [_ [? ?]] //]].
  Qed.

  Lemma Rpath_iff :
    [set st | st [\in] X /\ st [L\in] R]
    =   [set st | st = [::]] 
          `|` [set st | size(st) = 1 /\ (st [\in] X) ] 
          `|` [set st | size(st) > 1 /\ st [L\in] ((X `*` X)`&`R)]. 
  Proof.
    rewrite -[RHS]setUA -[in RHS]Rpath_iff1 -[in RHS]Rpath_iff2.
    by [].
  Qed.

End seq_subsets.

Section Suc_as_Lift. 
  (** * st [L\in] R <-> st [Suc\in] R *)
  (* st [Suc\in] R is more natural to define a path and st [L\in] R is more computational 
   * for sanity check we prove that the two are equivalent
   *)

  Variables (T: Type) (R:relation T).

  (* begin snippet RPathequiv:: no-out *)  
  Lemma RPath_equiv: forall (st: seq T), st [L\in] R <-> st [Suc\in] R.
  (* end snippet RPathequiv *)  
  Proof.
    move => st.
    (* we use seq_cases to explore the three cases *)
    pose proof seq_cases st as [H1 | [[x H1] | [q [x [y H1]]]]];rewrite H1.
    by split => H;[apply pp_void | ].
    by split => H;[apply pp_two;[apply pp_void | left] | ].
    clear H1.
    split.
    - elim: q x y => [ //= x y /andP [/inP H2 _] | z q Hr x y ].
      by apply pp_two;[ apply pp_two;[constructor | left] | right; exists y, [::]].
      rewrite rcons_cons Lift_c allset_cons andC;
        by move => [H1 H2];apply pp_two;[ apply Hr | right; exists z, (rcons q y)].
    - move => H.
      elim/RPath_ind: H => [// | x' y' ep H1 [-> // | [y1 [ep1 [H2 H3]]]]].
      by rewrite H2 in H1 *; rewrite Lift_c allset_cons //.
  Qed.

End Suc_as_Lift. 

Section Lift_bijective.
  (** * Lift is a bijection between D:= [set p:seq T | size(p) > 1] and Lift D *)
  Variables (T: Type).
  
  (* A relation on (T*T) (Ch for Chain) *)
  (* begin snippet Chrel:: no-out *)  
  Definition Chrel {T:Type} :=[set s: (T*T)*(T*T)| (s.1).2 = (s.2).1].
  (* end snippet Chrel *)  
  
  (* a sequence of edges obtained by the Lift operations is always an edge path *)
  (* begin snippet LiftLift:: no-out *)  
  Lemma Lift_Lift: forall (st:seq T), (Lift st) [L\in] Chrel. 
  (* end snippet LiftLift *)
  Proof.
    move => st. 
    pose proof seq_cases st as [H1 | [[x H1] | [q [x [y H1]]]]].
    (* st = [::] *) by rewrite H1. 
    (* st = [::x] *) by rewrite H1. 
    (* st = x::(rcons q y) *)
    have H2: size(st) > 1 by rewrite H1 /= size_rcons.
    move: H2 => /seq_cc [q1 [x1 [x2 ->]]].
    elim: q1 x1 x2 => [ x' y' // | y' st' Hr z' x'].
    by rewrite 3!Lift_c allset_cons -Lift_c;split;[ |apply Hr].
  Qed.

  (* begin snippet DI:: no-out *)  
  Definition Lift_Dom {T: Type}:= [set st:seq T| size(st) > 1].
  Definition Lift_Im  {T: Type}:= [set spt:seq (T*T)| size(spt) > 0 
                                                      /\ spt [L\in] Chrel].
  (* end snippet DI *)
  
  Lemma Lift_image: forall (st: seq T),
      st \in Lift_Dom -> (Lift st) \in Lift_Im.
  Proof.
    rewrite /Lift_Dom /Lift_Im /mkset; move => st /inP H1;rewrite inP Lift_sz2.
    by split;[ | apply Lift_Lift].
  Qed.
  
  Lemma UnLift_image: forall (spt: seq (T*T)),
      spt \in Lift_Im -> (forall (z:T), (UnLift spt z) \in Lift_Dom).
  Proof.
    move => st /inP [H1 _] z; apply inP.
    rewrite /Lift_Dom /mkset.
    elim: st H1 => [// | [x y] st _ /= _].
    elim: st y => [ // | [x' y'] st' _ z'].
    by rewrite UnLift_c /=. 
  Qed.

  Lemma Lift_UnLift: forall (spt: seq (T*T)),
      spt \in Lift_Im -> (forall (z:T), Lift (UnLift spt z) = spt).
  Proof.
    move => st /inP [H1 H2] z; apply inP.
    elim: st H1 H2 => [// | [x y] st Hr H1 H2].
    rewrite UnLift_c.
    elim: st y x Hr H1 H2 => [y x _ _ _ /= // | [x' y'] st Hr y x H1 H2 H3].
    by apply inP.
    rewrite UnLift_c in H1.
    rewrite UnLift_c Lift_c.
    move: (H3). rewrite Lift_c allset_cons => [[H4 H5]].
    move: H4. rewrite /Chrel /mkset => [H4].
    have H6:  (Lift (x' :: UnLift st y'))= ((x', y') :: st)
      by apply inP; apply H1. 
    apply inP. rewrite H6.
    by have -> : y=x' by [].
  Qed.
  
  (* begin snippet Liftinj:: no-out *) 
  Lemma Lift_inj: forall (st st': seq T),
      st \in Lift_Dom -> Lift st = Lift st' -> st = st'.
  (* end snippet Liftinj *) 
  Proof.
    rewrite /Lift_Dom /mkset.
    move => st q /inP H1 H2.
    move: (H1) => /Lift_sz2 H3. 
    have H4: size(q) > 1. by rewrite -Lift_sz2 -H2. 
    pose proof seq_crc H1 as [r [x [y H5]]].
    pose proof Lift_inv_sz2 H1 as H6.
    pose proof Lift_inv_sz2 H4 as H7.
    by rewrite -(H6 x) -(H7 x) H2. 
  Qed.
  
  Lemma Lift_inj': forall (st st': seq T),
      st \in Lift_Dom -> st' \in Lift_Dom -> Lift st = Lift st' -> st = st'.
  Proof.
    move => st q /inP H1 /inP H2 H3.
    pose proof seq_crc H1 as [_ [x _]].
    have H4: UnLift (Lift st) x = UnLift (Lift q) x by rewrite H3.
    pose proof (UnLift_left x H1) as H5.
    pose proof (UnLift_left x H2) as H6.
    by rewrite -H5 -H6 H4.
  Qed.
  
  (* begin snippet Liftsurj:: no-out *) 
  Lemma Lift_surj: forall (spt: seq (T*T)), 
      spt \in Lift_Im -> exists st, st\in Lift_Dom /\ Lift st=spt. 
  (* end snippet Liftsurj *) 
  Proof.
    move => st H0; move: (H0);rewrite /Lift_Im /mkset => /inP [H1 H2].
    pose proof (seq_c H1) as [_ [[x _] _]].
    pose proof Lift_UnLift H0 x as H3.
    pose proof UnLift_image H0 x as H4.
    by exists (UnLift st x). 
  Qed.
  
  (* a surjectivy result on a larger set *)
  Lemma Lift_Chrel: forall (spt : seq (T*T)),
      (Lift spt) [\in] Chrel <-> exists st: seq T, Lift st = spt.
  Proof.
    elim => [ | [x y] spt _ ];first by split => ?;[(exists [::]) |].
    have H1: size ((x, y) :: spt) > 0 by [].
    split => [H2 |].
    - have H5: ((x, y) :: spt) \in Lift_Im by rewrite inP /Lift_Im /mkset.  
      pose proof Lift_UnLift H5 as H6.
      by (exists (UnLift ((x, y) :: spt) x));rewrite H6.
    - by move => [st <-]; apply Lift_Lift.
  Qed.
  
  (* begin snippet Liftlemma:: no-out *)  
  Lemma Lift_lemma:  image [set st | True] (@Lift T) 
                     = preimage (@Lift (T*T)) [set spt| spt [\in] Chrel].
  (* end snippet Liftlemma *)  
  Proof. 
    rewrite /image /preimage /mkset predeqE => spt.
    by split => [[x _ <-] | /Lift_Chrel [p H1]];[ apply Lift_Lift | exists p].
  Qed.

End Lift_bijective.

Section Endpoints_and_Deployment.
  (** * endpoints  *)
  
  Variables (T: Type) (ptv: T*T).
  
  (* begin snippet Pe:: no-out *)  
  Definition Pe (st: seq T) := (head ptv.1 st, last ptv.1 st).
  (* end snippet Pe:: no-out *)  
  
  (* begin snippet Epe1:: no-out *)  
  Definition Epe1 (spt: seq (T*T)) := (Pe (UnLift spt ptv.1)) .
  (* end snippet Epe1 *)  
  
  (* begin snippet Epe:: no-out *)  
  Definition Epe (spt: seq (T*T)) := ((head ptv spt).1, (last ptv spt).2).
  (* end snippet Epe *)  
  
  (* Epe (Lift st) = Pe st *)
  (* begin snippet EpeLift:: no-out *)  
  Lemma Epe_Lift: forall (st:seq T), st \in Lift_Dom -> Epe (Lift st) = Pe st.
  (* end snippet EpeLift *)  
  Proof.
    move => st /inP H1; rewrite /Epe /Pe.
    have ->: (head ptv (Lift st)).1 = head ptv.1 st by apply head_Lift.
    have ->: (last ptv (Lift st)).2 = last ptv.1 st by apply last_Lift.
    by [].
  Qed.
  
  Lemma Epe_Epe1: forall (spt: seq (T*T)), 
      size(spt) > 0 -> spt [L\in] Chrel -> Epe1 spt = Epe spt.
  Proof.
    move => spt H1 H2.
    have H4: spt \in (@Lift_Im T) by apply inP.
    pose proof Lift_surj H4 as [st [H5 H6]].
    move: (H5) => /inP H5'.
    have H7: Epe1 (Lift st) = Pe st 
      by rewrite /Epe1 /Pe;
      have -> :(UnLift (Lift st) ptv.1) = st by apply: UnLift_left H5'.
    have H8: Epe (Lift st) = Pe st by apply Epe_Lift.
    by rewrite -H6 H7 H8.
  Qed.
  
  (* Pe (UnLift spt ptv.1) = Epe spt. *) 
  (* begin snippet PeUnLift:: no-out *)  
  Lemma Pe_UnLift: forall (spt: seq (T*T)), 
      spt \in Lift_Im->Pe (UnLift spt ptv.1)=Epe spt.
  (* end snippet PeUnLift *)  
  Proof. 
    by move => spt /inP [H1 H2]; rewrite -Epe_Epe1 /Epe1.
  Qed.

  (** * deployment paths 
   * Lift and UnLift are bijective on deployment path 
   * D_V <-[Lift]-> D_P 
   *) 

  (* begin snippet DP:: no-out *)  
  Definition D_P (R E: relation T):= 
    [set spt| spt \in Lift_Im /\ R (Epe spt) /\ spt [\in] E ].
  (* end snippet DP *)  
  
  (* begin snippet DPs:: no-out *)  
  Definition D_P_s (x y: T) (E: relation T):= D_P [set (x,y)] E.
  (* end snippet DPs *)  

  (* begin snippet DV:: no-out *)  
  Definition D_V (R E: relation T):=
    [set st| st \in Lift_Dom /\ R (Pe st) /\ st [L\in] E].
  (* end snippet DV *)  
  
  (* begin snippet DVs:: no-out *)  
  Definition D_V_s (x y:T) (E: relation T) := D_V [set (x,y)] E.
  (* end snippet DVs *)  

  (** * Lift D_V = D_P *)
  Definition D_P1 (R E: relation T):= 
    [set spt| spt \in Lift_Im /\ R (Epe1 spt) /\ spt [\in] E ].

  Lemma D_P_D_P1: forall (R E: relation T), D_P R E = D_P1 R E.
    move => R E;rewrite /D_P /D_P1 /mkset predeqE => spt.
    split => [[/inP [H1 H1'] [H2 H3]] | [/inP [H1 H1'] [H2 H3]]].
    by pose proof Epe_Epe1 H1 H1' as ->;rewrite inP.
    by pose proof Epe_Epe1 H1 H1' as <-;rewrite inP.
  Qed.
  
  (* begin snippet DPDV:: no-out *)  
  Lemma DP_DV: forall (R E: relation T), image (D_V R E) (@Lift T) = (D_P R E).
  (* end snippet DPDV:: no-out *)  
  Proof.
    move => R E.
    rewrite D_P_D_P1 /D_V /D_P1 /mkset predeqE => q.
    split. 
    - move => [p [/inP H1 [H2 H3]] <-].
      move: (H1) => /Lift_sz2 H1'.
      rewrite /Epe1. 
      have -> : (UnLift (Lift p) ptv.1) = p by apply UnLift_left. 
      rewrite inP.
      by pose proof Lift_Lift p as H5.
    - move => [/inP [H1 H2] [H3 H4]].
      have H6 : Lift (UnLift q ptv.1) = q  by apply Lift_UnLift;rewrite inP /Lift_Im. 
      have H7: 1 < size (UnLift q ptv.1) by rewrite -H6 Lift_sz2 in H1.
      rewrite -H6 /=.
      by exists (UnLift q ptv.1);[rewrite H6 inP|].
  Qed.
  
  Lemma DV_DP: forall (R E: relation T) (spt: seq (T*T)), 
      spt \in (D_P R E) -> exists st, st \in (D_V R E) /\ Lift st = spt.
  Proof.
    move => R E spt.
    rewrite D_P_D_P1 inP => [[H1 [H3 H4]]].
    move: (H1) => /inP [H1' H2].
    pose proof Pe_UnLift H1 as H5.
    pose proof Epe_Epe1 H1' H2 as H6.
    pose proof UnLift_image H1 ptv.1 as H7.
    pose proof Lift_UnLift H1 ptv.1 as H8.
    exists (UnLift spt ptv.1).
    by rewrite inP /D_V /mkset H5 -H6 H8.
  Qed.
  
End Endpoints_and_Deployment.


Section seq_pairs_subsets.
  (** * p: seq (T*T), p [\in] E and p [L\in] R] *)
  
  Variables (T: Type).

  (* begin snippet Epathgt:: no-out *)  
  Example P_gt (n: nat) (E: relation T)  := 
    [set spt | size(spt) > n /\ spt [\in] E /\ spt [L\in] Chrel].
  (* end snippet Epathgt *)  
  
End seq_pairs_subsets.
  
Section PathRel.
  (** * transitive closure and paths
   * the main result here is that the relation in TxT obtained 
   * by fun (x y : T) => (exists (p: seq T), AllL E p x y)
   * is the relation E.+ the transitive closure of E 
   *)

  Variables (T: Type) (ptv: T*T) (E: relation T).
  
  (* relation based on paths: take care that the path p depends on (x,y) *)
  Definition PathRel_n (E: relation T) (n:nat) :=
    [set x | (exists (p: seq T), size(p)=n /\ allL E p x.1 x.2)].

  (* composition and existence of paths coincide *)
  Lemma Itern_iff_PathReln : forall (n:nat), E^(n.+1) =  PathRel_n E n.
  Proof.
    elim => [ | n' H].
    - rewrite /iter /PathRel_n Delta_idem_l /mkset predeqE => [[x y]].
      split => [ H | ].
      by (exists [::]); rewrite allL0' /=.
      by move => [p [/size0nil -> /allL0' H2]].
    - rewrite -add1n iter_compose H /iter Delta_idem_l /mkset predeqE => [[x y]].
      split => [[z [/= /inP H1 [p [H2 /= H3]]]] |[p [H1 H2]]];
                first by (exists (z::p));rewrite -H2 allL_c H3 andbT H1. 
      elim: p H1 H2 => [ // | z p' _ H1].
      move: H1;rewrite /size -/size -/addn1 => /succn_inj H1.
      rewrite allL_c /= => [/andP [/inP H2 H3]].
      by exists z;split;[ | exists p'].
  Qed.
  
  (* R.+ =  PathRel R *)
  (* begin snippet TCP':: no-out *)  
  Lemma TCP': E.+ = [set vp | exists p, (Lift (vp.1::(rcons p vp.2))) [\in] E].
  (* end snippet TCP' *)  
  Proof.
    rewrite /mkset predeqE => [[x y]].
    split => [H1 | [p H1]].
    - apply clos_t_iterk in H1.
      move: H1 => [n H1].
      rewrite  Itern_iff_PathReln /PathRel_n in H1.
      move: H1 => [p [H1 H2]].
      by (exists p).
    - have H2:  PathRel_n E (size p) (x, y) by (exists p).
      rewrite -Itern_iff_PathReln in H2.
      by apply iterk_inc_clos_trans in H2.
  Qed.

  (* begin snippet TCP:: no-out *) 
  Lemma TCP: E.+ = [set vp| exists p, size(p) > 1 /\ Pe ptv p = vp /\ p [L\in] E].
  (* end snippet TCP *)  
  Proof.
    rewrite /mkset /Pe predeqE => [[x y]].
    split => [H1 | [p [H1 [H2 H3]]]].
    - apply clos_t_iterk in H1.
      move: H1 => [n H1].
      rewrite  Itern_iff_PathReln /PathRel_n in H1.
      move: H1 => [p [H1 H2]].
      exists (x::(rcons p y)).
      by split;[rewrite /= size_rcons|split;[rewrite /= last_rcons |]].
    - pose proof seq_crc H1 as [q [x' [y' H4]]].
      move: H2; rewrite H4 /= last_rcons => [[<- <-]].
      have H5:  PathRel_n E (size q) (x', y') by (exists q);rewrite /allL -H4. 
      rewrite -Itern_iff_PathReln in H5.
      by apply iterk_inc_clos_trans in H5.
  Qed.

End PathRel.

Section pair. 
  (** * sequences in  seq (T*T*O) *)
  Variables (T: Type).

  (* orientation  *)
  (* begin snippet OO:: no-out *)
  Inductive O := | P | N.
  (* end snippet OO *)

  (* begin snippet pair:: no-out *)  
  Fixpoint pair (stt: seq (T*T)) (so: seq O) := 
    match stt, so with 
    | (pt)::stt, o::so => (pt,o)::(pair stt so)
    | (pt)::stt, [::] =>  (pt,P)::(pair stt [::])
    | _ , _ => Nil (T*T*O)
    end.
  (* end snippet pair *)  
  
  Fixpoint unpair (s: seq (T*T*O)) := 
    match s with 
    | [::] => ([::],[::])
    | (x,y)::s => (x::(unpair s).1,y::(unpair s).2)
    end.
  
  Lemma pair_c: forall (stt: seq (T*T)) (so: seq O) (pt: T*T),
      pair (pt::stt) so = (pt,head P so)::(pair stt (behead so)).
  Proof.
    elim => [ so pa | pa1 spt Hr so pa ]; first by elim: so => [// | o so _ //].
    elim: so => [// | o so _ ].
    have -> : pair [:: pa, pa1 & spt] (o :: so) = (pa,o)::(pair [::pa1 & spt] so) by [].
    by rewrite Hr.
  Qed.

  Lemma pair_sz1: forall (stt: seq (T*T)) (so: seq O),
      size (pair stt so) = size stt.
  Proof.
    by elim => [// | t st Hr ss];rewrite pair_c /= Hr.
  Qed.
  
  Lemma pair_cc: forall(st: seq (T*T)) (ss: seq O) (t: T*T) (s:O),
      pair (t::st) (s::ss) = (t,s)::(pair st ss).
  Proof.
    move => st ss t s.
    by elim: st => [// | t1 st ];elim: ss=> [// | s1 ss ].
  Qed.
  
  Lemma pair_cat: forall (p q: seq (T*T)) (sop soq: seq O),
      size sop = size p ->
      pair (p++q) (sop++soq) = (pair p sop) ++ (pair q soq).
  Proof.
    elim => [ q sop soq /eqP //= /nilP -> //= | ].
    move => a p Hr q sop soq H1.
    elim: sop H1 Hr => [// | so1 sop H1 H2 H3].
    rewrite cat_cons cat_cons pair_c //=.
    have H4: size sop = size p by rewrite /size in H2; apply succn_inj.
    have -> //: pair (p ++ q) (sop ++ soq) = pair p sop ++ pair q soq 
      by apply H3.
  Qed.
  
  Lemma unpair_c: forall (stto: seq (T*T*O)) (tt: T*T) (s: O),
      (unpair ((tt,s)::stto)) =  (tt::(unpair stto).1, s::(unpair stto).2).
  Proof.
    by move => stto tt s /=.
  Qed.
  
  Lemma unpair_sz: forall (sts: seq (T*T*O)),
      size (unpair sts).1 = size (unpair sts).2. 
  Proof.
    by elim => [// | [t1 s1] sts Hrt];rewrite /= -[in RHS]Hrt. 
  Qed.

  Lemma unpair_sz1: forall (sts: seq (T*T*O)),
      size (unpair sts).1 = size sts.
  Proof.
    by elim => [// | [t1 s1] sts Hrt];rewrite /= -[in RHS]Hrt. 
  Qed.
  
  Lemma unpair_left: forall (st: seq (T*T)) (so: seq O),
      size(st) = size(so) -> unpair (pair st so) = (st,so).
  Proof.
    elim => [ | t st Hrt].
    by elim => [ // | s1 so _ //].
    by elim =>  [ // | s1 so _ /succn_inj/Hrt H1] /=; rewrite H1.
  Qed.

  Lemma unpair1_left: forall (st: seq (T*T)) (so: seq O),
      (unpair (pair st so)).1 = st.
  Proof.
    elim => [ | t st Hrt].
    by elim => [ // | s1 so _ //].
    elim =>  [ // | s1 so _]. 
    by rewrite pair_c /unpair Hrt -/unpair.
    by rewrite pair_c /unpair Hrt -/unpair /=.
  Qed.
  
  Lemma unpair_right: forall (sts: seq (T*T*O)),
      pair (unpair sts).1 (unpair sts).2 = sts.
  Proof.
    by elim => [// | [t1 s1] sts Hrt];rewrite /= -[in RHS]Hrt. 
  Qed.
  
  Definition Spairs := [set sts:  seq (T*T*O) | True].
  Definition Pseq := [set st : (seq (T*T))*(seq O) | size st.1 = size st.2].
  Definition IPseq := [set sts |exists st, exists ss,
                         size(st)= size(ss) /\ pair st ss = sts].

  Lemma P1: image Pseq (fun st => pair st.1 st.2) = IPseq .
  Proof.
    rewrite /image /Pseq /mkset predeqE => sts.
    split => [[[st ss] /= H1] H2 | [st [ss [H1 H2]]]].
    by (exists st;exists ss).
    by exists (st,ss).
  Qed.

  Lemma P2: Spairs =  IPseq.
  Proof.
    rewrite /mkset predeqE => sts.
    split => [ _ | _ ]; last first. by [].
    by exists (unpair sts).1;exists (unpair sts).2;
         split;[apply unpair_sz|apply unpair_right].
  Qed.

  (* endpoints of pairs *) 
  
  Lemma pair_h: forall (st: seq (T*T)) (ss: seq O) (pt: (T*T)),
      size (ss) = size (st)-> 
      head (pt,P) (pair st ss) = (head pt st, head P ss).
  Proof. 
    elim => [ss t /= /size0nil -> //= | t1 st Hr ss t H1 ]. 
    by rewrite pair_c /=.
  Qed.

  Lemma pair_rc: forall (st: seq (T*T)) (ss: seq O) (pt: (T*T)) (s: O),
      size ss = size st
      -> rcons (pair st ss) (pt, s) =
          pair (rcons st pt) (rcons ss s).
  Proof.
    elim => [ss t s /size0nil -> // | t1 st' Hr ss t s H1 ]. 
    have H2: size ss > 0 by rewrite H1 /=.
    pose proof seq_c H2 as [ss' [s' H3]].
    rewrite pair_c H3 3!rcons_cons /= Hr.
    by [].
    by rewrite H3 /= in H1; apply succn_inj in H1.
  Qed.
  
  Lemma pair_rev: forall (st: seq (T*T)) (ss: seq O),
      size (ss) = size (st)-> 
      rev (pair st ss) = pair (rev st) (rev ss). 
  Proof. 
    elim => [ss // | t1 st' Hr ss H1 ]. 
    have H2: size ss > 0 by rewrite H1 /=.
    pose proof seq_c H2 as [ss' [s' H3]].
    have H4: size ss' = size st' by rewrite H3 /= in H1; apply succn_inj in H1.
    rewrite H3 pair_c 3!rev_cons /= Hr.
    apply pair_rc.
    by rewrite 2!size_rev.
    by [].
  Qed.

  Lemma pair_l: forall (st: seq (T*T)) (ss: seq O) (t: T*T) (s: O),
      size (ss) = size (st)-> 
      last (t,s) (pair st ss) = (last t st, last s ss).
  Proof. 
    elim => [ss t s /= /size0nil -> //= | t1 st Hr ss t s H1 ]. 
    have H2: size ss > 0 by rewrite H1 /=.
    pose proof seq_c H2 as [ss' [s' H3]].
    rewrite H3  pair_c 3!last_cons /=  Hr.
    by [].
    by rewrite H3 /= in H1; apply succn_inj in H1.
  Qed.
  
  Lemma pair_ch: forall (st: seq (T*T)) (so: seq O) (t: (T*T)),
      pair (t::st) so = (t,head P so )::(pair st (behead so)).
  Proof. by apply pair_c. Qed.

  Lemma pair_h1: forall (sto: seq (T*T*O)) (st: seq (T*T)) (so: seq O) (t:T*T) (to: T*T*O),
    sto = pair (t::st) so -> (head to sto).1 = t.
  Proof.
    by move => sto st so t to;rewrite pair_ch => -> /=. 
  Qed.

  Definition Extend (R: relation (T*T)) :=
    [set tto : (T*T*O)*(T*T*O) | R (tto.1.1,tto.2.1)].
  
  Lemma pair_L1: forall (R: relation  (T*T)) (st:seq (T*T)) (so:seq O), 
      size(st) = size (so) -> (pair st so) [L\in] (Extend R) <-> st [L\in] R.
  Proof.
    move => R st so H1.
    elim: st so H1 => [so H1 // | tt st Hr so H1].
    have H2: size so > 0 by rewrite -H1 /=.
    pose proof seq_c H2 as [so' [o H3]].
    have H4: size st = size so'. by rewrite H3 /= in H1; apply succn_inj in H1.
    rewrite H3. clear H3 H2 H1.
    elim: st so' H4 Hr => [ so' H4 Hr // | tt' st' _ so' H4 Hr].
    rewrite 2!pair_c 2!Lift_c 2!allset_cons.
    split. 
    - move => [H5 H6].
      split. by [].
      apply Hr in H4. apply H4.
      by rewrite pair_c.
    - move => [H5 H6].
      split. by [].
      apply Hr in H4.
      rewrite pair_c in H4.
      by rewrite H4.
  Qed.
  
  Lemma pair_L2: forall (R: relation  (T*T)) (stto:seq (T*T*O)),
      stto [L\in] (Extend R) <-> (unpair stto).1 [L\in] R.
  Proof.
    move => R stto. 
    elim: stto => [ // | [[t1 t1'] o1] stto Hr ].
    elim: stto Hr => [ Hr // |[[t2 t2'] o2] stto Hr Hr'].
    rewrite unpair_c Lift_c allset_cons.
    split => [ [H1 /Hr' H2] /= |].
    - rewrite /Extend /mkset /= -inP in H1.
      by rewrite  H1 andbC andbT.
    - rewrite unpair_c Lift_c allset_cons.
      move => [H1 H2].
      split. by [].
      apply Hr'.
      by rewrite unpair_c.
  Qed.

End pair.

Section Extended_Oriented_Paths.
      
  (** * pair combined with Lift *)
  Variable (T:Type) (tv:T) (ptv: T*T).
  
  (* begin snippet LiftO:: no-out *)  
  Definition LiftO (st: seq T) (so: seq O) := pair (Lift st) so.
  (* end snippet LiftO *)  
  
  (* begin snippet LiftOp:: no-out *)  
  Definition LiftOp (stso: (seq T)*(seq O)) := pair (Lift stso.1) stso.2.
  (* end snippet LiftOp *)  

  Definition O_rev (o:O) := match o with | P => N | N => P end.
  
  (* begin snippet Oedge:: no-out *)  
  Definition Oedge (E: relation T): set (T*T*O) :=
    [set oe: T*T*O | (match oe with | (e,P) => E e | (e,N) => E.-1 e end)].
  (* end snippet Oedge *)
  
  (* begin snippet ChrelO:: no-out *)  
  Definition ChrelO := [set ppa: (T*T*O)*(T*T*O) | (ppa.1.1).2 = (ppa.2.1).1].
  (* end snippet ChrelO *)  
  
  Definition UnLiftO (p: seq (T*T*O)) (x: T) :=
    (UnLift (unpair p).1 x, (unpair p).2).

  Definition UnLiftO1 (p: seq (T*T*O)) (x: T) := UnLift (unpair p).1 x.
  
  Lemma Oedge_rev: forall (E: relation T) (x y: T),
      Oedge E (x,y,P) = Oedge E (y,x,N).
  Proof.
    by move => E x y.
  Qed.
  
  Lemma Oedge_inv: forall (E: relation T) (x y: T) (o:O),
      Oedge E (x,y,o) = Oedge E.-1 (x,y, O_rev o).
  Proof.
    by move => E x y; elim. 
  Qed.
  
  Lemma ChrelO_Chrel: forall (tto tto': T*T*O), ChrelO (tto, tto') = Chrel (tto.1, tto'.1).
  Proof.
    by move => [tt o] [tt' o'];rewrite /ChrelO /Chrel /mkset /=.
  Qed.

  Lemma ChrelO_eq: forall (x y z t: T) (o1 o2:O),
      ChrelO ((x,y,o1), (z,t,o2)) <-> y = z.
  Proof. by []. Qed.
  
  Lemma LiftO_c: forall  (p:seq T) (so: seq O) (x y: T) (o:O),
      LiftO [::x,y & p] [::o & so]= [::(x,y,o) & LiftO [::y & p] so].
  Proof.
    by move => p x y;split.
  Qed.
  
  Lemma LiftO_crc: forall (p:seq T) (so: seq O) (x y: T) (o:O),
      LiftO (x::(rcons p y)) [::o & so] 
      = (x,(head y p),o)::(LiftO (rcons p y) so).
  Proof.
    by move => p so x y o;rewrite headI LiftO_c. 
  Qed.
  
  (** * bijective relation with LiftO and UnLiftO *)

  Lemma UnLiftO_left: forall (t: T) (st: seq T) (so: seq O),
      size (st) > 1 -> size(st) = size(so) + 1 
      -> UnLiftO (LiftO st so) t = (st,so).
  Proof.
    move => t st so H1 H2.
    have H3: size(Lift st) = (size st) -1 by apply Lift_sz.
    have H4: size(Lift st) = size(so) by rewrite H3 H2 addn1 subn1. 
    have H5: (unpair (pair (Lift st) so)) = ((Lift st), so)
      by apply unpair_left.
    by rewrite /UnLiftO /LiftO H5 /=;f_equal;apply Lift_inv_sz2.
  Qed.
  
  Lemma LiftO_image: forall (st:seq T) (so:seq O), 
      size(st)> 1 -> size(st) = size(so)+1
      -> size (LiftO st so) > 0 /\ (LiftO st so) [L\in] ChrelO.
  Proof.
    move => st so H1 H2.
    have H3: size(Lift st) = size so by apply Lift_sz in H1;rewrite H2 addn1 subn1 in H1.
    split; first by rewrite pair_sz1 H3;rewrite H2 addn1 in H1;apply leq_ltn_trans with 0. 
    rewrite /LiftO.
    have -> : (pair (Lift st) so) [L\in] (Extend Chrel) 
         <-> (Lift st) [L\in] Chrel by  apply pair_L1.
    by rewrite Lift_Lift.
  Qed.
  
  Lemma LiftO_right_0: forall (stto:seq (T*T*O)),
      size stto > 0 -> stto [L\in] ChrelO 
      -> size (unpair stto).1 > 0 /\ (unpair stto).1 [L\in] Chrel.
  Proof.
    move => stto;move => H1 H2.
    split; first by rewrite unpair_sz1.
    pose proof unpair_right stto as H3.
    have H4: (Extend Chrel) = ChrelO by [].
    have H5: size ((unpair stto).1) = size (unpair stto).2 by apply unpair_sz.
    pose proof pair_L1 Chrel H5 as H6.
    by rewrite -H6 unpair_right H4. 
  Qed.
  
  Lemma LiftO_right: forall (t:T) (stto:seq (T*T*O)),
      size stto > 0 -> stto [L\in] ChrelO 
      -> LiftO (UnLiftO stto t).1 (UnLiftO stto t).2 = stto. 
  Proof.
    move => t stto H1 H2.
    rewrite /LiftO /UnLiftO /=.
    pose proof LiftO_right_0 H1 H2 as [H3 H4].
    have H5: (unpair stto).1 \in (@Lift_Im T). by rewrite inP;by split.
    pose proof Lift_UnLift H5 t as H6.
    by rewrite H6 unpair_right.
  Qed.
  
  Lemma Lift_LiftO: forall (st:seq T) (so:seq O), 
      size st > 1 -> size(st) = size(so)+1 -> (LiftO st so) [L\in] ChrelO. 
  Proof.
    move => st so H1 H2.
    by pose proof LiftO_image H1 H2 as [H3 H4].
  Qed.
  
  (** * U_gt and  p: seq (T*T*O), p [\in] E and p [L\in] R] *)
  
  (* begin snippet Ugt:: no-out *) 
  Example U_gt (n: nat) (E: relation T):=
    [set sto | size(sto) > n /\ sto [\in] (Oedge E) /\ (Lift sto) [\in] ChrelO].
  (* end snippet Ugt *)
    
  Definition REopaths (E: set (T*T*O)) (R: relation (T*T*O)) := 
    [set spt:seq (T*T*O) | spt [\in] E /\ spt [L\in] ChrelO /\ spt [L\in] R].
  
  Lemma REopath_iff1: forall (E:set (T*T*O)) (R: relation (T*T*O)),
      [set spt:seq (T*T*O) | spt [\in] E /\ spt [L\in] (ChrelO `&` R)]
    = [set spt | spt = [::]] 
        `|` [set spt | size(spt) = 1 /\ (spt [\in] E) ] 
        `|` [set spt | size(spt) > 1 /\ spt [L\in] ((E `*` E)`&` (ChrelO `&` R))]. 
  Proof.
    by move => E R;rewrite -[RHS]Rpath_iff.
  Qed.

  Lemma REopath_iff2: forall (E: set (T*T*O)) (R: relation (T*T*O)),
      [set p:seq (T*T*O) | p [\in] E /\ p [L\in] (ChrelO  `&` R)]
      = [set p | p [\in] E /\ p [L\in] ChrelO /\ p [L\in] R].
  Proof.
    move => E R. rewrite /mkset predeqE => p.
    split => [ [H1 /allset_I/andP [H2 H3]]// | [H1 [H2 H3]] ].
    by rewrite allset_I H1 H2 H3.
  Qed.
  
  (* begin snippet Ugeone:: no-out *) 
  Definition U_ge_1 (E: relation T):=
    [set sto | sto [\in] (Oedge E) /\  size(sto) > 0 /\ 
                 (Lift sto) [\in] ChrelO].
  (* end snippet Ugeone *)
  
  (** * Endpoints in Extended oriented paths *)
  
  (* begin snippet Eope:: no-out *)  
  Definition Eope (stto : seq(T*T*O)) : T*T :=
    ((head (ptv,P) stto).1.1, (last (ptv,P) stto).1.2).
  (* end snippet Eope *)  
  
  (* begin snippet EopeLiftO:: no-out *)  
  Lemma Eope_LiftO: forall (st:seq T) (so:seq O),
      size(st) > 1 -> size (so) = size st -1 -> Eope (LiftO st so) = Pe ptv st.
  (* end snippet EopeLiftO *)  
  Proof.
    move => st so H1 H2.
    have H3: size (Lift st)= size so 
      by pose proof (Lift_sz H1) as H3;rewrite H3 H2.
    have H4: head (ptv,P) (pair (Lift st) so) = (head ptv (Lift st), head P so)
      by apply pair_h.
    have H5: (head (ptv,P) (LiftO st so)).1.1 = head ptv.1 st
      by rewrite /LiftO H4 /=;apply head_Lift.
    have H6: last (ptv,P) (pair (Lift st) so) = (last ptv (Lift st), last P so)
      by apply pair_l.
    have H7: (last (ptv,P) (LiftO st so)).1.2 = last ptv.1 st
      by rewrite H6 /=;apply last_Lift.
    by rewrite /Eope H7 H5.
  Qed.
  
  (* begin snippet PeUnLiftO:: no-out *)  
  Lemma Pe_UnLiftO: forall (stto: seq (T*T*O)), 
      size(stto) > 0 -> stto [L\in] ChrelO -> 
      (Pe ptv (UnLiftO stto ptv.1).1) =  Eope stto.
  (* end snippet PeUnLiftO *)  
  Proof. 
    move => stto H1 H2.
    rewrite /UnLiftO.
    rewrite /UnLiftO Pe_UnLift /Epe.
    pose proof unpair_right stto as H3.
    rewrite -[in RHS]H3 /Eope pair_h.
    rewrite pair_l.
    by [].
    by rewrite unpair_sz.
    by rewrite unpair_sz.
    pose proof LiftO_right_0 H1 H2 as [H3 H4].
    by rewrite inP.
  Qed.
  
  (** * deployment paths for extended oriented
   * Lift and UnLift are bijective on deployment path 
   * D_V <-[Lift]-> D_P 
   *) 
  
  (* begin snippet DU:: no-out *)  
  Definition D_U (R E: relation T) := [set stto : seq (T*T*O) |size(stto)>0 
     /\ R (Eope stto) /\ stto [\in] (Oedge E) /\ stto [L\in] ChrelO].
  (* end snippet DU *)  
  
  (* begin snippet DU1:: no-out *)  
  Definition D_U_s (x y: T) (E: relation T):= D_U [set (x,y)] E.
  (* end snippet DU1 *)  
  
  (* begin snippet DUp:: no-out *)  
  Definition D_U' (R E: relation T):=
    [set st : (seq T)*(seq O) | 
      st.1 \in (@Lift_Dom T) /\ size(st.2) = size(st.1) -1 /\ 
               R (@Pe T ptv st.1) /\ (LiftOp st) [\in] (Oedge E)].
  (* end snippet DUp *)  
  
  (* begin snippet DV1:: no-out *)  
  Definition D_U'_s (x y:T) (E: relation T) := D_U' [set (x,y)] E.
  (* end snippet DV1 *)  
  
  (* begin snippet DUDU':: no-out *) 
  Lemma DU_DU': forall (R E: relation T), image (D_U' R E) LiftOp = (D_U R E).
  (* end snippet DUDU':: no-out *)  
  Proof.
    move => R E.
    rewrite /D_U /D_U' /mkset predeqE => stto.
    split. 
    - move => [[st so] [/inP H1 [H2 [H3 H3']]] <-].
      move: (H1) => /Lift_sz2 H1'.
      have H4: size st > 1 by rewrite -Lift_sz2.
      have H5: size so +1 = size st by rewrite H2 addn1 subn1;apply: (ltn_predK H4).
      have H6: (UnLiftO (LiftO st so) ptv.1) = (st,so)
        by rewrite  /LiftOp;apply UnLiftO_left.
      have H7: size (pair (Lift st) so) > 0 by rewrite pair_sz1.
      have H8: size st = size so +1. by [].
      pose proof LiftO_image H4 H8 as [H9 H10].
      pose proof Pe_UnLiftO H7 H10 as H11.
      by rewrite -H11 H6.
    - move => [H1 [H2 [H3 H4]]].
      pose proof LiftO_right ptv.1 H1 H4 as H5.
      have H6: LiftOp (UnLiftO stto ptv.1) = stto by [].
      rewrite -H6 /=. 
      exists (UnLiftO stto ptv.1); last by [].
      pose proof  Pe_UnLiftO H1 H4 as H7.
      by rewrite H6 H7 inP /UnLiftO /= /Lift_Dom /mkset UnLift_sz 
         -unpair_sz unpair_sz1 addn1 subn1.
  Qed.
  
  Lemma DU'_DU: forall (R E: relation T) (stto: seq (T*T*O)), 
      stto \in (D_U R E) -> exists st, st \in (D_U' R E) /\ (pair (Lift st.1) st.2) = stto.
  Proof.
    move => R E spt /inP [H1 [H3 [H4 H5]]].
    exists (UnLiftO spt ptv.1).
    pose proof LiftO_right ptv.1 H1 H5 as H6.
    pose proof Pe_UnLiftO H1 H5 as H7.
    pose proof LiftO_right ptv.1 H1 H5 as H8.
    have H9: LiftOp (UnLiftO spt ptv.1) = spt by rewrite /LiftOp.
    rewrite inP /D_U' /mkset.
    split;last by rewrite -[RHS]H6.
    split.
    by rewrite /UnLiftO inP /Lift_Dom /mkset UnLift_sz unpair_sz1 addn1.
    split.
    by rewrite /UnLiftO UnLift_sz /= unpair_sz addn1 subn1.
    split.
    by rewrite H7.
    by rewrite H9.
  Qed.
  
  (* begin snippet DU2:: no-out *) 
  Definition D_U'' (R E: relation T):=
    [set spa | spa [\in] (Oedge E) /\
                 (exists p, exists x,exists y,exists o, (LiftO (x::(rcons p y)) o) = spa /\ R (x,y))].
  (* end snippet DU2 *)

  (* begin snippet Atr:: no-out *)  
  Definition A_tr (W: set T) (E: relation T) := ChrelO `&` 
    [set oe : (T*T*O) * (T*T*O)| match (oe.1.2,oe.2.2, oe.1.1.2) with 
      | (P,P,v) => W.^c v | (N,N,v) => W.^c v | (N,P,v) => W.^c v
      | (P,N,v) => (Fset E.* W) v end].
  (* end snippet Atr *)
  
  Lemma A_tr_P1: forall(W: set T) (E: relation T), A_tr W E = ChrelO `&` (A_tr W E).
  Proof.
    by move => W E;rewrite /A_tr setIA setIid.
  Qed.

  (* begin snippet ActiveOe:: no-out *)  
  Definition ActiveOe (W: set T) (E: relation T) :=  
    ((Oedge E) `*` Oedge E) `&` (A_tr W E).
  (* end snippet ActiveOe *)  

  (* Equivalent definition see ActiveOe_iff used in proofs *)
  Definition ActiveOe' (W: set T) (E: relation T) := 
    [set oe : (T*T*O) * (T*T*O) | 
      Oedge E oe.1 /\ Oedge E oe.2 /\ (ChrelO oe)
      /\ match (oe.1.2,oe.2.2, oe.1.1.2) with 
        | (P,P,v) => W.^c v
        | (N,N,v) => W.^c v
        | (N,P,v) => W.^c v
        | (P,N,v) => (Fset E.* W) v
        end].
  
  Lemma ActiveOe_iff: forall (W: set T) (E: relation T), 
      ActiveOe W E = ActiveOe' W E.
  Proof.
    move => W E.
    rewrite /ActiveOe' /A_tr /ActiveOe /setI /setX /mkset predeqE => [[eo1 eo2]].
    by split => [[[H1 H2] [H3 H4]] | [H1 [H2 [H3 H4]]]]. 
  Qed.
  
  Lemma ActiveOe_Oedge: forall (W: set T) (E: relation T) (eo : (T*T*O) * (T*T*O)),
      (ActiveOe W E) eo -> Oedge E eo.1 /\ Oedge E eo.2.
  Proof.
    by move => W E eo [H1 [H2 _]].
  Qed.
  
  Lemma ActiveOe_Compose: forall (W: set T) (E: relation T) (eo : (T*T*O) * (T*T*O)),
      eo \in (ActiveOe W E) -> ChrelO eo. 
  Proof.
    by move => W E eo;rewrite ActiveOe_iff => /inP [_ [_ [H3 _]]].
  Qed.

  Lemma ActiveOe_ChrelO: forall (W: set T) (E: relation T),
      (ActiveOe W E) `<=` ChrelO.
  Proof.
    move => W E;rewrite /subset => s /inP H1.
    by apply ActiveOe_Compose with W E.
  Qed.
  
  Lemma ActiveOe_o: forall (W: set T) (E: relation T) (x y z: T) (o:O),
      (ActiveOe W E) ((x,y,o),(y,z,o)) 
      <-> (Oedge E (x,y,o)) /\ (Oedge E (y,z,o)) /\ W.^c y.
  Proof.
    move => W E x y z o;rewrite ActiveOe_iff /mkset /ChrelO /=.
    case: o.
    by split => [[? [? [_ ?]]] // | [? [? ?]]].
    by split => [[? [? [_ ?]]] // | [? [? ?]]].
  Qed.
  
  Lemma ActiveOeT: forall (W: set T) (E: relation T) (x u v z t: T) (o1 o2 o3 o4: O),
      (Fset E.* W) x 
      /\ ActiveOe W E ((u,x,o1), (x,v,o2)) /\ ActiveOe W E ((z,x,o3), (x,t,o4))
      -> ActiveOe W E ((u,x,o1), (x,t,o4)).
  Proof.
    move => W E x u v z t o1 o2 o3 o4;rewrite ActiveOe_iff.
    case: o1;case: o2; case:o3; case:o4;
      by move => [H0 [[H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]]]].
  Qed.
  
  Lemma ActiveOe_rev: forall (W:set T) (E: relation T) (e1 e2: T*T) (o:O),
      (ActiveOe W E).-1 ((e1,o), (e2,o)) 
      <-> ActiveOe W E.-1 ((e2,O_rev o), (e1,O_rev o)).
  Proof.
    by move => W E [x1 y1] [x2 y2] o; case: o. 
  Qed.
  
  (** * The final set we wish to study *)

  (* begin snippet DUa:: no-out *)  
  Definition D_U_a (R E: relation T) (W: set T) (x y:T):=
    (D_U R E) `&` [set stto | stto [L\in] (A_tr W E)].
  (* end snippet DUa *)  
  
  Definition D_U_a' (R E: relation T) (W: set T) (x y:T):=
    [set stto : seq (T*T*O) | size(stto)>0 
     /\ R (Eope stto) /\ stto [\in] (Oedge E) /\  stto [L\in] (A_tr W E)].
  
  Lemma DU_a_DU_a': forall (R E: relation T) (W: set T) (x y:T),
      D_U_a R E W x y =  D_U_a' R E W x y.
  Proof. 
    move => R E W x y.
    rewrite /D_U_a /D_U_a' /D_U /setI /mkset predeqE => stto.
    split. 
    - by move => [[? [? [? ?]]] ?].
    - rewrite 1!A_tr_P1. 
      move => [H1 [H2 [H3 /allset_I/andP [H4 H5]]]].
      by rewrite -1!A_tr_P1. 
  Qed.

  Definition D_U_a1' (E: relation T) (W: set T) (x y:T) := 
    D_U_a [set (x,y)] E W x y.
  
  (* begin snippet DUaone:: no-out *)  
  Definition D_U_a1 (E: relation T) (W: set T) (x y:T):=
    [set stto |size(stto)>0 /\ (Eope stto)=(x,y) /\ stto [\in] (Oedge E) 
               /\ stto [L\in] ChrelO /\ stto [L\in] (A_tr W E)].
  (* end snippet DUaone *)  
  
  Lemma DU_a1_DU_a1': forall (E: relation T) (W: set T) (x y:T),
      D_U_a1 E W x y =  D_U_a1' E W x y.
  Proof. 
    move => E W x y.
    rewrite /D_U_a1 /D_U_a1' /D_U_a /D_U /setI /mkset predeqE => stto.
    by split;[move => [? [? [? [? ?]]]]| move => [[? [? [? ?]]] ?]].
  Qed.
  
  (* Active is now almost expressed as a transitive closure 
   * on an lifted space (A * A) * O as it uses AllL *)
  (* begin snippet Aeop:: no-out *)  
  Definition Active_path
    (W: set T) (E: relation T) (p: seq (T*T*O)) (x y: T) :=
    match p with 
    | [::] => x = y 
    | [::eo1] => eo1.1.1 = x /\  eo1.1.2 = y /\  Oedge E eo1 
    | eo1 :: [:: eo2 & p]
      => eo1.1.1 = x /\ (last eo2 p).1.2 = y 
        /\ allL (ActiveOe W E) (belast eo2 p) eo1 (last eo2 p)
    end.
  (* end snippet Aeop *)

  Theorem Active_check1: forall (E: relation T) (W: set T) (x y:T) stto,
      ((x=y /\ stto = [::]) \/  stto \in (D_U_a1 E W x y))
      -> Active_path W E stto x y.
  Proof.
    move => E W x y stto.
    pose proof seq_cases1 stto as [H1 | [[[[t t'] o] H1] | [stto' [eo1 [eo2 H1]]]]].
    - rewrite H1; move => [[-> _] // |].
      by rewrite inP /D_U_a1 /mkset /= => [[H2 _]].
    - rewrite H1; move => [[-> H2] // |].
      by rewrite inP /D_U_a1 /mkset /Eope /= andbT inP /Oedge => [[_ [[H3 H3'] [H4 _]]]].
    - rewrite H1; move => [[-> H2] // |].
      rewrite inP /D_U_a1 /mkset.  
      rewrite /Active_path.
      have H2: (head (ptv,P) [:: eo1, eo2 & stto']).1.1 = eo1.1.1 by [].
      have H3: (last (ptv,P) [:: eo1, eo2 & stto']).1.2 = (last eo2 stto').1.2
        by rewrite 2!last_cons.
      have H4: eo1::(rcons (belast eo2 stto') (last eo2 stto')) = stto
        by rewrite -lastI.
      rewrite -H2 -H3 /allL H4 -H1. 
      move => [H5 [[H6 H6'] [H7 [H8 H9]]]].
      have H10: stto [L\in] (ActiveOe W E)
        by apply (@Rpath_L3 (T*T*O)).
      by [].
  Qed.

  Theorem Active_check2: forall (E: relation T) (W: set T) (x y:T) stto,
      Active_path W E stto x y
      -> ((x=y /\ stto = [::]) \/  stto \in (D_U_a1 E W x y)).
  Proof.
    move => E W x y stto.
    pose proof seq_cases1 stto as [H1 | [[[[t t'] o] H1] | [stto' [eo1 [eo2 H1]]]]].
    - by rewrite H1 /Active_path; left. 
    - rewrite H1 /Active_path; move => [/= -> [-> H4]]; right.
      by rewrite inP /D_U_a1 /mkset /Eope allset_cons.
    - rewrite H1 /Active_path; move => [H2 [H3 H4]]; right.
      have H5: (head (ptv,P) [:: eo1, eo2 & stto']).1.1 = eo1.1.1 by [].
      have H6: (last (ptv,P) [:: eo1, eo2 & stto']).1.2 = (last eo2 stto').1.2
        by rewrite 2!last_cons.
      have H7: eo1::(rcons (belast eo2 stto') (last eo2 stto')) = stto
        by rewrite -lastI.
      have H8: stto [L\in]  (ActiveOe W E) by rewrite -H7.
      move: H2 H3 H8;rewrite -H5 -H6 -H1 => H2 H3 H8.
      rewrite inP /D_U_a1 /mkset.
      have H9:  1 < size stto by rewrite H1.
      have H9':  0 < size stto by rewrite H1.
      have H10: stto [\in] (Oedge E)
        by move: H8;rewrite allset_I => /andP [H8 H8']; apply (@Rpath_L2 (T*T*O)).
      have H11: stto [L\in] ChrelO
        by pose proof ActiveOe_ChrelO;apply allset_subset with (ActiveOe W E);
        [apply ActiveOe_ChrelO |].
      have H12: stto [L\in] (A_tr W E)
        by apply allset_subset with (ActiveOe W E);[ rewrite /ActiveOe|].
      by rewrite /Eope H2 H3. 
  Qed.

  (** * Two equivalent definitions of D_separated *)
  (** * in D_separated_iff. *)

  Lemma Active_eq: forall (E: relation T) (W: set T) (x y:T) stto,
      ((x=y /\ stto = [::]) \/  stto \in (D_U_a1 E W x y))
      <-> Active_path W E stto x y.
  Proof.
    move => E W x y stto.
    split. 
    apply Active_check1.
    apply Active_check2.
  Qed.
  
  Lemma D_separated_L3: forall (W: set T) (E: relation T) (x y: T),
      (D_U_a1 E W x y) != set0 <-> (exists p, D_U_a1 E W x y p).
  Proof.
    move => W E x y;rewrite -notempty_exists. 
    by split;move => [p /inP H1]; exists p.
  Qed.

  Lemma D_separated_L5: forall (W: set T) (E: relation T) (x y: T),
      ~ (exists p, D_U_a1 E W x y p) <-> (D_U_a1 E W x y) = set0.
  Proof.
    by move => W E x y;rewrite -D_separated_L3 empty_iff.
  Qed.
  
  Lemma D_separated_L4: forall (W: set T) (E: relation T) (x y: T),
      ~ (exists (p: seq (T*T*O)), Active_path W E p x y)
      <-> ~( (x=y \/ (exists p, D_U_a1 E W x y p))).
  Proof.
    move => W E x y; rewrite iff_not2 -D_separated_L3.
    split. 
    - move => [p /Active_eq [[H1 _] | H1]].
      by left. 
      by right;rewrite -notempty_exists;exists p.
    - move => [-> | /notempty_exists [p H1]]. 
      + by (exists [::]).
      + by exists p;apply Active_eq; by right.
  Qed.
  
  Lemma D_separated_L6: forall (W: set T) (E: relation T) (x y: T),
      ~ (x=y \/ (exists p, D_U_a1 E W x y p))
      <-> ~ (x = y) /\ (D_U_a1 E W x y) = set0.
  Proof.
    move => W E x y.
    split.
    by rewrite not_orE => [[H1 /D_separated_L5 H2]]. 
    by move => [H1 H2]; rewrite not_orE D_separated_L5.
  Qed.
  
  Lemma D_separated_L7: forall (W: set T) (E: relation T) (x y: T),
      ~ (exists (p: seq (T*T*O)), Active_path W E p x y)
      <->  ~ (x = y) /\ (D_U_a1 E W x y) = set0.
  Proof.
    by move => W E x y; rewrite D_separated_L4 D_separated_L6.
  Qed.
  
  Lemma D_separated_L0: forall (W: set T) (E: relation T) (x y: T),
    (D_U_a1 E W x y) = set0 
    <-> ((D_U [set (x,y)] E) `&` [set stto | stto [L\in] (A_tr W E)]) = set0.
  Proof. 
    by move => W E x y; rewrite DU_a1_DU_a1' /D_U_a1' /D_U_a .
  Qed.

  Lemma D_separated_L1: forall (T': Type) (A B: set T'),
      A `&` B = set0 <-> A `<=` ~` B.
  Proof.
    move => A B;split.
    - by move => /disj_set2P/disj_setPLR ?.
    - by move => /disj_setPLR/disj_set2P ?.
  Qed.

  Lemma D_separated_L2: forall (W: set T) (E: relation T) (x y: T),
      (D_U_a1 E W x y) = set0 
      <->  (D_U [set (x,y)] E) `<=` ~` [set stto | stto [L\in] (A_tr W E)].
  Proof.
    by move =>  W E x y;rewrite D_separated_L0 D_separated_L1.
  Qed.
  
  (* begin snippet  Activeeq:: no-out *)  
  Definition Ub (W: set T) (E: relation T) := 
    ~` [set stto | stto [L\in] (A_tr W E)].
  Lemma D_separated_iff: forall (W: set T) (E: relation T) (x y: T),
      ~(exists (p: seq (T*T*O)), Active_path W E p x y)
      <-> ~ (x = y) /\  (D_U [set (x,y)] E) `<=` (Ub W E). 
  (* end snippet  Activeeq *)  
  Proof.
    by move  =>  W E x y;rewrite D_separated_L7 D_separated_L2.
  Qed.
  
End Extended_Oriented_Paths.

Section Seq_lifto. 
  (** * Lifto that is LiftO with constant orientation along the path  *)
  Variables (T: Type).
  
  Fixpoint pair_o (spt: seq (T*T)) (o: O):= 
    match spt with
    | [::] => @nil (T*T*O)
    | pa::spt => (pa,o)::(pair_o spt o)
    end.

  Definition Lifto (sa: seq T) (o: O) := pair_o (Lift sa) o.
  
  Lemma pair_o_c: forall (spt: seq (T*T)) (o: O) (aa:T*T),
        pair_o (aa::spt) o = (aa,o)::(pair_o spt o).
  Proof.
    by [].
  Qed.

  Lemma pair_o_rc: forall (spt: seq (T*T)) (o: O) (aa:T*T),
        pair_o (rcons spt aa) o = rcons (pair_o spt o) (aa, o).
  Proof.
    by elim => [// | aa1 p Hr] o aa; rewrite rcons_cons //= Hr.
  Qed.

  Lemma pair_o_last: forall (spt: seq (T*T)) (o: O) (aa:T*T),
     last (aa,o) (pair_o spt o) = ((last aa spt), o).
  Proof.
    by elim => [// | aa1 p Hr] o aa //=.
  Qed.

  Lemma pair_o_head: forall (spt: seq (T*T)) (o: O) (aa:T*T),
     head (aa,o) (pair_o spt o) = ((head aa spt), o).
  Proof.
    by elim => [// | aa1 p Hr] o aa //=.
  Qed.

  Lemma pair_o_iff: forall (spt: seq (T*T)) (o: O),
      pair_o spt o = pair spt (nseq (size spt) o).
  Proof.
    by elim => [ // | pa spt Hr o ];rewrite pair_ch pair_o_c Hr.
  Qed.
  
  Lemma Lifto_c: forall (p:seq T) (o:O) (x y: T),
      Lifto [::x, y & p] o = (x,y,o)::(Lifto [::y & p] o).
  Proof.
    by [].
  Qed.

  Lemma Lifto_crc: forall (p:seq T) (o:O) (x y: T),
      Lifto (x::(rcons p y)) o = (x,(head y p),o)::(Lifto (rcons p y) o).
  Proof.
    by move => p o x y; rewrite /Lifto Lift_crc. 
  Qed.
    
  Lemma Lifto_rcc: forall (p:seq T) (o:O) (x y: T),
      Lifto (rcons (x::p) y) o = rcons (Lifto (x::p) o) (last x p,y,o).
  Proof.
    by move => p o x y; rewrite /Lifto lastI Lift_rcrc pair_o_rc.
  Qed.
    
  Lemma Lifto_rcrc: forall (p:seq T) (o:O) (x y: T),
      Lifto (rcons (rcons p x) y) o =  rcons (Lifto (rcons p x) o) (x,y,o).
  Proof.
    by move => p o x y;rewrite /Lifto Lift_rcrc pair_o_rc. 
  Qed.
    
  Lemma Lifto_last: forall (p:seq T) (o:O) (y z: T),
      last (z, y ,o) (Lifto (rcons p y) o) = (last z p, y,o).
  Proof.
    elim/last_ind => [o y z // | p t Hr o y z].
    by rewrite /Lifto Lift_rcrc pair_o_last !last_rcons.
  Qed.

  Lemma Lifto_last1: forall (p:seq T) (o:O) ( y z: T),
      last (z, head y p,o) (Lifto (rcons p y) o) = (last z p, y,o).
  Proof.
    elim/last_ind => [o y z // | p t Hr o y z].
    by rewrite /Lifto Lift_rcrc pair_o_last !last_rcons.
  Qed.
    
  Lemma Lifto_head: forall (p:seq T) (o:O) (x z: T),
      head (x, z ,o) (Lifto (x::p) o) = (x, head z p, o).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q
        by elim. 
    elim/last_ind => [o x y // | p t Hr o x z].
    by rewrite /Lifto Lift_crc H1. 
  Qed.

  Lemma Lifto_head1: forall (p:seq T) (o:O) (x z: T),
      head (last x p, z ,o) (Lifto (x::p) o) = (x, head z p, o).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q
        by elim. 
    elim/last_ind => [o x y // | p t Hr o x z].
    by rewrite /Lifto Lift_crc H1. 
  Qed.
  
  Lemma Lift_o_cons: forall (p:seq T) (o:O) (x y z: T),
      Lifto (x::(rcons (z::p) y)) o = (x,z,o)::(Lifto (z::(rcons p y)) o).
  Proof.
    move => p o x y z;rewrite Lifto_crc //.
  Qed.
  
  Lemma Lift_o_start_end: forall (p q: seq T) (x y t: T),
    exists (x' y': T) (r: seq (T*T*O)), 
      ((Lifto (x::(rcons p t)) N)++(Lifto (t::(rcons q y)) P))
      = (x,x',N)::(rcons r (y',y,P)).
  Proof.
    elim => [ |x' p Hr q ].
    - elim/last_ind => [x y t | q z Hr x y t]; first by (exists t,t,[::]).
      (exists t,z, (Lifto (t::(rcons q z)) P)).
      by rewrite //= -!rcons_cons Lifto_rcrc !rcons_cons. 
    - elim/last_ind: q x' p Hr => [x p Hr x' y t |q x1 Hr x2 p H1 x y t ].
      + specialize Hr with [::] x y t as [x1 [y1 [r H1]]].
        by (exists x, y1, ((x, x1, N)::r));rewrite //= H1.
      + exists x2, x1, ((Lifto (x2::(rcons p t)) N) ++ (Lifto (t::(rcons q x1)) P)).
        by rewrite rcons_cons Lifto_c -!rcons_cons Lifto_rcrc -rcons_cat.
  Qed.
  
End Seq_lifto. 

Section Active_relation.
  (** * D_U and active relation *)
  
  Variables (T: Type) (ptv: T*T).
  Variables (W: set T) (E: relation T).
  
  Definition R_o (o:O):= match o with | P => E | N=> E.-1 end.

  Lemma R_o': forall (o:O) (xy: T*T),
      R_o o xy <-> match o with | P => E xy | N=> E.-1 xy end.
  Proof.
    by move => o xy; case: o.
  Qed.

  (** increase active path by left addition *)
  Lemma Active_path_cc: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (y: T),
      Active_path W E [:: eo1, eo2 & p] eo1.1.1 y
      <-> Active_path W E [:: eo2 & p] eo2.1.1 y /\ ActiveOe W E (eo1, eo2).
  Proof.
    elim => [ | eo3 p _] eo1 eo2 y. 
    - split.
      + by move => [_ [/= -> /allL0' H3]];move: (H3) => /ActiveOe_Oedge [_ H4].
      + by move => [[_ [<- H3]] /inP H4] /=; rewrite allL0.
    - split.
      by move => [H2 [/= H3 /= /allL_c/andP [/inP H4 H5]]] //.  
      by move => [[_ [H3 H4]] /inP H5] /=;
                  rewrite allL_c;split;[| split;[| apply /andP]].
  Qed.
  
  Lemma Active_path_cc_ht: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path W E [:: eo1, eo2 & p] x y -> 
      x = eo1.1.1 /\ y = (last eo2 p).1.2.
  Proof.
    by move => p eo1 eo2 x y [H1 [H2 _]].
  Qed. 
  
  Lemma Active_path_cc_a: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path W E [:: eo1, eo2 & p] x y -> ActiveOe W E (eo1, eo2) .
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_cc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_cc [_ H1].
  Qed.
  
  Lemma Active_path_crc: forall  (p: seq (T*T*O)) (eo1 eo2: T*T*O),
      Active_path W E (eo1::(rcons p eo2)) eo1.1.1 eo2.1.2
      <-> allL (ActiveOe W E) p eo1 eo2.
  Proof.
    elim => [ | eo p H1] eo1 eo2;
           first by split;[move => [_ [_ /= H2]] |move => H1;split;[ |split]].
    split; rewrite rcons_cons.
    move => /Active_path_cc [H2 /inP H3]. 
    by rewrite allL_c; apply/andP; split;[ | apply H1].
    by move => H2;split;[ | split;[ rewrite last_rcons | rewrite belast_rcons last_rcons]].
  Qed.
  
  Lemma Active_path_crc_ht: forall  (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path W E (eo1::(rcons p eo2)) x y -> eo1.1.1 = x /\  eo2.1.2 = y.
  Proof.
    move => p eo1 eo2 x y;rewrite headI;move => [H1 [H2 _]].
    by elim: p H2 => [ //= | a p _ //=]; rewrite last_rcons.
  Qed.
  
  Lemma Active_path_crc_a: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path W E (eo1::(rcons p eo2)) x y
      -> ActiveOe W E (eo1, (head eo2 p)) /\ ActiveOe W E ((last eo1 p), eo2).
  Proof.
    elim => [eo1 eo2 x y [_ [/= _ /allL0' H4]] // | eo3 p H1 eo1 eo2 x y].
    rewrite rcons_cons. move => H2.
    pose proof Active_path_cc_ht H2 as [H3 H4].
    pose proof Active_path_cc_a H2 as H5.
    move: H2;rewrite H3 Active_path_cc;move => [H6 H7].
    apply H1 in H6 as [H6 H8].
    by split;[ | rewrite last_cons].
  Qed.
  
  Lemma Active_path_rcrc: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O),
      Active_path W E (rcons (rcons p eo1) eo2) (head eo1 p).1.1 eo2.1.2
      <-> Active_path W E (rcons p eo1) (head eo1 p).1.1 eo1.1.2
        /\ ActiveOe W E (eo1, eo2).
  Proof.
    elim => [ | eo p H1] eo1 eo2.
    - split. 
      by move => [_ [_ /= /allL0' H3]];move: (H3) => /ActiveOe_Oedge [H4 _ /=].
      by move => [_ H2] /=;rewrite allL0'. 
    - 
      rewrite !rcons_cons.
    rewrite Active_path_crc.
    split. 
    move => /allL_rc/andP [/inP H2 H3].
    by rewrite Active_path_crc.
    rewrite Active_path_crc. move => [H2 /inP H3].
    rewrite allL_rc. 
    by apply/andP.
  Qed.

  Lemma Active_path_rcrc_ht: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path W E (rcons (rcons p eo1) eo2) x y 
      -> x = (head eo1 p).1.1 /\ y= eo2.1.2.
  Proof.
    elim => [ | eo p H1] eo1 eo2 x y; first by move => [H1 [H2 _]]; split.
    by rewrite !rcons_cons => /Active_path_crc_ht [H2 H3].
  Qed.

  Lemma Active_path_rcrc_a: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path W E (rcons (rcons p eo1) eo2) x y 
      -> ActiveOe W E (eo1, eo2).
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_rcrc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_rcrc [_ H1].
  Qed.

  Lemma Active_path_rc_hto: forall (p: seq (T*T*O)) (eo1: T*T*O) (x y: T),
      Active_path W E (rcons p eo1) x y ->
      x = (head eo1 p).1.1 /\ y = eo1.1.2 
      /\ Oedge E eo1 /\ Oedge E (head eo1 p).
  Proof.
    elim => [eo1 x y [H2 [H3 H4]] // | eo2 p _ eo1 x y H1]. 
    pose proof Active_path_crc_ht H1 as [H2 H3];
    pose proof Active_path_crc_a H1 as H4.
    by move: H4; rewrite ActiveOe_iff => [[[H4 _] [_ [H8 _]]]].
  Qed.
  
  Lemma Active_path_c_hto: forall (p: seq (T*T*O)) (eo1: T*T*O) (x y: T),
      Active_path W E (eo1::p) x y -> 
      x = eo1.1.1 /\ y = (last eo1 p).1.2
      /\ Oedge E eo1 /\ Oedge E (last eo1 p).
  Proof.
    elim => [eo1 x y [H1 [H2 H3]] // | eo2 p _ eo1 x y H1]. 
    pose proof Active_path_cc_ht H1 as [H2 H3].
    pose proof Active_path_cc_a H1 as H4.
    move: H4; rewrite  ActiveOe_iff => [[H4 [H5 _]]].
    rewrite lastI in H1.
    by pose proof Active_path_rc_hto H1 as [_ [_ [H8 _]]]. 
  Qed.
  
  Lemma Active_path_split: forall (p q: seq (T*T*O)) (eop eoq: T*T*O) (x y: T),
      Active_path W E ((rcons p eop)++ eoq::q) x y
      -> Active_path W E (rcons p eop) x eop.1.2
        /\ Active_path W E (eoq::q) eoq.1.1 y
        /\ ActiveOe' W E (eop, eoq).
  Proof.
    elim => [ q eop eoq x y // | z p Hr q eop eoq x y ].
    - rewrite cat_rcons cat0s => H1.
      pose proof Active_path_cc_ht H1 as [H2 _].
      pose proof Active_path_cc_a H1 as H3. 
      move: H3; rewrite  ActiveOe_iff => [[H3 _]].
      by move: H1; rewrite H2 Active_path_cc ActiveOe_iff; move => [H4 H5];split.
    - elim/last_ind: q Hr eop eoq x y.
      + move => _ eop eoq x y.
        rewrite -cat_rcons cats0 => H1.
        pose proof Active_path_rcrc_ht H1 as [H2 H3].
        move: H1; rewrite H2 H3 Active_path_rcrc; move => [H4 H5]. 
        rewrite ActiveOe_iff in H5.
        by pose proof H5 as [H6 [H7 _]].
      + move => q1 t _ H1 eo1 eo2 x y H3.
        rewrite rcons_cons cat_cons -rcons_cons -rcons_cat in H3.
        pose proof Active_path_crc_ht H3 as [H4 H5].
        move: H3; rewrite -H4 -H5.
        move => /Active_path_crc /allL_cat/andP [H6 /allL_c/andP [/inP H7 H8]]. 
        by rewrite rcons_cons Active_path_crc Active_path_crc -ActiveOe_iff .
  Qed.
  
  Lemma Active_path_cat: forall (p q: seq (T*T*O)) (eop eoq: T*T*O) (x y z: T),
      ActiveOe W E (eop, eoq)
      /\ Active_path W E (rcons p eop) x y 
      /\ Active_path W E (eoq::q) y z
      -> Active_path W E (rcons p eop++ eoq::q) x z.
  Proof.
    elim. 
    - move => q eop eoq x y z [H1 [H2 H3]].
      have -> : rcons [::] eop ++ eoq :: q = [:: eop, eoq & q] by [].
      pose proof Active_path_rc_hto H2 as [H4 _].
      pose proof Active_path_c_hto H3 as [H6 _].
      by rewrite H4 Active_path_cc -H6.
    - move => eo1 p1 Hr q eop eoq x y z [H1 [H2 H3]]. 
      rewrite rcons_cons cat_cons.
      rewrite rcons_cons in H2.
      elim/last_ind: q Hr H1 H2 H3.
      + move => _ /inP H1 H2 H3.
        pose proof Active_path_crc_ht H2 as [H4 H5].
        have [H7 H8]: y = eoq.1.1 /\ z = eoq.1.2 by move: H3 => [H3 [H3' _]].
        rewrite -H4 -H5 Active_path_crc in H2.
        rewrite cats1 -H4 H8 Active_path_crc allL_rc. 
        by apply/andP.
      + move => q1 eoq1 _ _ /inP H2 H3 H4.
        pose proof Active_path_crc_ht H3 as [H5 H6].
        pose proof Active_path_crc_ht H4 as [H7 H8].
        rewrite -H5-H6 Active_path_crc in H3.
        rewrite -H7 -H8 Active_path_crc in H4.
        rewrite -rcons_cons -{1}cat_rcons -/rcons -rcons_cat.
        rewrite -H5 -H8 Active_path_crc allL_cat. 
        apply/andP. rewrite allL_rc.
        split. by apply/andP. by [].
  Qed.

  Lemma Active_path_iff: forall (p q: seq (T*T*O)) (eop eoq: T*T*O) (x y z: T),
      ActiveOe W E (eop, eoq)
      /\ Active_path W E (rcons p eop) x y 
      /\ Active_path W E (eoq::q) y z
      <-> Active_path W E (rcons p eop++ eoq::q) x z /\ y= eop.1.2.
  Proof.
    move => p q eop eoq x y z.
    split => [ [H1 [H2 H3]] | [H1 H2]].
    - pose proof Active_path_rc_hto H2 as [_ [H4 _]].
      by split;[apply Active_path_cat with y | ].
    - pose proof Active_path_split H1 as [H3 [H4 H5]].
      rewrite ActiveOe_iff.
      pose proof H5 as [_ [H7 [H8 _]]].
      by split;[ | split;[rewrite H2 | rewrite H2 H8]].
  Qed.
  
  Lemma Active_path_cat': forall (p q: seq (T*T*O)) (x y z: T),
      (exists (p' q': seq (T*T*O)), exists (eop eoq: T*T*O),
          p = rcons p' eop /\ q = eoq::q' /\  ActiveOe W E (eop, eoq))
      /\ Active_path W E p x y 
      /\ Active_path W E q y z
      -> Active_path W E (p++q) x z.
  Proof.
    move => p q x y z [[p1 [q1 [eop [eoq [H1 [H2 H3]]]]]] [H4 H5]].
    by rewrite H1 H2; apply Active_path_cat with y; rewrite -H1 -H2.
  Qed.

  
  Section Active_path_unique. 

    (** * If there exists an active path from x to y there exists a walk from x to y
        we just prove that when a variable is repeated twice we can shorten the
        active path * to prove the general property, we have maybe to switch from
        Type to eqType to use unique * in seq ?  *)
    
    Lemma Oedge_Fset:  forall (u v: T), Oedge E (u,v, P) /\ E.*#W v -> E.*#W u.
    Proof.
      move => u v [H1 H2]. 
      move: H2 => [w [H2 H3]].
      have H4: (E `;` E.* ) (u,w) by (exists v).
      have H5:  (E.+ `<=` E.*) by apply clos_t_clos_rt.
      have H6: E.* (u, w) by rewrite r_clos_rt_clos_t in H4 ;apply H5 in H4.
      by (exists w).
    Qed.
  
    Lemma Active_path_Fset:  forall (p: seq T) (x y: T),
        Active_path W E ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ E.*#W (last y p) -> E.*#W x. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        move => x y [[_ [_ H2]] H3].
        by apply Oedge_Fset with y.
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc ActiveOe_iff. 
        move => [[H1 H2] H3].
        have H4: E.*#W y by apply Hr with z.
        move: H2 => [H2 _].
        by apply Oedge_Fset with y.
    Qed.
    
    Lemma Active_path_Fset':  forall (p: seq T) (x y: T),
        Active_path W E ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ E.*#W (last y p) -> E.*#W y. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        by move => x y [[_ [_ H2]] H3].
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc ActiveOe_iff.
        move => [[H1 H2] H3].
        have H4: E.*#W z by apply Hr with y.
        move: H2 => [_ [H2 _]].
        by apply Oedge_Fset with z.
    Qed.
    
    Lemma Active_path_shorten_L1: forall (p: seq (T*T*O)) (x y z u v w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,v,N)) (v,w,N))] x w
        -> exists (q: seq T), Active_path W E (Lifto [::x,y & q] P) x (last y q) 
                        /\ (Fset E.* W) (last y q).
    Proof. 
      elim => [x y z u v w| ].
      - rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons Active_path_rcrc.
        have -> : [:: (x, y, P); (y, z, P)] = rcons [:: (x, y, P)]  (y, z, P) by [].
        rewrite Active_path_rcrc /head ActiveOe_iff.
        move => [[H1 [H'2 [H'3 [/ChrelO_eq H'4 H'5]]]] [H3 [H4 [_ H6]]]].
        by (exists [::z]).
      - move => [[t s] o] p Hr x y z u v w.
        rewrite rcons_cons rcons_cons Active_path_cc ActiveOe_iff.
        elim: p Hr.
        + move => Hr [H1 H2].
          move: (H1);
            rewrite Active_path_cc ActiveOe_iff => [[_ [_ [_ [/ChrelO_eq H3 _]]]]];
                                               rewrite <- H3 in *.
          elim: o H1 => [ /Hr [q [H1 H4]] | ].
          ++ exists [:: z & q].
             by rewrite Lifto_c Lifto_c Active_path_cc  -Lifto_c /last_cons 
                                                           ActiveOe_iff.
          ++ exists [::z].
             move: H1 => /Active_path_cc H1. 
             move: H1; rewrite  ActiveOe_iff => [[H1 [_ [_ [_ H7]]]]].
             move: (H2) => [H2' [H2'' _]].
             rewrite !Lifto_c Active_path_cc -Lifto_c ActiveOe_iff /last.
             by split.
        + move => [[a b] o2] p _ H1 H2.
          move: (H2);rewrite Active_path_cc rcons_cons rcons_cons ActiveOe_iff ;
            move => [[_ [_ [_ [/ChrelO_eq H6 _]]]] _].
          rewrite <- H6 in *; clear H6.
          elim: o H2 => [[H2 H3] | ].
          ++ apply H1 in H2;move:H2 => [q H2].
             exists [::z].
             move: H2;rewrite Lifto_c => [[H2 H4]].
             rewrite /Lifto /Lift /pair_o.
             rewrite Active_path_cc last_cons /last ActiveOe_iff .
             move: (H3) => [H5 [H6 _]].
             specialize Active_path_Fset' with q y z => H7.
             by split;[split | apply H7].
          ++ move => [H2 H3].
             pose proof H2 as H5.
             rewrite Active_path_cc  ActiveOe_iff in H2.
             rewrite Active_path_crc in H2.
             move: H2; rewrite ActiveOe_iff => [[H2 [_ [_ [_ H8 ]]]]].
             exists [::z];rewrite last_cons /last.
             split. 
             by rewrite /= allL0' ActiveOe_iff.
             by [].
    Qed.
    
    Lemma Active_path_shorten_L2: forall (p: seq (T*T*O)) (x y z u w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> E.*#W y. 
    Proof. 
      move => p x y z u w H1.
      pose proof Active_path_shorten_L1 H1 as [q H2].
      rewrite Lifto_c in H2.
      by apply  Active_path_Fset' in H2.
    Qed.

    Lemma Active_path_shorten_L3: forall (p: seq (T*T*O)) (x y z u w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> ActiveOe' W E ((x,y,P), (y,w,N)).
    Proof. 
      move => p x y z u w H1.
      move: (H1) => /Active_path_shorten_L2 H2.
      pose proof Active_path_cc_a H1 as H3. 
      move : H3; rewrite ActiveOe_iff => [[H3 _]].
      move: (H1); rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons. 
      move => /Active_path_rcrc_a H4. 
      move: H4; rewrite ActiveOe_iff =>[[_ [H4 _]]].
      by [].
    Qed.
    
    (* the only complex case is (o1 o2 o3 o4)= ( P P N N) which was is treated 
       in the previous lemmata *) 
    Lemma Active_path_shorten: forall (p: seq (T*T*O)) (x y z u w: T) (o1 o2 o3 o4:O) ,
        Active_path W E [::(x,y,o1),(y,z,o2) & (rcons (rcons p (u,y,o3)) (y,w,o4))] x w
        -> ActiveOe' W E ((x,y,o1), (y,w,o4)).
    Proof. 
      move => p x y z u w o1 o2 o3 o4 H1. 
      move: (H1); rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons. 
      move => /Active_path_rcrc_a H2. 
      move: H2; rewrite ActiveOe_iff => [[_ [H2 [_ H3]]]].
      move: o1 o2 o3 o4 H1 H2 H3.
      case; case; case; case;
        move => H1 H2 H3;
               pose proof Active_path_cc_a H1 as H4;
               move: H4; rewrite ActiveOe_iff =>[[H4 [_ [_ H5]]]];
               move: H5 => //= H5;move: H3 => //= H3.
      by apply Active_path_shorten_L3 with p z u.
    Qed.
    
  End Active_path_unique. 

End Active_relation.

Section Active. 
  (** * The D_separated and Active relation as a relation on TxT *)
  Variables (T: Type). 

  (* begin snippet Dseparated:: no-out *)  
  Definition D_separated (W: set T) (E: relation T) (x y: T) := 
    ~(exists (p: seq (T*T*O)), Active_path W E p x y).
  (* end snippet Dseparated *)  

  (* begin snippet Active:: no-out *)  
  Definition Active (W: set T) (E: relation T) (x y: T) :=
   (exists (p: seq (T*T*O)), Active_path W E p x y).
  (* end snippet Active *)  

  Lemma Deployment_to_Active_path:
    forall (W: set T) (E: relation T) (p: seq T) (x y: T) (o:O),
      p [\in] W.^c /\ allL (R_o E o) p x y 
      <-> Active_path W E (Lifto (x::(rcons p y)) o) x y.
  Proof.
    split.
    + elim: p x y => [x y [_ /allL0' /R_o' _] // | ]. 
      move => x1 p _ x y. 
      rewrite allset_consb allL_c. 
      move => [ /andP [H2 H'2] /andP [/inP H3 H4]].
      rewrite Lifto_crc Lifto_rcc Active_path_crc /=. 
      elim: p x x1 H3 H2 H'2 H4 => [x x1 H3 /inP H1 _ /allL0' H4 // | ].  
      ++ by rewrite allL0 /=; apply mem_set; split;case: o H3 H4 => /R_o' H3 /R_o' H4.
      ++ move => z p H1 x1 x H3 /inP H2 /allset_cons [H4 H4'] /allL_c/andP [/inP H5 H6] /=. 
         rewrite Lifto_c allL_c;apply /andP;split; last first. 
         by apply: (H1 x z H5 _ H4' H6); apply mem_set. 
         clear H1 H6;apply mem_set;rewrite ActiveOe_o /Oedge.
         by case: o H3 H5 => /R_o' H3 /R_o' H5. 
    + elim: p x y;
        first by move => x y //= [_ [_ H]];
                        split; elim: o H => H;[ | | apply /allL0'/R_o' | apply /allL0'/R_o'].
      
      move => z p H1 x y; rewrite Lift_o_cons;elim: p x y H1. 
      move => x y H1 /Active_path_cc H2. 
      move: H2; rewrite ActiveOe_iff => [[H2 [H3 [H4 [H5 H6]]]]].
      elim: o H1 H2 H3 H4 H5 H6 => /= H1 H2 H3 H4 H5 H6.
      rewrite andbT.
      split. apply mem_set. by []. rewrite /allL /=.
      by move: H3 => /inP ->;move: H4 => /inP ->.
      rewrite andbT.
      split. apply mem_set. by []. rewrite /allL /=.
      by move: H3 => /inP ->;move: H4 => /inP ->.
      (* size p >= 2 *)
      move => t p _ x y H2;rewrite Lift_o_cons;move => /Active_path_cc [/H2 [H3 H5] H4].
      split.
        rewrite allset_cons andC. 
        rewrite ActiveOe_iff in H4.
          split;[ | move: H4 => [_ [_ [_ H4]]]].
        by elim: o H2 H4 H5 => _ H4 H5.
        by elim: o H2 H4 H5 => _ /= H4 H5.
        rewrite ActiveOe_iff in H4.
        rewrite allL_c H5 andbT.
        by elim: o H2 H4 H5 => _ [/= /inP H4 _] _ /=.
  Qed.
  
  Lemma Deployment_to_Active: forall (W: set T) (E: relation T) (p: seq T) (x y: T),
      p [\in] W.^c /\ allL E p x y -> Active W E x y.
  Proof.
    move => W E p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) P); apply Deployment_to_Active_path;split.
  Qed.

  Lemma Deployment_inv_to_Active: forall (W: set T) (E: relation T) (p: seq T) (x y: T),
      p [\in] W.^c /\ allL E.-1 p x y -> Active W E x y.
  Proof.
    move => W E p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) N); apply Deployment_to_Active_path;split.
  Qed.

End Active. 

Section PathRel_Examples.
  (** * Utilities *)
  
  Variables (T: Type) (E: relation T) (W: set T).

  Lemma clos_t_to_paths_l : forall (x y: T),
      (Δ_(W.^c) `;` E).+ (x, y) ->
      (exists (p: seq T), (x::p) [\in] W.^c /\ allL E p x y
                     /\ (x::p) [\in] ((Δ_(W.^c) `;` E).+)#_(y)).
  Proof.
    move => x y; rewrite {1}TCP'; move => [p /= H1]; exists p.
    move: (H1) => /allL_WS_iff/andP [H2 H2'].
    apply allL_All in H1;apply allset_cons in H1;move: H1=> [/inP H1 H1'].
    by rewrite -allset_consb H1 H1' andbT.
  Qed.
  
  Lemma clos_t_to_paths_r : forall (x y: T),
      (E `;` Δ_(W.^c)).+ (x, y) ->
      (exists (p: seq T), (rcons p y) [\in] W.^c /\ allL E p x y
                     /\ (y::(rev p)) [\in] ((Δ_(W.^c) `;` E.-1).+)#_(x)).
  Proof.
    move => x y; rewrite {1}TCP'; move  => [p H1]; exists p.
    rewrite allL_rev inverse_compose DeltaE_inverse /= in H1.
    move: (H1) => /allL_WS_iff/andP /= [/andP [/inP H2 H3] H2'].
    apply allL_All in H1;apply allset_cons in H1;move: H1=> [/inP /= H1 H1'].
    by rewrite H1 H1' andbT allL_rev H2' allset_rcons allset_rev H3. 
  Qed.
  
End PathRel_Examples.
