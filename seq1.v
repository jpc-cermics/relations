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
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
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

(* begin snippet all_notation:: no-out *)  
Notation "p [\in] X" := (all (fun x => x \in X) p). 
(* end snippet all_notation *)  

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
  
  (* begin snippet RPath:: no-out *)  
  Notation "s [Suc\in] R" := (RPath R s).
  (* end snippet RPath *)  
      
End Suc_def. 

Notation "s [Suc\in] R" := (RPath R s) (at level 4, no associativity). 

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
    have H2: 0 < size s by apply leq_ltn_trans with 1.  
    pose proof seq_rc H2 as [q [x H3]].
    have H4: 0 < size q by rewrite H3 size_rcons ltnS in H1.
    pose proof seq_rc H4 as [r [z H5]].
    by exists r,z,x;rewrite H3 H5.
  Qed.
  
  Lemma seq_crc: forall (s: seq T), 
      1 < size s -> exists (s':seq T) (x y:T), s = x::(rcons s' y).
  Proof.
    move => s H1.
    have H2: 0 < size s by apply leq_ltn_trans with 1.  
    pose proof seq_rc H2 as [r [y H3]].
    have H4: 0 < size r by rewrite H3 size_rcons ltnS in H1.
    pose proof seq_c H4 as [q [x H5]].
    by exists q,x,y;rewrite H3 H5.
  Qed.
  
  Lemma seq_cc: forall (s: seq T), 
      1 < size s -> exists (s':seq T) (x y:T), s = [::x,y &s'].
  Proof.
    move => s H1.
    have H2: 0 < size s by apply leq_ltn_trans with 1.  
    pose proof seq_c H2 as [r [y H3]].
    have H4: 0 < size r by rewrite H3 ltnS in H1.
    pose proof seq_c H4 as [q [x H5]].
    by exists q,y,x;rewrite H3 H5.
  Qed.

  Lemma seq_cc': forall (s: seq T), 
      1 < size s <-> exists (s':seq T) (x y:T), s = [::x,y &s'].
  Proof.
    move => s.
    - split => [H1 | ].
      have H2: 0 < size s by apply leq_ltn_trans with 1.  
      pose proof seq_c H2 as [r [y H3]].
      have H4: 0 < size r by rewrite H3 ltnS in H1.
      pose proof seq_c H4 as [q [x H5]].
      by exists q,y,x;rewrite H3 H5.
    - by move => [s' [x [y -> /=]]].
  Qed.
  
  Lemma seq_1: forall (s: seq T), 
      size s = 1 <-> exists (x:T), s = [::x].
  Proof.
    split; last by move => [x H1];rewrite H1.
    elim:s => [// | x s H1 /= H2].
    by (have -> : s = [::] by apply size0nil; apply succn_inj in H2);(exists x).
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
    + have H2: size(s) > 0.  by rewrite H1. 
      pose proof (seq_c H2) as [q [x H3]].
      rewrite H3 /= in H1. apply succn_inj in H1.
      by exists q, x. 
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
  
  Lemma UnLift_c: forall (spt: seq (T * T)) (x y z: T),
      UnLift ((x, y) :: spt) z = [::x & UnLift spt y].
  Proof.
    by [].
  Qed.

  Lemma UnLift_sz: forall (spt: seq (T * T)) (z: T),
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

  Lemma Lift_sz3: forall (st:seq T),
      size(Lift st) > 0 -> size(st) = size(Lift st) +1. 
  Proof.
    move => st H1.
    have H2:  size st >1. by apply Lift_sz2.
    have H3:  size (Lift st) = (size st) -1 by apply Lift_sz.
    rewrite H3 subn1 addn1. 
    by have ->: (size st).-1.+1 = size st by apply: (ltn_predK H2).
  Qed.

  Lemma Lift_szn': forall (st:seq T) (n:nat),
      size(Lift st) = n.+1 <-> size (st) = n.+2.
  Proof.
    move => st n.
    split => H1.
    - have H2: size(Lift st) > 0 by rewrite H1.
      have H3: size(st) > 1 by rewrite -Lift_sz2.
      move: (H3) => /Lift_sz H4.
      have H5: ((size st).-1)%N  = n.+1 by rewrite -subn1 -H4.
      have H6: (size st).-1.+1 = size(st) by apply: (ltn_predK H3).
      by rewrite -H5 -[in LHS]H6.
    - have H3: size(st)> 1 by rewrite H1.
      pose proof (Lift_sz H3) as H4.
      by move: H4;rewrite H1 subn1 /=.
  Qed.
  
  Lemma Lift_szn: forall (st:seq T) (n:nat),
      size(Lift st) > n <-> size (st) > n.+1.
  Proof.
    move => st n.
    split => H1.
    - have H3: size(st)> 1 by rewrite -Lift_sz2 ;apply leq_ltn_trans with n.
      pose proof Lift_sz H3 as H4.
      by move: H1;rewrite H4 -ltn_predRL -subn1.
    - have H3: size(st)> 1 by apply leq_ltn_trans with n.+1.
      pose proof Lift_sz H3 as H4.
      by rewrite H4 subn1 ltn_predRL.
  Qed.

End Lift_props. 

Section allset.
  (** * utilities for st [\in] X, X: set T *)

  Variables (T: Type).

  (* begin snippet Sn:: no-out *)  
  Definition Sn (n: nat) (D: set T):= [set st| st [\in] D/\size(st)=n].
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
    pose proof intersectionSr.
    have H1: (X `&` Y) `<=` X by rewrite /setI /mkset /subset => [t [? ?]].
    have H2: (X `&` Y) `<=` Y by rewrite /setI /mkset /subset => [t [? ?]].
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

Notation "[L: x ; st ; y `\in` E ]" := ((Lift (x::(rcons st y))) [\in] E).

Section allset_Lifted.
  (** * properties of st [L\in] R for st: seq T  *)
  (** * with specified endpoints *)
  
  Variables (T: Type).
  Definition allL (E: relation T) (st: seq T) (x y:T) := [L: x; st ;y `\in` E].
  
  Lemma allL0 : forall (E: relation T) (x y : T),
      allL E [::] x y = ((x,y) \in E).
  Proof.
    by move => E x y;rewrite /allL Lift_c /andP /= andbT. 
  Qed.

  Lemma allL0' : forall (E: relation T) (x y : T),
      allL E [::] x y <-> E (x,y).
  Proof.
    by move => E x y;rewrite allL0;split=> [/set_mem H1 // | /inP H1]. 
  Qed.
  
  Lemma allL_c: forall (E: relation T) (st: seq T) (x y z: T),
      allL E (z::st) x y <-> ((x, z) \in E) && allL E st z y.
  Proof.
    by move => E st x y z;split;[rewrite /allL rcons_cons Lift_c allset_cons |].
  Qed.

  Lemma allL_rc: forall (E: relation T) (st: seq T) (x y z: T),
      allL E (rcons st z) x y <-> ((z,y) \in E) && allL E st x z.
  Proof.
    move => E st x y z;split.
    by rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons;move => [-> /inP ->].
    by move => /andP [/inP ? ?];rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons. 
  Qed.
  
  Lemma allL_cat: forall (E: relation T) (st st': seq T) (x y z: T),
      allL E ((rcons st y) ++ st') x z <-> allL E st x y && allL E st' y z.
  Proof.
    move => E st st' x y z.
    rewrite /allL cat_rcons rcons_cat rcons_cons -cat_rcons Lift_cat_crc allset_cat.
    by split => [ [? ?] | /andP [? ?]];[apply/andP |].
  Qed.
  
  Lemma allL_subset: forall (E R: relation T) (st: seq T) (x y: T),
      (E `<=` R) -> allL E st x y -> allL R st x y.
  Proof.
    by move => E R st x y H1 H2;apply allset_subset with E.
  Qed.
  
  Lemma allL_WS_iff: forall (E: relation T) (W:set T) (st: seq T) (x y: T),
      allL (Δ_(W.^c) `;` E) st x y <-> (x::st) [\in] W.^c && allL E st x y.
  Proof.
    move => E W st x y.
    have H1: (L_(W.^c) `&` E) `<=` E by apply intersectionSr.
    have H2: (L_(W.^c) `&` E) `<=` L_(W.^c) by apply intersectionSl.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) E) as H4.    
    rewrite DeltaLco /allL allset_I.
    by split => /andP [/allset_Lr H5 H6];[apply /andP | apply /andP].
  Qed.
  
  Lemma allL_SW_iff: forall (E: relation T) (W:set T) (st: seq T) (x y: T),
      allL (E `;` Δ_(W.^c)) st x y <-> (rcons st y) [\in] W.^c && allL E st x y.
  Proof.
    move => E W st x y.
    have H1: (E `&` L_(W.^c)) `<=` E by apply intersectionSl.
    have H2: (E `&` L_(W.^c)) `<=` L_(W.^c) by apply intersectionSr.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) E) as H4.    
    rewrite DeltaRco /allL allset_I; split => /andP [H5 H6]. 
    by rewrite allset_Rr in H6; apply /andP; split. 
    by apply /andP; split;[| rewrite allset_Rr].
  Qed.
  
  Lemma allL_rev: forall (E: relation T) (st: seq T) (x y: T),
      allL E st x y <->  allL E.-1 (rev st) y x.
  Proof.
    move => E st x y. 
    have H1: (y :: rcons (rev st) x) = rev (x::(rcons st y)) 
      by rewrite rev_cons rev_rcons -rcons_cons.
    by rewrite /allL allset_rev allset_inv H1 Lift_rev.
  Qed.
  
  Lemma allL_All: forall (E: relation T) (st: seq T) (x y: T),
      allL E st x y -> (x::st) [\in] (E.+)#_(y).
  Proof.
    move => E st x y.
    elim: st x => [x | z st Hr x].
    by rewrite /allL /= => /andP [/inP H1 _];
                          apply /andP;split;[apply mem_set;apply Fset_t1|].
    rewrite allL_c => /andP [/inP H1 /Hr H2].
    move: (H2);rewrite allset_cons => [[H3 H4]].
    by rewrite allset_cons;split;[ apply Fset_t2; exists z |].
  Qed.
  
End allset_Lifted.

Section Suc_as_Lift. 
  (** * st [L\in] R <-> st [Suc\in] R *)
    
  Variables (T: Type).

  (* begin snippet RPath_equiv:: no-out *)  
  Lemma RPath_equiv: forall (R:relation T) (st: seq T), st [L\in] R <-> st [Suc\in] R.
  (* end snippet RPath_equiv *)  
  Proof.
    move => R st.
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
  Definition Chrel {T:Type} :=[set sptt: (T*T)*(T*T)| (sptt.1).2 = (sptt.2).1].
  (* end snippet Chrel *)  
  
  Lemma Lift_Lift: forall (st:seq T), (Lift st) [L\in] Chrel. 
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

  (* begin snippet Lift_Suc:: no-out *)  
  Lemma Lift_Suc: forall (st:seq T), (Lift st) [Suc\in] Chrel. 
  (* end snippet Lift_Suc *)  
  Proof.
    by move => st; rewrite -RPath_equiv; apply Lift_Lift.
  Qed.
  
  (* begin snippet DI:: no-out *)  
  Definition D := [set st:seq T | size(st) > 1].
  Definition I := [set spt:seq (T*T) | size(spt) > 0 /\ spt [Suc\in] Chrel].
  (* end snippet DI *)
  
  Lemma Lift_image: forall (st: seq T),
      st \in D -> (Lift st) \in I.
  Proof.
    rewrite /D /I /mkset; move => st /inP H1;rewrite inP Lift_sz2.
    by split;[ | rewrite -RPath_equiv;apply Lift_Lift].
  Qed.
  
  Lemma UnLift_image: forall (spt: seq (T*T)),
      spt \in I -> (forall (z:T), (UnLift spt z) \in D).
  Proof.
    move => st /inP [H1 _] z; apply inP.
    rewrite /D /mkset.
    elim: st H1 => [// | [x y] st _ /= _].
    elim: st y => [ // | [x' y'] st' _ z'].
    by rewrite UnLift_c /=. 
  Qed.

  Lemma Lift_UnLift: forall (spt: seq (T*T)),
      spt \in I -> (forall (z:T), Lift (UnLift spt z) = spt).
  Proof.
    move => st /inP [H1 H2] z; apply inP.
    elim: st H1 H2 => [// | [x y] st Hr H1 H2].
    rewrite UnLift_c.
    elim: st y x Hr H1 H2 => [y x _ _ _ /= // | [x' y'] st Hr y x H1 H2 H3].
    by apply inP.
    rewrite UnLift_c in H1.
    rewrite UnLift_c Lift_c.
    move: (H3). rewrite -RPath_equiv Lift_c allset_cons => [[H4 H5]].
    move: H4. rewrite /Chrel /mkset => [H4].
    have H6:  (Lift (x' :: UnLift st y'))= ((x', y') :: st)
      by apply inP; apply H1;[ | rewrite -RPath_equiv].
    apply inP. rewrite H6.
    by have -> : y=x' by [].
  Qed.
  
  (* begin snippet Lift_inj:: no-out *) 
  Lemma Lift_inj: forall st st', st \in D -> Lift st = Lift st' -> st = st'.
  (* end snippet Lift_inj *) 
  Proof.
    rewrite /D /mkset.
    move => st q /inP H1 H2.
    move: (H1) => /Lift_sz2 H3. 
    have H4: size(q) > 1. by rewrite -Lift_sz2 -H2. 
    pose proof seq_crc H1 as [r [x [y H5]]].
    pose proof Lift_inv_sz2 H1 as H6.
    pose proof Lift_inv_sz2 H4 as H7.
    by rewrite -(H6 x) -(H7 x) H2. 
  Qed.
  
  Lemma Lift_inj': forall st st',
      st \in D -> st' \in D -> Lift st = Lift st' -> st = st'.
  Proof.
    move => st q /inP H1 /inP H2 H3.
    pose proof seq_crc H1 as [_ [x _]].
    have H4: UnLift (Lift st) x = UnLift (Lift q) x by rewrite H3.
    pose proof (UnLift_left x H1) as H5.
    pose proof (UnLift_left x H2) as H6.
    by rewrite -H5 -H6 H4.
  Qed.
  
  (* begin snippet Lift_surj:: no-out *) 
  Lemma Lift_surj: forall spt, spt \in I -> exists st, st\in D /\ Lift st=spt. 
  (* end snippet Lift_surj *) 
  Proof.
    move => st H0; move: (H0);rewrite /I /mkset => /inP [H1 H2].
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
    - have H5: ((x, y) :: spt) \in I by rewrite inP /I /mkset -RPath_equiv.  
      pose proof Lift_UnLift H5 as H6.
      by (exists (UnLift ((x, y) :: spt) x));rewrite H6.
    - by move => [st <-]; apply Lift_Lift.
  Qed.
  
  (* begin snippet Lift_lemma:: no-out *)  
  Lemma Lift_lemma:  image [set st | True] (@Lift T) 
                     = preimage (@Lift (T*T)) [set spt| spt [\in] Chrel].
  (* end snippet Lift_lemma *)  
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
  (* begin snippet Epe_Lift:: no-out *)  
  Lemma Epe_Lift: forall (st:seq T), size(st) > 1 -> Epe (Lift st) = Pe st.
  (* end snippet Epe_Lift *)  
  Proof.
    move => st H1; rewrite /Epe /Pe.
    have ->: (head ptv (Lift st)).1 = head ptv.1 st by apply head_Lift.
    have ->: (last ptv (Lift st)).2 = last ptv.1 st by apply last_Lift.
    by [].
  Qed.
  
  Lemma EpeZ_Lift: forall (st: seq T), size(st) > 1 -> Epe1 (Lift st) = Pe st.
  Proof.
    move => st H1;rewrite /Epe1 /Pe. 
    by have ->: (UnLift (Lift st) ptv.1) = st by apply: UnLift_left H1.
  Qed.
  
  Lemma Epe_Epe1: forall (spt: seq (T*T)), 
      size(spt) > 0 -> spt [Suc\in] Chrel -> Epe1 spt = Epe spt.
  Proof.
    move => spt H1 H2.
    have H4: spt \in (@I T) by apply inP.
    pose proof Lift_surj H4 as [st [H5 H6]].
    move: H5 => /inP H5.
    have H7: Epe1 (Lift st) = Pe st by apply EpeZ_Lift.
    have H8: Epe (Lift st) = Pe st by apply Epe_Lift.
    by rewrite -H6 H7 H8.
  Qed.
  
  (* Pe (UnLift spt ptv.1) = Epe spt. *) 
  (* begin snippet Pe_UnLift:: no-out *)  
  Lemma Pe_UnLift: forall (spt: seq (T*T)), 
      size(spt) > 0 -> spt [Suc\in] Chrel -> Pe (UnLift spt ptv.1) = Epe spt.
  (* end snippet Pe_UnLift *)  
  Proof. 
    by move => spt H1 H2; rewrite -Epe_Epe1 /Epe1.
  Qed.

  (** * deployment paths 
   * Lift and UnLift are bijective on deployment path 
   * D_V <-[Lift]-> D_P 
   *) 
  
  (* begin snippet D_P:: no-out *)  
  Definition D_P (R E: relation T):= 
    [set spt| spt \in (@I T) /\ R (Epe1 spt) /\ spt [\in] E ].
  (* end snippet D_P *)  
  
  (* begin snippet D_P_s:: no-out *)  
  Definition D_P_s (x y: T) (E: relation T):= D_P [set (x,y)] E.
  (* end snippet D_P_s *)  

  (* begin snippet D_V:: no-out *)  
  Definition D_V (R E: relation T):=
    [set st| st \in (@D T) /\ R (Pe st) /\ st [Suc\in] E].
  (* end snippet D_V *)  
  
  (* begin snippet D_V_s:: no-out *)  
  Definition D_V_s (x y:T) (E: relation T) := D_V [set (x,y)] E.
  (* end snippet D_V_s *)  
  
  (* begin snippet DP_DV:: no-out *)  
  Lemma DP_DV: forall (R E: relation T), image (D_V R E) (@Lift T) = (D_P R E).
  (* end snippet DP_DV:: no-out *)  
  Proof.
    move => R E.
    rewrite /D_V /D_P /mkset predeqE => q.
    split. 
    - move => [p [/inP H1 [H2 H3]] <-].
      move: (H1) => /Lift_sz2 H1'.
      rewrite /Epe1. 
      have -> : (UnLift (Lift p) ptv.1) = p by apply UnLift_left. 
      rewrite RPath_equiv inP.
      by pose proof Lift_Suc p as H5.
    - move => [/inP [H1 H2] [H3 H4]].
      have H6 : Lift (UnLift q ptv.1) = q  by apply Lift_UnLift;rewrite inP /I. 
      have H7: 1 < size (UnLift q ptv.1) by rewrite -H6 Lift_sz2 in H1.
      rewrite -H6 /=.
      by exists (UnLift q ptv.1);[rewrite -RPath_equiv H6 inP|].
  Qed.
  
  Lemma DV_DP: forall (R E: relation T) (spt: seq (T*T)), 
      spt \in (D_P R E) -> exists st, st \in (D_V R E) /\ Lift st = spt.
  Proof.
    move => R E spt /inP [H1 [H3 H4]].
    move: (H1) => /inP [H1' H2].
    pose proof Pe_UnLift H1' H2 as H5.
    pose proof Epe_Epe1 H1' H2 as H6.
    pose proof UnLift_image H1 ptv.1 as H7.
    pose proof Lift_UnLift H1 ptv.1 as H8.
    exists (UnLift spt ptv.1).
    by rewrite inP /D_V /mkset H5 -H6 -RPath_equiv H8.
  Qed.
  
End Endpoints_and_Deployment.

Section seq_subsets.
  (** * p: seq T, p [\in] X and p [L\in] R] *)

  Variables (T: Type) (R: relation T) (X: set T).
  
  (* begin snippet Rpath_L1:: no-out *)  

  Lemma Rpath_L1: forall (st: seq T), st [\in] X -> st [L\in] (X `*` X). 
  (* end snippet Rpath_L1 *)  
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

Section seq_pairs_subsets.
  (** * p: seq (T*T), p [\in] E and p [L\in] R] *)
  
  Variables (T: Type).

  (* begin snippet Epath_gt:: no-out *)  
  Definition P_gt (n: nat) (E: relation T)  := 
    [set spt | size(spt) > n /\ spt [\in] E /\ spt [Suc\in] Chrel].
  (* end snippet Epath_gt *)  
  
  Definition REpaths (E: relation T) (R: relation (T*T)) := 
    [set spt:seq (T*T) | spt [\in] E /\ spt [L\in] Chrel /\ spt [L\in] R].
  
  Lemma REpath_iff1: forall (E: relation T) (R: relation (T*T)),
      [set spt:seq (T*T) | spt [\in] E /\ spt [L\in] (Chrel `&` R)]
    = [set spt | spt = [::]] 
        `|` [set spt | size(spt) = 1 /\ (spt [\in] E) ] 
        `|` [set spt | size(spt) > 1 /\ spt [L\in] ((E `*` E)`&` (Chrel `&` R))]. 
  Proof.
    by move => E R;rewrite -[RHS]Rpath_iff.
  Qed.

  Lemma REpath_iff2: forall (E: relation T) (R: relation (T*T)),
      [set p:seq (T*T) | p [\in] E /\ p [L\in] (Chrel  `&` R)]
      = [set p | p [\in] E /\ p [L\in] (@Chrel T) /\ p [L\in] R].
  Proof.
    move => E R. rewrite /mkset predeqE => p.
    split => [ [H1 /allset_I/andP [H2 H3]]// | [H1 [H2 H3]] ].
    by rewrite allset_I H1 H2 H3.
  Qed.

End seq_pairs_subsets.
  
Section PathRel.
  (** * transitive closure and paths
   * the main result here is that the relation in AxA obtained 
   * by fun (x y : T) => (exists (p: seq T), AllL E p x y)
   * is the relation E.+ the transitive closure of E 
   *)

  Variables (T: Type) (E: relation T).
  
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
  (* begin snippet TCP:: no-out *)  
  Lemma TCP: E.+ = [set vp | exists p, (Lift (vp.1::(rcons p vp.2))) [\in] E].
  (* end snippet TCP *)  
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

End PathRel.

Section pair. 
  (** * pair sequences *)
  Variables (T: Type).

  (* orientation  *)
  (* begin snippet O:: no-out *)
  Inductive O := | P | N.
  (* end snippet O *)

  (* begin snippet pair:: no-out *)  
  Fixpoint pair (stt: seq (T*T)) (so: seq O) := 
    match stt, so with 
    | (pt)::stt, o::so => (pt,o)::(pair stt so)
    | (pt)::stt, [::] =>  (pt,P)::(pair stt [::])
    | _ , _ => @nil (T*T*O)
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
      size(st) = size (so) -> (pair st so) [Suc\in] (Extend R) <-> st [Suc\in] R.
  Proof.
    move => R st so H1; rewrite -2!RPath_equiv.
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
      stto [Suc\in] (Extend R) <-> (unpair stto).1 [Suc\in] R.
  Proof.
    move => R stto; rewrite -2!RPath_equiv.
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

Section pair_lift1.
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
    fun (oe: T*T*O) => match oe with | (e,P) => E e | (e,N) => E.-1 e end.
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
      -> size (LiftO st so) > 0 /\ (LiftO st so) [Suc\in] ChrelO.
  Proof.
    move => st so H1 H2.
    have H3: size(Lift st) = size so by apply Lift_sz in H1;rewrite H2 addn1 subn1 in H1.
    split; first by rewrite pair_sz1 H3;rewrite H2 addn1 in H1;apply leq_ltn_trans with 0. 
    rewrite /LiftO.
    have -> : (pair (Lift st) so) [Suc\in] (Extend Chrel) 
         <-> (Lift st) [Suc\in] Chrel by  apply pair_L1.
    by rewrite -RPath_equiv Lift_Lift.
  Qed.
  
  Lemma LiftO_right_0: forall (stto:seq (T*T*O)),
      size stto > 0 -> stto [Suc\in] ChrelO 
      -> size (unpair stto).1 > 0 /\ (unpair stto).1 [Suc\in] Chrel.
  Proof.
    move => stto; rewrite -2!RPath_equiv;move => H1 H2.
    split; first by rewrite unpair_sz1.
    pose proof unpair_right stto as H3.
    have H4: (Extend Chrel) = ChrelO by [].
    have H5: size ((unpair stto).1) = size (unpair stto).2 by apply unpair_sz.
    pose proof pair_L1 Chrel H5 as H6.
    by rewrite RPath_equiv -H6 unpair_right H4 -RPath_equiv.
  Qed.
  
  Lemma LiftO_right: forall (t:T) (stto:seq (T*T*O)),
      size stto > 0 -> stto [Suc\in] ChrelO 
      -> LiftO (UnLiftO stto t).1 (UnLiftO stto t).2 = stto. 
  Proof.
    move => t stto H1 H2.
    rewrite /LiftO /UnLiftO /=.
    pose proof LiftO_right_0 H1 H2 as [H3 H4].
    have H5: (unpair stto).1 \in (@I T). by rewrite inP;by split.
    pose proof Lift_UnLift H5 t as H6.
    by rewrite H6 unpair_right.
  Qed.
  
  Lemma Lift_LiftO: forall (st:seq T) (so:seq O), 
      size st > 1 -> size(st) = size(so)+1 -> (LiftO st so) [L\in] ChrelO. 
  Proof.
    move => st so H1 H2.
    pose proof LiftO_image H1 H2 as [H3 H4].
    by rewrite RPath_equiv.
  Qed.
  
  (** * Y_gt and p: seq (T*T*O), p [\in] E and p [L\in] R] *)
  
  (* begin snippet U_gt:: no-out *) 
  Definition U_gt (n: nat) (E: relation T):=
    [set sto | size(sto) > n /\ sto [\in] (Oedge E) /\ (Lift sto) [\in] ChrelO].
  (* end snippet U_gt *)
    
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
  
  (* begin snippet U_ge_1:: no-out *) 
  Definition U_ge_1 (E: relation T):=
    [set sto | sto [\in] (Oedge E) /\  size(sto) > 0 /\ 
                 (Lift sto) [\in] ChrelO].
  (* end snippet U_ge_1 *)
  
  (** * Endpoints in Extended oriented paths *)
  
  (* begin snippet Eope:: no-out *)  
  Definition Eope (stto : seq(T*T*O)) : T*T :=
    ((head (ptv,P) stto).1.1, (last (ptv,P) stto).1.2).
  (* end snippet Eope *)  
  
  (* begin snippet Eope_LiftO:: no-out *)  
  Lemma Eope_LiftO: forall (st:seq T) (so:seq O),
      size(st) > 1 -> size (so) = size st -1 -> Eope (LiftO st so) = Pe ptv st.
  (* end snippet Eope_LiftO *)  
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
  
  (* begin snippet Pe_UnLiftO:: no-out *)  
  Lemma Pe_UnLiftO: forall (stto: seq (T*T*O)), 
      size(stto) > 0 -> stto [Suc\in] ChrelO -> 
      (Pe ptv (UnLiftO stto ptv.1).1) =  Eope stto.
  (* end snippet Pe_UnLiftO *)  
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
    by rewrite unpair_sz1.
    by pose proof LiftO_right_0 H1 H2 as [H3 H4].
  Qed.
  
  (** * Eope properties *)
  
  Lemma Lift_ChrelO: forall (sto: seq(T*T*O)),
      sto [L\in] ChrelO <-> (unpair sto).1 [L\in] (@Chrel T).
  Proof.
    split. 
    - elim:sto  => [ // | tto sto Hr].
      elim: sto tto Hr => [ [t1 t2 o1] _ // | [[t1' t2'] o1'] sto Hr [[t1 t2] o1] H1 H2].
      move: H2;rewrite Lift_c allset_cons=> [[H2 H3]].
      rewrite /unpair Lift_c allset_cons.
      by split;[ | apply H1].
    - elim:sto => [ // | tto sto Hr].
      elim: sto tto Hr => [ [t1 t2 o1] _ // | [[t1' t2'] o1'] sto _ [[t1 t2] o1] H1 H2].
      rewrite Lift_c allset_cons.
      move: H2; rewrite 2!unpair_c Lift_c allset_cons => [[H3 H4]].
      by split;[rewrite /ChrelO /mkset /= | apply H1;rewrite unpair_c].
  Qed.
  
  Lemma Lift_ChrelO1: forall (sto: seq(T*T*O)),
      size(sto) > 0 -> sto [L\in] ChrelO 
      -> exists p: seq T, size(p) = size(sto)+1 /\ Lift p = (unpair sto).1 
                    /\  (Lift p) [Suc\in] (@Chrel T).
  Proof.
    move => sto H0 H1.
    have H2: (unpair sto).1 [L\in] (@Chrel T) by apply Lift_ChrelO.
    move: H2;rewrite Lift_Chrel => [[p H3]].
    exists p. 
    split.
    have H2: size(Lift p)= size(sto) by rewrite -[RHS]unpair_sz1 H3.
    have H4: size(p) > 1 by rewrite -Lift_sz2 H2.
    have H5: size(p) = size (Lift p) +1 by apply Lift_sz3;rewrite H2.
    by rewrite H5 H2. 
    split. 
    by [].
    by rewrite H3 -RPath_equiv;apply Lift_ChrelO.
  Qed.

  Lemma Lift_ChrelO2: forall (sto: seq(T*T*O)) (x y:T),
      size(sto) > 0 -> sto [L\in] ChrelO -> Eope sto = (x, y)
      -> exists p, size p = size sto + 1 /\ Lift p = (unpair sto).1 
             /\ (Lift p) [L\in] (Chrel (T:=T))
             /\ Epe1 ptv (Lift p) = (x, y). 
  Proof.
    move => sto x y H1 H2 H3.
    have H2': sto [Suc\in] ChrelO by rewrite -RPath_equiv.
    pose proof Pe_UnLiftO H1 H2' as H4. 
    rewrite H3 /UnLiftO /= in H4.
    pose proof Lift_ChrelO1 H1 H2 as [p [H5 [H6 H6']]].
    have H7: pair ((unpair sto).1) ((unpair sto).2) = sto
      by apply unpair_right.
    have H8: (pair ((unpair sto).1) ((unpair sto).2)) [L\in] ChrelO
      by rewrite unpair_right.
    have H9: (LiftO p (unpair sto).2) [L\in] ChrelO
      by rewrite  /LiftO H6.
    have H10: size (unpair sto).1 = size (unpair sto).2 by apply unpair_sz.
    by exists p;rewrite /Epe1 H6 H4 -[in (unpair sto).1 [L\in] Chrel]H6 RPath_equiv.
  Qed.
  
  Lemma Lift_ChrelO2': forall (sto: seq(T*T*O)),
    size(sto) > 0 -> sto [L\in] ChrelO -> 
    exists p: seq T,exists so: seq O, 
      size(p) = size(sto)+1 /\ size(p)=size(so) +1 /\ LiftO p so = sto.
  Proof.
    move => sto H0 H1.
    pose proof Lift_ChrelO1 H0 H1 as [p [H2 [H3 H3']]].
    have H4: size p > 1 by rewrite H2 addn1.
    exists p; exists (unpair sto).2.
    rewrite -unpair_sz. 
    split. by []. split. 
    rewrite -H3.
    rewrite [in RHS]Lift_sz. 
    rewrite subn1 addn1.
    pose proof (ltn_predK H4) as H5.
    by rewrite H5.
    by [].
    rewrite /LiftO H3. 
    apply unpair_right.
  Qed.

  (** * deployment paths for extended oriented
   * Lift and UnLift are bijective on deployment path 
   * D_V <-[Lift]-> D_P 
   *) 
  
  (* begin snippet D_U:: no-out *)  
  Definition D_U (R E: relation T) := [set stto : seq (T*T*O) |size(stto)>0 
     /\ R (Eope stto) /\ stto [\in] (Oedge E) /\ stto [Suc\in] ChrelO].
  (* end snippet D_U *)  
  
  (* begin snippet D_U1:: no-out *)  
  Definition D_U_s (x y: T) (E: relation T):= D_U [set (x,y)] E.
  (* end snippet D_U1 *)  
  
  (* begin snippet D_Up:: no-out *)  
  Definition D_U' (R E: relation T):=
    [set st : (seq T)*(seq O) | 
      st.1 \in (@D T) /\ size(st.2) = size(st.1) -1 /\ 
               R (@Pe T ptv st.1) /\ (LiftOp st) [\in] (Oedge E)].
  (* end snippet D_Up *)  
  
  (* begin snippet D_V1:: no-out *)  
  Definition D_U'_s (x y:T) (E: relation T) := D_U' [set (x,y)] E.
  (* end snippet D_V1 *)  
  
  (* begin snippet DU_DU':: no-out *) 
  Lemma DU_DU': forall (R E: relation T), image (D_U' R E) LiftOp = (D_U R E).
  (* end snippet DU_DU':: no-out *)  
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
      by rewrite H6 H7 inP /UnLiftO /= /D /mkset UnLift_sz 
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
    by rewrite /UnLiftO inP /D /mkset UnLift_sz unpair_sz1 addn1.
    split.
    by rewrite /UnLiftO UnLift_sz /= unpair_sz addn1 subn1.
    split.
    by rewrite H7.
    by rewrite H9.
  Qed.
  
  (* begin snippet D_U2:: no-out *) 
  Definition D_U'' (R E: relation T):=
    [set spa | spa [\in] (Oedge E) /\
                 (exists p, exists x,exists y,exists o, (LiftO (x::(rcons p y)) o) = spa /\ R (x,y))].
  (* end snippet D_U2 *)

  (* begin snippet A_tr:: no-out *)  
  Definition A_tr (W: set T) (E: relation T) := ChrelO `&` 
    [set oe : (T*T*O) * (T*T*O)| match (oe.1.2,oe.2.2, oe.1.1.2) with 
      | (P,P,v) => W.^c v | (N,N,v) => W.^c v | (N,P,v) => W.^c v
      | (P,N,v) => (Fset E.* W) v end].
  (* end snippet A_tr *)
  
  Lemma A_tr_P1: forall(W: set T) (E: relation T), A_tr W E = ChrelO `&` (A_tr W E).
  Proof.
    by move => W E;rewrite /A_tr setIA setIid.
  Qed.

  (* begin snippet ActiveOe:: no-out *)  
  Definition ActiveOe (W: set T) (E: relation T) := 
    [set oe : (T*T*O) * (T*T*O) | 
      Oedge E oe.1 /\ Oedge E oe.2 /\ (ChrelO oe)
      /\ match (oe.1.2,oe.2.2, oe.1.1.2) with 
        | (P,P,v) => W.^c v
        | (N,N,v) => W.^c v
        | (N,P,v) => W.^c v
        | (P,N,v) => (Fset E.* W) v
        end].
  (* end snippet ActiveOe *)  
  
  Definition A_tr_eo (W: set T) (E: relation T) :=  
    ((Oedge E) `*` Oedge E) `&` (A_tr W E).
  
  Lemma Active_iff: forall (W: set T) (E: relation T), 
      A_tr_eo W E = ActiveOe W E.
  Proof.
    move => W E.
    rewrite /A_tr_eo /A_tr /ActiveOe /setI /setM /mkset predeqE => [[eo1 eo2]].
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
    by move => W E eo /inP [_ [_ [H3 _]]].
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
    move => W E x y z o;rewrite /ActiveOe /mkset /ChrelO /=.
    case: o.
    by split => [[? [? [_ ?]]] // | [? [? ?]]].
    by split => [[? [? [_ ?]]] // | [? [? ?]]].
  Qed.
  
  Lemma ActiveOeT: forall (W: set T) (E: relation T) (x u v z t: T) (o1 o2 o3 o4: O),
      (Fset E.* W) x 
      /\ ActiveOe W E ((u,x,o1), (x,v,o2)) /\ ActiveOe W E ((z,x,o3), (x,t,o4))
      -> ActiveOe W E ((u,x,o1), (x,t,o4)).
  Proof.
    move => W E x u v z t o1 o2 o3 o4.
    case: o1;case: o2; case:o3; case:o4;
      by move => [H0 [[H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]]]].
  Qed.
  
  Lemma ActiveOe_rev: forall (W:set T) (E: relation T) (e1 e2: (T * T)) (o:O),
      (ActiveOe W E).-1 ((e1,o), (e2,o)) <-> ActiveOe W E.-1 ((e2,O_rev o), (e1,O_rev o)).
  Proof.
    by move => W E [x1 y1] [x2 y2] o; case: o. 
  Qed.
  
  Lemma ActiveOe_eq: forall  (W: set T) (E: relation T),
      (((Oedge E)`*`(Oedge E))`&`(A_tr W E)) = (ActiveOe W E).
  Proof.
    move => W E.
    rewrite /A_tr /ActiveOe /setI /setM /mkset predeqE /= => [[tto1 tto2]].
    by split => [[[H1 H2] [H3 H4]] | [H1 [H2 [H3 H4]]]].
  Qed.

  (** * The final set we wish to study *)

  (* begin snippet D_U_a:: no-out *)  
  Definition D_U_a (R E: relation T) (W: set T) (x y:T):=
    (D_U R E) `&` [set stto | stto [Suc\in] (A_tr W E)].
  (* end snippet D_U_a *)  
  
  (* begin snippet D_U_a1:: no-out *)  
  Definition D_U_a1 (E: relation T) (W: set T) (x y:T):=
    [set stto |size(stto)>0 /\ (Eope stto)=(x,y) /\ stto [\in] (Oedge E) 
     /\ stto [Suc\in] ChrelO /\ stto [Suc\in] (A_tr W E)].
  (* end snippet D_U_a1 *)  
  
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
      move => [H5 [[H6 H6'] [H7 [H8 /RPath_equiv H9]]]].
      have H10: stto [L\in] (ActiveOe W E)
        by rewrite -ActiveOe_eq; apply (@Rpath_L3 (T*T*O)).
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
      by rewrite inP /D_U_a1 /mkset /Eope allset_cons -2!RPath_equiv. 
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
        by move: H8;rewrite -ActiveOe_eq allset_I => /andP [H8 H8']; apply (@Rpath_L2 (T*T*O)).
      have H11: stto [Suc\in] ChrelO
        by rewrite -RPath_equiv;pose proof ActiveOe_ChrelO;apply allset_subset with (ActiveOe W E);
        [apply ActiveOe_ChrelO |].
      have H12: stto [Suc\in] (A_tr W E)
        by rewrite -RPath_equiv;apply allset_subset with (ActiveOe W E);[ rewrite -ActiveOe_eq|].
      
      by rewrite /Eope H2 H3. 
  Qed.

  (* begin snippet  Active_eq:: no-out *)  
  Theorem Active_eq: forall (E: relation T) (W: set T) (x y:T) stto,
      ((x=y /\ stto = [::]) \/  stto \in (D_U_a1 E W x y))
      <-> Active_path W E stto x y.
  (* end snippet  Active_eq *)  
  Proof.
    move => E W x y stto.
    split. 
    apply Active_check1.
    apply Active_check2.
  Qed.
    
End pair_lift1.

Section Seq_lifto. 
  (** * Lifto that is LiftO with constant orientatio along the  *)
  Variables (T: Type).
  
  Fixpoint pair_o (spt: seq (T * T)) (o: O):= 
    match spt with
    | [::] => @nil (T*T*O)
    | pa::spt => (pa,o)::(pair_o spt o)
    end.

  Definition Lifto (sa: seq T) (o: O) := pair_o (Lift sa) o.
  
  Lemma pair_o_c: forall (spt: seq (T * T)) (o: O) (aa:T * T),
        pair_o (aa::spt) o = (aa,o)::(pair_o spt o).
  Proof.
    by [].
  Qed.

  Lemma pair_o_rc: forall (spt: seq (T * T)) (o: O) (aa:T * T),
        pair_o (rcons spt aa) o = rcons (pair_o spt o) (aa, o).
  Proof.
    by elim => [// | aa1 p Hr] o aa; rewrite rcons_cons //= Hr.
  Qed.

  Lemma pair_o_last: forall (spt: seq (T * T)) (o: O) (aa:T * T),
     last (aa,o) (pair_o spt o) = ((last aa spt), o).
  Proof.
    by elim => [// | aa1 p Hr] o aa //=.
  Qed.

  Lemma pair_o_head: forall (spt: seq (T * T)) (o: O) (aa:T * T),
     head (aa,o) (pair_o spt o) = ((head aa spt), o).
  Proof.
    by elim => [// | aa1 p Hr] o aa //=.
  Qed.

  Lemma pair_o_iff: forall (spt: seq (T * T)) (o: O),
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
