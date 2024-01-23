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

(* From RL Require Import  ssrel rel.  *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Reserved Notation "p [\in] X" (at level 4, no associativity). 
(* begin snippet all_notation:: no-out *)  
Notation "p [\in] X" := (all (fun x => x \in X) p). 
(* end snippet all_notation *)  

Section Seq_utilities.
  (** * some utilities on seq *)
  Variables (T: Type).

  Lemma seq_rc: forall (p: seq T), 
      (0 < size p) -> exists (q:seq T) (x:T), p = (rcons q x).
  Proof.
    by elim => [ // | x p _ _];exists (belast x p), (last x p);rewrite lastI.
  Qed.

  Lemma seq_c: forall (p: seq T), 
      (0 < size p) -> exists (q:seq T) (x:T), p = x::q.
  Proof.
    by elim => [ // | x p _ _]; exists p, x. 
  Qed.
  
  Lemma seq_rcrc: forall (p: seq T), 
      1 < size p -> exists (q:seq T) (x y:T), p = (rcons (rcons q x) y).
  Proof.
    move => p H1.
    have H2: 0 < size p by apply leq_ltn_trans with 1.  
    pose proof seq_rc H2 as [q [x H3]].
    have H4: 0 < size q by rewrite H3 size_rcons ltnS in H1.
    pose proof seq_rc H4 as [r [z H5]].
    by exists r,z,x;rewrite H3 H5.
  Qed.

  Lemma seq_crc: forall (p: seq T), 
      1 < size p -> exists (q:seq T) (x y:T), p = x::(rcons q y).
  Proof.
    move => p H1.
    have H2: 0 < size p by apply leq_ltn_trans with 1.  
    pose proof seq_rc H2 as [r [y H3]].
    have H4: 0 < size r by rewrite H3 size_rcons ltnS in H1.
    pose proof seq_c H4 as [q [x H5]].
    by exists q,x,y;rewrite H3 H5.
  Qed.

  Lemma seq_cc: forall (p: seq T), 
      1 < size p -> exists (q:seq T) (x y:T), p = [::x,y &q].
  Proof.
    move => p H1.
    have H2: 0 < size p by apply leq_ltn_trans with 1.  
    pose proof seq_c H2 as [r [y H3]].
    have H4: 0 < size r by rewrite H3 ltnS in H1.
    pose proof seq_c H4 as [q [x H5]].
    by exists q,y,x;rewrite H3 H5.
  Qed.
  
  Lemma seq_1: forall (p: seq T), 
      size p = 1 <-> exists (x:T), p = [::x].
  Proof.
    split; last by move => [x H1];rewrite H1.
    elim:p => [// | x p H1 /= H2].
    by (have -> : p = [::] by apply size0nil; apply succn_inj in H2);(exists x).
  Qed. 
  
  Lemma seq_rcrc0: forall (p: seq T), 
      size p = 2 <-> exists (x y:T), p = [::x;y].
  Proof.
    split => [H1 |[x [y H1]]];last by rewrite H1.
    - have H2: 1 < size p by rewrite -H1.
      pose proof seq_rcrc H2 as [q [x [y H3]]].
      move: H1;rewrite H3 size_rcons size_rcons => /eqP H1.
      have /nilP H4: size q == 0 by [].
      by exists x,y;rewrite H4.
  Qed.
  
  Lemma seq_cases: forall (p: seq T), 
      p=[::] \/ (exists x, p=[::x]) \/ exists (q:seq T), exists (x y:T), p=x::(rcons q y).
  Proof.
    elim => [| x p _]; first by left.
    elim: p => [ | y p _]; first by right;left;(exists x).
    right;right.
    have H1: size([:: x, y & p]) > 1 by [].
    pose proof (seq_crc H1) as [q [x' [y' H2]]].
    by exists q;exists x';exists y';rewrite H2.
  Qed.

  Lemma seq_cases_test: forall  (p:seq T),
      True.
  Proof.
    move => p.
    pose proof seq_cases p as [H1 | [[x H1] | [q [x [y H1]]]]].
    by []. 
    by [].
    by [].
  Qed.
  
End Seq_utilities.

Section Seq_lift. 
  (** * Lift operation on sequences *) 
  Variables (T: Type).
  
  (* begin snippet Lift:: no-out *)  
  Fixpoint Lift (p: seq T): seq (T * T) := 
    match p with 
    | x :: [:: y & p] as p1 => (x,y)::(Lift p1)
    | _ => @nil (prod T T)
    end.
  (* end snippet Lift *)  
  
  Lemma Lift_c: forall (p:seq T) (x y: T),
      Lift [::x,y & p] = [::(x,y) & Lift [::y & p]].
  Proof.
    by move => p x y; split.
  Qed.
  
  Lemma Lift_crc: forall (p:seq T) (x y: T),
      Lift (x::(rcons p y)) = (x,(head y p))::(Lift (rcons p y)).
  Proof.
    by move => p x y; rewrite headI Lift_c. 
  Qed.
  
  Lemma Lift_rcrc: forall (p:seq T) (x y: T),
      Lift (rcons (rcons p x) y) =  rcons (Lift (rcons p x)) (x,y).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    elim => [ x y // | z p Hr x y ].
    rewrite [in RHS]rcons_cons [in RHS]Lift_crc [in RHS]rcons_cons -[in RHS]Hr.
    by rewrite ![in LHS]rcons_cons [in LHS]Lift_crc H1. 
  Qed.
  
  Lemma Lift_rcc: forall (p:seq T) (x y: T),
      Lift (rcons (x::p) y) = rcons (Lift (x::p)) (last x p,y).
  Proof.
    by move => p x y;rewrite lastI Lift_rcrc.
  Qed.
  
  Lemma Lift_last: forall (p:seq T) (x y: T),
      last (x, head y p) (Lift (rcons p y)) = (last x p, y).
  Proof.
    by elim/last_ind => [x y // | p z Hr x y ];rewrite Lift_rcrc !last_rcons.
  Qed.

  Lemma Lift_head: forall (p:seq T) (x y: T),
      head (x, last y p) (Lift (x::p)) = (x,head y p).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    by elim/last_ind => [x y // | p z Hr x y ];rewrite Lift_crc H1 last_rcons.
  Qed.
  
  Lemma Lift_cat_rc: forall (p q:seq T) (y z: T),
      Lift ((rcons p y) ++ (rcons q z)) =
        Lift (rcons p y) ++ Lift (y::rcons q z).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    elim => [q y z // | t p Hr q y z].
    rewrite rcons_cons cat_cons -rcons_cat Lift_crc rcons_cat Hr. 
    have H2: head z (rcons p y ++ q) = head y p
      by elim/last_ind: q y z => [y z | q z' Hr' y z];
                                [rewrite cats0 H1 | rewrite -rcons_cat H1 Hr'].
    by rewrite H2 -cat_cons -Lift_crc.
  Qed.
  
  Lemma Lift_cat_crc: forall (p q:seq T) (x y z: T),
      Lift (x::(rcons p y) ++ (rcons q z)) =
        Lift(x::(rcons p y)) ++ Lift (y::rcons q z).
  Proof.
    elim => [q x y z // | t p Hr q x y z].
    by rewrite Lift_crc [in RHS]cat_cons -Lift_cat_rc.
  Qed.
  
  Lemma Lift_rev: forall (p:seq T), 
      Lift (rev p) = map (fun tt =>(tt.2, tt.1)) (rev (Lift p)). 
  Proof.
    elim => [// | x p Hr ];elim: p x Hr => [// | x' p _ x H1].
    by rewrite rev_cons rev_cons Lift_rcrc 
       -rev_cons H1 Lift_c rev_cons map_rcons.
  Qed.
  
  (** Left inverse of Lift when p is not the empty list *)
  
  Fixpoint UnLift (p: seq (T * T)) (t: T):= 
    match p with 
    | [::] => [::t]
    | [::(t1,t2) & p1 ] => [::t1 & UnLift p1 t2]
    end.
  
  Lemma UnLift_c: forall (p: seq (T * T)) (x y z: T),
      UnLift ((x, y) :: p) z = [::x & UnLift p y].
  Proof.
    by [].
  Qed.

  Lemma Lift_inv1: forall (p : seq T) (x y z: T),
      UnLift (Lift (x::(rcons p y))) z = (x::(rcons p y)).
  Proof.
    by elim => [// | y p Hr x' x z]; rewrite Lift_c UnLift_c Hr.
  Qed.

  Lemma UnLift_left: forall (t:T) (p : seq T),
      size (p) > 1 -> UnLift (Lift p) t = p.
  Proof.
    move => t p H1.
    pose proof (seq_crc H1) as [q [x [y H2]]]. 
    rewrite H2. apply Lift_inv1. 
  Qed.
  
  Lemma Lift_inv2: forall (p : seq T) (x: T),
      p <> [::] ->  UnLift (Lift p) (head x p) = p.
  Proof.
    move => p x'.
    pose proof seq_cases p as [H1 | [[x H1] | [r [x [y H1]]]]];rewrite H1 //;
      by move => _; apply Lift_inv1.
  Qed.
  
  Lemma Lift_inv_sz2: forall (p : seq T),
      (size(p) > 1) -> (forall (x:T), UnLift (Lift p) x = p).
  Proof.
    move => p.
    pose proof seq_cases p as [H1 | [[x H1] | [r [x [y H1]]]]];rewrite H1 //.
    by move => _ x1; apply Lift_inv1.
  Qed.
  
  Lemma Lift_inv: forall (p : seq T) (x y z: T),
      UnLift (Lift [::x,y & p]) z = [::x,y & p].
  Proof.
    by move => p x y z; apply Lift_inv_sz2.
  Qed.
  
  Lemma Lift_bc: forall (p : seq T) (x:T) (y: T*T) (q: seq (T*T)),
      Lift (x :: p) = y :: q -> x = y.1.
  Proof.
    move => p x' [y1 y2] q.
    by pose proof seq_cases p as [H1 | [[x H1] | [r [x [y H1]]]]];
    rewrite H1; [ | rewrite /= => [[?]] |rewrite Lift_c => [[?] _ _]].
  Qed.
  
  Lemma Lift_sz: forall (p:seq T),
      size(p) > 1 -> size (Lift p) = (size p) -1.
  Proof.
    move => p H1;pose proof seq_cc H1 as [q [x [y H2]]];rewrite H2;clear H2. 
    elim: q x y => [x y // | z q Hr x y].
    have H2: size ((x, y) :: Lift [:: y, z & q]) = 1+ size(Lift [:: y, z & q]) by [].
    by rewrite Hr in H2;rewrite Lift_c H2 /= addnC [RHS]subn1 subn1 addn1 /=.
  Qed.

  Lemma Lift_sz2: forall (p:seq T),
      size(Lift p) > 0 <-> size (p) > 1.
  Proof.
    by elim => [// | x p ]; elim: p x => [// | x p Hr y H1 // H2].
  Qed.

  Lemma Lift_sz3: forall (p:seq T),
      size(Lift p) > 0 -> size(p) = size(Lift p) +1. 
  Proof.
    move => p H1.
    have H2:  size p >1. by apply Lift_sz2.
    have H3:  size (Lift p) = (size p) -1 by apply Lift_sz.
    rewrite H3 subn1 addn1. 
    by have ->: (size p).-1.+1 = size p by apply: (ltn_predK H2).
  Qed.

  Lemma Lift_szn': forall (p:seq T) (n:nat),
      size(Lift p) = n.+1 <-> size (p) = n.+2.
  Proof.
    move => p n.
    split => H1.
    - have H2: size(Lift p) > 0 by rewrite H1.
      have H3: size(p) > 1 by rewrite -Lift_sz2.
      move: (H3) => /Lift_sz H4.
      have H5: ((size p).-1)%N  = n.+1 by rewrite -subn1 -H4.
      have H6: (size p).-1.+1 = size(p) by apply: (ltn_predK H3).
      by rewrite -H5 -[in LHS]H6.
    - have H3: size(p)> 1 by rewrite H1.
      pose proof (Lift_sz H3) as H4.
      by move: H4;rewrite H1 subn1 /=.
  Qed.
  
  Lemma Lift_szn: forall (p:seq T) (n:nat),
      size(Lift p) > n <-> size (p) > n.+1.
  Proof.
    move => p n.
    split => H1.
    - have H3: size(p)> 1 by rewrite -Lift_sz2 ;apply leq_ltn_trans with n.
      pose proof Lift_sz H3 as H4.
      by move: H1;rewrite H4 -ltn_predRL -subn1.
    - have H3: size(p)> 1 by apply leq_ltn_trans with n.+1.
      pose proof Lift_sz H3 as H4.
      by rewrite H4 subn1 ltn_predRL.
  Qed.

End Seq_lift.

Section basic_pair_unpair.
  (** * pair sequences *)
  Variables (T S: Type).
  
  (* we need an extra element as the two sequence may 
   * differ in size *)
  Fixpoint pair_ (s: S) (st: seq T) (so: seq S):= 
    match st, so with 
    | t::st, o::so => (t,o)::(pair_ s st so)
    | t::st, [::] =>  (t,s)::(pair_ s st [::])
    |  _ , _ => @nil (T*S)
    end.
  
  Fixpoint unpair (s: seq (T*S)) := 
    match s with 
    | [::] => ([::],[::])
    | (x,y)::s => (x::(unpair s).1,y::(unpair s).2)
    end.

  Lemma pair_c_: forall (s: S) (st: seq T) (ss: seq S) (t: T),
      pair_ s (t::st) ss = (t,head s ss)::(pair_ s st (behead ss)).
  Proof.
    move => s.
    elim => [ so pa // | pa1 spa Hr so pa ]; first by elim: so => [// | o so _ //].
    elim: so => [// | o so _ ].
    have -> : pair_ s [:: pa, pa1 & spa] (o :: so) = (pa,o)::(pair_ s [::pa1 & spa] so) by [].
    by rewrite Hr.
  Qed.

  Lemma pair_cc_: forall (sv: S) (st: seq T) (ss: seq S) (t: T) (s:S),
      pair_ sv (t::st) (s::ss) = (t,s)::(pair_ sv st ss).
  Proof.
    move => sv st ss t s.
    by elim: st => [// | t1 st ];elim: ss=> [// | s1 ss ].
  Qed.
  
  Lemma pair_cat_: forall (s: S) (p q: seq T) (sop soq: seq S),
      size sop = size p ->
      pair_ s (p++q) (sop++soq) = (pair_ s p sop) ++ (pair_ s q soq).
  Proof.
    move => s.
    elim => [ q sop soq /eqP //= /nilP -> //= | ].
    move => a p Hr q sop soq H1.
    elim: sop H1 Hr => [// | so1 sop H1 H2 H3].
    rewrite cat_cons cat_cons pair_c_ //=.
    have H4: size sop = size p by rewrite /size in H2; apply succn_inj.
    have -> : pair_ s (p ++ q) (sop ++ soq) = pair_ s p sop ++ pair_ s q soq 
      by apply H3.
    by [].
  Qed.

  Lemma unpair_sz: forall (sts: seq (T*S)),
      size (unpair sts).1 = size (unpair sts).2. 
  Proof.
    by elim => [// | [t1 s1] sts Hrt];rewrite /= -[in RHS]Hrt. 
  Qed.

  Lemma unpair_sz1: forall (sts: seq (T*S)),
      size (unpair sts).1 = size sts.
  Proof.
    by elim => [// | [t1 s1] sts Hrt];rewrite /= -[in RHS]Hrt. 
  Qed.
  
  Lemma unpair_left: forall(s: S) (st: seq T) (so: seq S),
      size(st) = size(so) -> unpair (pair_ s st so) = (st,so).
  Proof.
    move => s.
    elim => [ | t st Hrt].
    by elim => [ // | s1 so _ //].
    by elim =>  [ // | s1 so _ /succn_inj/Hrt H1] /=; rewrite H1.
  Qed.

  Lemma unpair1_left: forall(s: S) (st: seq T) (so: seq S),
      (unpair (pair_ s st so)).1 = st.
  Proof.
    move => s.
    elim => [ | t st Hrt].
    by elim => [ // | s1 so _ //].
    elim =>  [ // | s1 so _]. 
    by rewrite pair_c_ /unpair Hrt -/unpair.
    by rewrite pair_c_ /unpair Hrt -/unpair /=.
  Qed.
  
  Lemma unpair_right: forall(s: S) (sts: seq (T*S)),
      pair_ s (unpair sts).1 (unpair sts).2 = sts.
  Proof.
    by move => s;elim => [// | [t1 s1] sts Hrt];rewrite /= -[in RHS]Hrt. 
  Qed.

  Definition Spairs := [set sts:  seq (T*S) | True].
  Definition Pseq := [set st : (seq T)*(seq S) | size st.1 = size st.2].
  Definition IPseq (s:S) := [set sts |exists st, exists ss,
                         size(st)= size(ss) /\ pair_ s st ss = sts].

  Lemma P1: forall (s:S), image Pseq (fun st => pair_ s st.1 st.2) = IPseq s.
  Proof.
    move=> s.
    rewrite /image /Pseq /mkset predeqE => sts.
    split => [[[st ss] /= H1] H2 | [st [ss [H1 H2]]]].
    by (exists st;exists ss).
    by exists (st,ss).
  Qed.

  Lemma P2: forall (s:S), Spairs =  IPseq s.
  Proof.
    move => s.
    rewrite /mkset predeqE => sts.
    split => [ _ | _ ]; last first. by [].
    by exists (unpair sts).1;exists (unpair sts).2;
         split;[apply unpair_sz|apply unpair_right].
  Qed.

End basic_pair_unpair.

Section pair_unpair.
  (** * pair (seq: T) (seq:O) with O inductive
   * using P as default value. 
   *)
  
  Variables (T: Type).
  
  (* orientation  *)
  (* begin snippet O:: no-out *)
  Inductive O := | P | N.
  (* end snippet O *)

  (* begin snippet pair:: no-out *)  
  Definition pair (spa: seq (T)) (so: seq O):= @pair_ (T) (O) P spa so.
  (* end snippet pair *)  
  
  Lemma pair_c: forall (spa: seq T) (so: seq O) (pa: T),
      pair (pa::spa) so = (pa,head P so )::(pair spa (behead so)).
  Proof. by apply pair_c_. Qed.

  Lemma pair_cc: forall (st: seq T) (so: seq O) (t: T) (o: O),
      pair (t::st) (o::so) = (t,o)::(pair st so).
  Proof. by apply pair_cc_. Qed.
  
  Lemma pair_cat: forall (p q: seq T) (sop soq: seq O),
      size sop = size p ->
      pair (p++q) (sop++soq) = (pair p sop) ++ (pair q soq).
  Proof. by apply pair_cat_. Qed.

End pair_unpair.

Section pair_lift1.
  (** * pair combined with Lift *)
  Variables (T: Type).
  
  Definition LiftO (sa: seq T) (so: seq O) := pair (Lift sa) so.

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
  
  Definition UnLiftO (p: seq (T*T*O)) (x: T) :=
    ( UnLift (unpair p).1 x, (unpair p).2).

  Definition UnLiftO1 (p: seq (T*T*O)) (x: T) := UnLift (unpair p).1 x.
  
  Lemma UnLiftO_left: forall (t: T) (st: seq T) (so: seq O),
      size (st) > 1 /\ size(st) = size(so) + 1 
      -> UnLiftO (LiftO st so) t = (st,so).
  Proof.
    move => t st so [H1 H2].
    have H3: size(Lift st) = (size st) -1 by apply Lift_sz.
    have H4: size(Lift st) = size(so) by rewrite H3 H2 addn1 subn1. 
    have H5: (unpair (pair (Lift st) so)) = ((Lift st), so)
      by apply unpair_left.
    by rewrite /UnLiftO /LiftO H5 /=;f_equal;apply Lift_inv_sz2.
  Qed.
  
  Lemma UnLiftO1_left: forall(t: T) (st: seq T) (so: seq O),
      size (st) > 1 -> (UnLiftO (LiftO st so) t).1 = st.
  Proof.
    move => t st so H1.
    have H3: size(Lift st) = (size st) -1 by apply Lift_sz.
    have H5: (unpair (pair (Lift st) so)).1 = (Lift st)
      by apply unpair1_left.
    by rewrite /UnLiftO /LiftO H5 /=;f_equal;apply Lift_inv_sz2.
  Qed.

End pair_lift1.

Section Seq_lifto. 
  (** * Lifto *)
  Variables (T: Type).
  
  Fixpoint pair_o (spa: seq (T * T)) (o: O):= 
    match spa with
    | [::] => @nil (T*T*O)
    | pa::spa => (pa,o)::(pair_o spa o)
    end.

  Definition Lifto (sa: seq T) (o: O) := pair_o (Lift sa) o.
  
  Lemma pair_o_c: forall (spa: seq (T * T)) (o: O) (aa:T * T),
        pair_o (aa::spa) o = (aa,o)::(pair_o spa o).
  Proof.
    by [].
  Qed.

  Lemma pair_o_rc: forall (spa: seq (T * T)) (o: O) (aa:T * T),
        pair_o (rcons spa aa) o = rcons (pair_o spa o) (aa, o).
  Proof.
    by elim => [// | aa1 p Hr] o aa; rewrite rcons_cons //= Hr.
  Qed.

  Lemma pair_o_last: forall (spa: seq (T * T)) (o: O) (aa:T * T),
     last (aa,o) (pair_o spa o) = ((last aa spa), o).
  Proof.
    by elim => [// | aa1 p Hr] o aa //=.
  Qed.

  Lemma pair_o_head: forall (spa: seq (T * T)) (o: O) (aa:T * T),
     head (aa,o) (pair_o spa o) = ((head aa spa), o).
  Proof.
    by elim => [// | aa1 p Hr] o aa //=.
  Qed.

  Lemma pair_o_iff: forall (spa: seq (T * T)) (o: O),
      pair_o spa o = pair spa (nseq (size spa) o).
  Proof.
    by elim => [ // | pa spa Hr o ];rewrite pair_c pair_o_c Hr.
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

Section Pair_of_seq.
  (** * pair of sequences using Record *)
  Variables (T S: Type).
  
  Record Pairs (n m:nat) 
    := pair_s { pfst: (seq T);
               psnd: (seq S);
               cond1: size(pfst) >= n;cond2: size(pfst)=size(psnd) + m}.

  Definition Pairs0 : (Pairs 0 0).
  Proof.
    by refine {| pfst:= [::]; psnd:= [::]; cond1:= _;cond2:= _|}.
  Defined.
  
  (* define a cons operator for Pairs: second way with refine *)
  Definition spair_cons (n m:nat) (ts: T*S) (sp : Pairs n m) : (Pairs n m).
  Proof.
    refine {| pfst:= (ts.1::(pfst sp)); psnd:= (ts.2::(psnd sp)); cond1:= _;cond2:= _|}.
    by apply leqW; apply (cond1 sp).
    by rewrite /= (cond2 sp) -addn1 -addnA [m+1]addnC addnA addn1. 
  Defined.
  
  Definition Pair (ps: (Pairs 0 0)) (s:S) := pair_ s (pfst ps) (psnd ps).
  
  Definition Unpair (s: seq (T*S)) : (Pairs 0 0).
  Proof.
    refine {| pfst:= (unpair s).1;psnd := (unpair s).2;cond1:= _ ;cond2:= _|}.
    by [].
    by rewrite addn0 unpair_sz.
  Defined. 
  
  Lemma unpair_right': forall(s: S) (sts: seq (T*S)),
      Pair (Unpair sts) s = sts.
  Proof.
    move => s;elim => [/= | [t1 s1] sts Hrt]. 
    by rewrite /Pair /=.
    by rewrite /Pair /= -[in RHS]Hrt.
  Qed.

End Pair_of_seq.

Section LiftO. 
  (** * LiftO with Record *)
  Variables (T S: Type).
  
  Lemma size_l: forall (ps : (@Pairs T S 2 1)), size((Lift (pfst ps)))= size(psnd ps) + 0.
  Proof.
    move => ps. 
    pose proof (cond2 ps) as H1.
    pose proof (cond1 ps) as H2.
    pose proof (Lift_sz H2) as H3. 
    by rewrite H3 H1 addn1 addn0 subn1.
  Qed.
  
  Lemma size_gt1: forall (ps : (@Pairs T S 2 1)), size((Lift (pfst ps))) > 0.
  Proof.
    move => ps. 
    pose proof (cond2 ps) as H1.
    pose proof (cond1 ps) as H2.
    pose proof (Lift_sz H2) as H3. 
    rewrite H3 H1 addn1 subn1 /=.
    pose proof ltn_predK H2 as H4.
    rewrite -H4 addn1 in H1. apply succn_inj in H1.
    by rewrite -H1 ltn_predRL.
  Qed.
  
  Definition LiftT (s: (@Pairs T S 2 1)): (@Pairs (T*T) S 1 0) := 
    {| pfst:= (Lift (pfst s));psnd:=(psnd s);cond1:= size_gt1 s ; cond2:= size_l s |}.

End LiftO.
