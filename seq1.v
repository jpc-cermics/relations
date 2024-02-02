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
  Fixpoint Lift (st: seq T): seq (T * T) := 
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
  
  Lemma Lift_last: forall (st:seq T) (x y: T),
      last (x, head y st) (Lift (rcons st y)) = (last x st, y).
  Proof.
    by elim/last_ind => [x y // | st z Hr x y ];rewrite Lift_rcrc !last_rcons.
  Qed.

  Lemma Lift_head: forall (st:seq T) (x y: T),
      head (x, last y st) (Lift (x::st)) = (x,head y st).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    by elim/last_ind => [x y // | st z Hr x y ];rewrite Lift_crc H1 last_rcons.
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
    have H1: (y :: rcons (rev st) x) = rev (x::(rcons st y)) by rewrite rev_cons rev_rcons -rcons_cons.
    by rewrite /allL allset_rev allset_inv H1 Lift_rev.
  Qed.
  
  Lemma allL_All: forall (E: relation T) (st: seq T) (x y: T),
      allL E st x y -> (x::st) [\in] (E.+)#_(y).
  Proof.
    move => E st x y.
    elim: st x. 
    by move => x;rewrite /allL /= => /andP [/inP H1 _];apply /andP;split;[apply mem_set;apply Fset_t1|].
    move => z st Hr x;rewrite allL_c => /andP [/inP H1 /Hr H2].
    move: (H2);rewrite allset_cons => [[H3 H4]].
    by rewrite allset_cons;split;[ apply Fset_t2; exists z |].
  Qed.
  
End allset_Lifted.

Section Suc_as_Lift. 
  (** * st [L\in] R <-> st [Suc\in] R *)
    
  Variables (T: Type).

  (* begin snippet RPath_equiv:: no-out *)  
  Lemma RPath_equiv: forall (R:relation T) (st: seq T),  st [L\in] R <-> st [Suc\in] R.
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
  Definition Chrel  := [set sptt: (T*T)*(T*T) | (sptt.1).2 = (sptt.2).1].
  (* end snippet Chrel *)  
  
  Lemma Lift_Lift: forall (st:seq T), (Lift (Lift st)) [\in] Chrel. 
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
  
  (** * extra results ? *)
  
  (* begin snippet Lift_Suc:: no-out *)  
  Lemma Lift_Suc: forall (st:seq T), (Lift st) [Suc\in] Chrel. 
  (* end snippet Lift_Suc *)  
  Proof.
    by move => st; rewrite -RPath_equiv; apply Lift_Lift.
  Qed.
  
  Lemma Lift_Chrel_n_imp: forall (n: nat) (spt : seq (T*T)),
      size(spt)= n.+2 -> (Lift spt) [\in] Chrel -> exists st: seq T, Lift st = spt.
  Proof.
    elim => [// | n Hr].
    - move => spt H1 H2.
      rewrite seq_rcrc0 in H1;move: H1 => [[x1 x2] [[y1 y2] H3]].
      move: H2; rewrite H3 allL0' /Chrel /mkset => /= [->].
      by (exists [::x1;y1;y2]).
    - move => spt H1 H2.
      have H4: size(spt) > 1 by rewrite H1.
      pose proof seq_cc H4 as [q [[x1 x2] [[y1 y2] H5]]].
      move: H2; rewrite H5 Lift_c allset_cons => [[H6 H7]].
      move: H6; rewrite /Chrel /mkset /= => ->.
      have H8: size [::(y1, y2) & q] = n.+2
        by rewrite H5 /= -addn1 -[in RHS]addn1 in H1; apply addIn in H1.
      apply Hr in H7;last by [].
      move: H7 => [p1 H7].
      have H10: size(p1) > 1 by rewrite -Lift_sz2 H7.  
      pose proof seq_cc H10 as [q3 [x3 [y3 H11]]].
      exists [::x1,x3,y3& q3].
      rewrite Lift_c -H11 H7. 
      by have -> : x3 = y1 by move: H7; rewrite H11 Lift_c => [[H7]]. 
  Qed.
  
  Lemma Lift_Chrel_n_iff: forall (n: nat) (spt : seq (T*T)),
      size(spt)= n.+2 -> ((Lift spt) [\in] Chrel <-> exists st: seq T, Lift st = spt).
  Proof.
    move => n spt H1;split;first by apply Lift_Chrel_n_imp with n.
    by move => [st <-]; apply Lift_Lift.
  Qed.
  
  Lemma Lift_Chrel_gt1: forall (spt : seq (T*T)),
      size(spt) > 1 -> ((Lift spt) [\in] Chrel <-> exists st: seq T, Lift st = spt).
  Proof.
    move => spt H1.
    have H0: forall (n : nat), 1 < n -> n = n.-2.+2
        by elim => [// | [// |n _ H2 ]];
                  pose proof ltn_predK H2;rewrite -H;apply succn_inj.
    have H2: (size(spt)).-2 >= 0 by [].
    split => [H3 | [st <-]].
    by apply Lift_Chrel_n_imp with (size(spt)).-2;[apply H0 |].
    by apply Lift_Lift.
  Qed.
  
  Lemma Lift_Chrel: forall (spt : seq (T*T)),
      ((Lift spt) [\in] Chrel <-> exists st: seq T, Lift st = spt).
  Proof.
    elim => [ | [x y] spt _ ];first by split => ?;[(exists [::]) |].
    elim: spt => [ | [z t] spt _]; first by split => [H2 | [st H2]];[(exists [::x;y])|].
    by apply Lift_Chrel_gt1.
  Qed.

  (* begin snippet Lift_lemma:: no-out *)  
  Lemma Lift_lemma:  image [set st | True] (@Lift T) 
                     = preimage (@Lift (T*T)) [set spt| spt [\in] Chrel].
  (* end snippet Lift_lemma *)  
  Proof. 
    rewrite /image /preimage /mkset predeqE => spt.
    by split => [[x _ <-] | /Lift_Chrel [p H1]];[ apply Lift_Lift | exists p].
  Qed.

  (* begin snippet Lift_lemma2:: no-out *)  
  Definition Im (n: nat):= image [set st | size(st)>n] (@Lift T).
  Definition Im1 (n: nat):= [set spt| exists st: seq T, Lift st = spt /\ size(st)>n].
  Definition Pre (n: nat):= 
    preimage (@Lift (T*T)) [set spt| spt [\in] Chrel /\ size(spt)> n].
  Definition Pre1 (n: nat):= [set spt| (Lift spt) [\in] Chrel /\ size(spt)>n].
  (* end snippet Lift_lemma2 *)  

  Lemma Lift_lemma2: (Im 2) = (Pre 0).
  Proof. 
    rewrite /Im /Pre /image /preimage /mkset predeqE => spt.
    split => [[x H1 <-] | [/Lift_Chrel [p H1] H2]]. 
    by split;[apply Lift_Lift | move: H1; rewrite 2!Lift_szn].
    by exists p;[rewrite -2!Lift_szn H1 |].
  Qed.

  Lemma Lift_lemma3: (Im 2) = (Im1 2).
  Proof. 
    rewrite /Im /Im1 /image /mkset predeqE => spt.
    by split => [[p H1 H2]|[p [H1 H2]]];(exists p).
  Qed.
    
  Lemma Lift_lemma4: (Pre 0) = (Pre1 1).
  Proof. 
    by rewrite /Pre /Pre1 /preimage /mkset predeqE => spt;rewrite Lift_szn.
  Qed.

End Lift_bijective.

Section epts.
  (** * endpoints and deployment  *)

  Variables (T: Type) (t:T).

  (* begin snippet Pe:: no-out *)  
  Definition Pe (st: seq T) := (head t st, last t st).
  (* end snippet Pe:: no-out *)  

  Definition decomp (st: seq T) := (head t st, last t st, behead (behead (belast t st))).
  Definition comp (tr: T*T*(seq T)) := tr.1.1::(rcons tr.2 tr.1.2).

  (* begin snippet Epe:: no-out *)  
  Definition Epe (spt: seq (T*T)) := (Pe (UnLift spt t)) .
  (* end snippet Epe *)  
  Definition Edecomp (spt: seq (T*T)) := (decomp (UnLift spt t)).
  Definition Ecomp (tr: T*T*(seq T)) := Lift (comp tr).
  
  Definition D1 (x y :T) := [set st:seq T | (decomp st).1 = (x,y)].
  Definition I1 (x y :T) := [set spt:seq (T*T) | (Edecomp spt).1 = (x,y)].

  Lemma Lxx: forall (st:seq T), size(st)> 1 -> comp (decomp st) = st.
  Proof. 
    move => p.
    pose proof seq_cases p as [H1 | [[x H1] | [r [x [y H1]]]]];rewrite H1 //.
    move => _.
    by rewrite /decomp /comp /= belast_rcons last_rcons /=.
  Qed.

  Lemma Lyy: forall (tr: T*T*(seq T)),  decomp (comp tr) = tr.
  Proof. 
    move => [[x p] y].
    by rewrite /comp /decomp /=  belast_rcons last_rcons /=.
  Qed.
  
  Lemma Lift_epts_image: forall (st: seq T) (x y:T),
      st \in ((D1 x y)`&` (@D T))-> (Lift st) \in (I1 x y)`&` (@I T).
  Proof.
    move => st x y.
    move => /inP [[H1 H2] /inP H3].
    pose proof (Lift_image H3) as H4.
    move: H4 => /inP [H4 H5].
    rewrite inP /setI.
    split. 
    - rewrite /I1 /= .
      have -> : (UnLift (Lift st) t) = st 
        by rewrite Lift_sz2 in H4;apply: UnLift_left H4.
      by rewrite H1 H2.
    - by []. 
  Qed.
  
  Lemma UnLift_epts_image: forall (spt: seq (T*T)) (x y:T),
      spt \in ((I1 x y)`&` (@I T))-> (UnLift spt t) \in (D1 x y)`&` (@D T).
  Proof.
    move => p x y.
    move => /inP [[H1 H2] /inP H3].
    pose proof (UnLift_image H3) t as H4.
    by rewrite inP /D1 /setI /mkset /decomp H1 H2 /= ;split;[ | apply inP].
  Qed.
  
  (* begin snippet D_P:: no-out *)  
  Definition D_P (R E: relation T):= 
    [set spt|size(spt)>0/\R (Epe spt)/\spt [\in] E/\spt [Suc\in] (@Chrel T)].
  (* end snippet D_P *)  
  
  (* begin snippet D_P1:: no-out *)  
  Definition D_P1 (x y: T) (E: relation T):= D_P [set (x,y)] E.
  (* end snippet D_P1 *)  

  (* begin snippet D_V:: no-out *)  
  Definition D_V (R E: relation T):=[set st| size(st)>1 /\R (Pe st) /\st [Suc\in] E].
  (* end snippet D_V *)  
  
  (* begin snippet D_V1:: no-out *)  
  Definition D_V1 (x y:T) (E: relation T) := D_V [set (x,y)] E.
  (* end snippet D_V1 *)  
  
  (* begin snippet DP_DV:: no-out *)  
  Lemma DP_DV: forall  (R E: relation T), image (D_V R E) (@Lift T) = (D_P R E).
  (* end snippet DP_DV:: no-out *)  
  Proof.
    move => R E.
    rewrite /D_V /D_P /mkset predeqE => q.
    split. 
    - move => [p [H1 [H2 H3]] <-].
      move: (H1) => /Lift_sz2 H1'.
      rewrite /Epe /Edecomp.
      have -> : (UnLift (Lift p) t) = p by apply UnLift_left. 
      rewrite RPath_equiv.
      by pose proof Lift_Suc p as H5.
    - move => [H1 [H2 [H3 H4]]].
      have H6 : Lift (UnLift q t) = q  by apply Lift_UnLift;rewrite inP /I. 
      have H7: 1 < size (UnLift q t) by rewrite -H6 Lift_sz2 in H1.
      rewrite -H6 /=.
      by exists (UnLift q t);[rewrite -RPath_equiv H6|]. 
  Qed.
  
  (* it remains to express D_P when R=[set (x,y)] using the image lemma *)

  Definition D_P1_new1 (x y:T) (E: relation T) := 
    [set spt| exists st, spt = Lift (x::(rcons st y)) /\ spt [\in] E /\ spt [Suc\in] (@Chrel T)].

  Definition D_P1_new2 (x y:T) (E: relation T) := 
    [set spt| spt=[::(x,y)] /\ E (x,y)] `|` 
      [set spt | exists st, spt = Lift (x::(rcons st y)) /\ spt [L\in] ((E `*`E ) `&` (@Chrel T))].

  Lemma D_V1_step1: forall (x y:T) (st:seq T),
      1 < size st /\ [set (x, y)] (Pe st) <-> exists q, st= x::(rcons q y).
  Proof.
  Admitted.

  Section XXXX.
    
    (** * fixed endpoints *) 
    Lemma Epe_L1: forall (q: seq (T*T)) (x y:T),
        q \in (@I T) -> Epe q = (x, y) 
            -> exists p, p \in (@D T) /\ q= Lift p /\ Pe p =(x,y).
    Proof.
      move => q x y H1 H2.
      pose proof Lift_surj H1 as [st [H3 H4]].
      exists st.
      move: H2. rewrite /Epe -H4.
      have -> :(UnLift (Lift st) t) = st by apply UnLift_left;rewrite inP in H3.
      by move => H5. 
    Qed.
    
    Lemma Epe_L2: forall (p: seq T) (x y:T),
        p \in (@D T) -> Pe p =(x,y) -> exists q, p = x::(rcons q y).
    Proof.
      move => p x y /inP H1 H2.
      pose proof seq_crc H1 as [q [x' [y' H3]]].
      move: H2;rewrite /Pe H3 //= => [[H2 //= H4]].
      have H5: forall q' x'', last x'' (rcons q' y') = y'
          by elim;[| move => z q' Hr x'';rewrite rcons_cons /=; rewrite Hr].
      by exists q;rewrite H2 -H4 H5.
    Qed.
    
    Lemma Epe_L3: forall (q: seq (T*T)) (x y:T),
        q \in (@I T) -> Epe q = (x, y) ->exists p, q= Lift (x::(rcons p y)). 
    Proof.
      move => q x y H1 H2.
      pose proof Epe_L1 H1 H2 as [p [H3 [H4 H5]]].
      pose proof Epe_L2 H3 H5 as [p' H6].
      by exists p'; rewrite H4 H6.
    Qed.
    
    Lemma Epe_L4: forall (q: seq (T*T)) (x y:T),
        q \in (@I T) -> Epe q = (x, y) -> size(q) > 1
            -> (exists q', exists eo1, exists eo2, q= eo1 :: [:: eo2 & q']) 
              /\ (exists p, q= Lift (x::(rcons p y))).
    Proof.
      move => q x y H1 H2 H3.
      pose proof Epe_L3 H1 H2 as [p H4].
      pose proof seq_cc H3 as [q' [eo1 [eo2 H5]]].
      by split;[exists q';exists eo1;exists eo2 | exists p].
    Qed.

    Lemma Epe_L5: forall (q: seq (T*T)) (x y:T),
        q \in (@I T) -> Epe q = (x, y) -> size(q) > 1
            -> (exists q', exists eo1, exists eo2, exists p, 
                  q= eo1 :: [:: eo2 & q'] /\
                  eo1 :: [:: eo2 & q'] = Lift (x::(rcons p y))).
    Proof.
      move => q x y H1 H2 H3.
      pose proof  Epe_L4 H1 H2 H3 as [[q' [eo1 [eo2 H4]]] [p H5]].
      by exists q';exists eo1;exists eo2;exists p; rewrite -H4 -H5.
    Qed.
    
    Lemma Epe_L6: forall (q: seq (T*T)) (p: seq T) (eo1:T*T) (eo2:T*T) (x y:T),
        eo1 :: [:: eo2 & q] = Lift (x::(rcons p y)) -> eo1.1 = x.
    Proof.
      move => q p eo1 eo2 x y H1.
      have H2: head (x, last y (rcons p y)) ([:: eo1, eo2 & q])
               = (head (x, last y (rcons p y)) (Lift (x :: rcons p y)))
        by rewrite H1.
      rewrite Lift_head /= in H2.
      by rewrite H2.
    Qed.

    Lemma Epe_L7: forall (q: seq (T*T)) (p: seq T) (eo1:T*T) (eo2:T*T) (x y:T),
        eo1 :: [:: eo2 & q] = Lift (x::(rcons p y)) -> (last eo2 q).2 = y.
    Proof.
      move => q p eo1 eo2 x y H1.
      have H2: last (x,  head y (x::p)) ([:: eo1, eo2 & q])
               = last (x, head y (x::p)) (Lift (rcons (x::p) y))
        by rewrite H1 rcons_cons.
      rewrite Lift_last /= in H2.
      by rewrite H2.
    Qed.
    
    Lemma Epe_L8: forall (q: seq (T*T)) (x y:T),
       q \in (@I T) -> Epe q = (x, y) -> size(q) > 1
            -> (exists q', exists eo1, exists eo2,
                  q= eo1 :: [:: eo2 & q'] /\ eo1.1 = x /\ (last eo2 q').2 = y).
    Proof.
      move => q x y H1 H2 H3.
      pose proof Epe_L5 H1 H2 H3 as [q' [eo1 [eo2 [p [H4 H5]]]]].
      exists q'; exists eo1;exists eo2.
      pose proof Epe_L6 H5 as H6.
      pose proof Epe_L7 H5 as H7.
      by [].
    Qed.
    
  End XXXX.
  
End epts.

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
    [set spt | size(spt) > n /\ spt [\in] E /\ spt [Suc\in] (@Chrel T)].
  (* end snippet Epath_gt *)  
  
  Definition REpaths (E: relation T) (R: relation (T*T)) := 
    [set spt:seq (T*T) | spt [\in] E /\ spt [L\in] (@Chrel T) /\ spt [L\in] R].
  
  Lemma REpath_iff1: forall (E: relation T) (R: relation (T*T)),
      [set spt:seq (T*T) | spt [\in] E /\ spt [L\in] ((@Chrel T) `&` R)]
    = [set spt | spt = [::]] 
        `|` [set spt | size(spt) = 1 /\ (spt [\in] E) ] 
        `|` [set spt | size(spt) > 1 /\ spt [L\in] ((E `*` E)`&` ((@Chrel T) `&` R))]. 
  Proof.
    by move => E R;rewrite -[RHS]Rpath_iff.
  Qed.

  Lemma REpath_iff2: forall (E: relation T) (R: relation (T*T)),
      [set p:seq (T*T) | p [\in] E /\ p [L\in] ((@Chrel T) `&` R)]
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
    elim => [ so pa // | pa1 spt Hr so pa ]; first by elim: so => [// | o so _ //].
    elim: so => [// | o so _ ].
    have -> : pair_ s [:: pa, pa1 & spt] (o :: so) = (pa,o)::(pair_ s [::pa1 & spt] so) by [].
    by rewrite Hr.
  Qed.

  Lemma pair_sz:  forall (s: S) (st: seq T) (ss: seq S),
      size (pair_ s st ss) = size st.
  Proof.
    by move => s;elim => [// | t st Hr ss];rewrite pair_c_ /= Hr.
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
  Definition pair (spt: seq (T)) (so: seq O):= @pair_ (T) (O) P spt so.
  (* end snippet pair *)  
  
  Lemma pair_c: forall (spt: seq T) (so: seq O) (pa: T),
      pair (pa::spt) so = (pa,head P so )::(pair spt (behead so)).
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
  
  (* begin snippet LiftO:: no-out *)  
  Definition LiftO (sa: seq T) (so: seq O) := pair (Lift sa) so.
  (* end snippet LiftO *)  

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
    by elim => [ // | pa spt Hr o ];rewrite pair_c pair_o_c Hr.
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
