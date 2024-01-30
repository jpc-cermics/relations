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
  Fixpoint Lift (p: seq T): seq (T * T) := 
    match p with 
    | x :: [:: y & p] as p1 => (x,y)::(Lift p1)
    | _ => Nil (T*T)
    end.
  (* end snippet Lift *)  
  
  (* another equivalent definition *)
  Definition Lift' (t:T) (p: seq T) := 
    (behead (pairmap (fun x y => (x,y)) t p)).
  
  Lemma Lift_eq: forall (t:T) (p:seq T), Lift p = Lift' t p.
  Proof.
    move => t;elim => [// | t1 p _];elim: p t1 => [// | t2 p H1 t1 //]. 
    have -> : Lift [:: t1, t2 & p] = (t1,t2)::(Lift [::t2 & p]) by split.
    by rewrite H1.
  Qed.

End Lift_def.

(* begin snippet Liftnota:: no-out *)
Notation "p [L\in] R" := (Lift p) [\in] R.
(* end snippet Liftnota *)

Section Suc_def.
  (** * p [Suc\in] R: consecutive elements of p satisfy relation R *)
  (** * we later prove that: p [L\in] R <-> p [Suc\in] R *)
    
  Variables (T: Type).

  Inductive RPath (R: relation T): seq T -> Prop :=
  | pp_void : RPath R [::]
  | pp_two (t: T) (st: seq T) : 
    RPath R st ->
    st = [::] \/ (exists (t': T), exists (st': seq T), st = [::t' & st'] /\ R (t,t'))
    -> RPath R ([:: t & st]).
  
  (* begin snippet RPath:: no-out *)  
  Notation "p [Suc\in] R" := (RPath R p).
  (* end snippet RPath *)  
      
End Suc_def. 

Notation "p [Suc\in] R" := (RPath R p) (at level 4, no associativity). 

Section Seq_utilities.
  (** * some utilities for sequences *)
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

  Lemma seq_n: forall (n:nat) (p: seq T), 
      size p = n.+1 -> exists q,exists x, p = [::x & q] /\ size(q) = n.
  Proof.
    elim => [| n Hn p H1].
    + elim => [_ // | t p H1 /= /succn_inj/size0nil H2]. 
      by rewrite H2;exists [::], t.
    + have H2: size(p) > 0.  by rewrite H1. 
      pose proof (seq_c H2) as [q [x H3]].
      rewrite H3 /= in H1. apply succn_inj in H1.
      by exists q, x. 
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

  Lemma seq_cases1: forall (p: seq T), 
      p=[::] \/ (exists x, p=[::x]) \/ exists (q:seq T), exists (x y:T), p=[::x,y & q].
  Proof.
    elim => [| x p _]; first by left.
    elim: p => [ | y p _]; first by right;left;(exists x).
    right;right.
    have H1: size([:: x, y & p]) > 1 by [].
    pose proof (seq_cc H1) as [q [x' [y' H2]]].
    by exists q;exists x';exists y';rewrite H2.
  Qed.
  
End Seq_utilities.

Section Lift_props. 
  (** * properties of the Lift mapping *)
  Variables (T: Type).
  
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
  
  (** Left inverse of Lift *)
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

End Lift_props. 


Section allset.
  (** * utilities for p [\in] X, X: set T *)

  Variables (T: Type).

  (* begin snippet Sn:: no-out *)  
  Definition Sn (T:Type) (n: nat) (D: set T):= [set p| p [\in] D/\size(p)=n].
  (* end snippet Sn *)
  
  Lemma allsetP: forall (X: set T) (p: seq T) (x:T),
      X x /\ p [\in] X <-> (x \in X) && (p [\in] X).
  Proof.
    by split => [[/mem_set -> ->] // | /andP [/set_mem H1 H2]].
  Qed.
  
  Lemma allset_consb: forall (X: set T) (p: seq T) (x:T),
      ((x::p) [\in] X) <-> (x \in X) && p [\in] X.
  Proof. by split. Qed.

  Lemma allset_cons: forall (X: set T) (p: seq T) (x:T),
      ((x::p) [\in]  X) <->  X x /\ p [\in] X.
  Proof.
    by move=> X p x;rewrite allset_consb allsetP.
  Qed.
  
  Lemma allset_subset: forall (X Y: set T) (p: seq T), 
      (X `<=` Y) -> (p [\in]  X) -> (p [\in] Y).
  Proof.
    move => X Y;elim => [ // | x' p' H1 H2 /andP [H3 H4]]. 
    apply/andP;split.
    by apply: mem_set;apply: H2; apply set_mem. 
    by apply H1.
  Qed.
  
  Lemma allset_rcons: forall (X: set T) (p: seq T) (x:T),
      (rcons p x) [\in] X <-> p [\in] X /\ X x.
  Proof.
    by move => X p x;rewrite all_rcons andC allsetP.
  Qed. 
    
  Lemma allset_rev: forall (X: set T) (p: seq T),
      p [\in] X <->  (rev p) [\in] X.
  Proof.
    by move => X p;rewrite all_rev.
  Qed. 
  
  Lemma allset_cat: forall (X: set T) (p q: seq T),
      (p++q) [\in] X <-> p [\in] X /\ q [\in] X.
  Proof.
    by move=> X p q;rewrite all_cat;split => [/andP | [-> ->]].
  Qed.

  Lemma allset_I: forall (X Y: set T) (p: seq T),
    p [\in] (X `&` Y) <-> p [\in] X && p [\in] Y. 
  Proof.
    move => X Y p.
    pose proof intersectionSr.
    have H1: (X `&` Y) `<=` X by rewrite /setI /mkset /subset => [t [? ?]].
    have H2: (X `&` Y) `<=` Y by rewrite /setI /mkset /subset => [t [? ?]].
    split => [H3 | ]. 
    by apply/andP;split;[apply: (allset_subset H1 H3)
                        | apply: (allset_subset H2 H3)].
    elim: p => [// |  x spa Hr /andP H3].
    move: H3; rewrite !allset_cons => [[[H3 H4] [H5 H6]]].
    by split;[rewrite /setI /mkset | apply Hr;apply/andP].
  Qed.
  
End allset.

Section allset2.
  (** * extra utilities for p [\in] R, R: relation T *)
  Variables (T: Type).
  
  Lemma allset_inv: forall (E: relation T) (spa: seq (T * T)), 
      spa [\in] E <-> (map (fun tt => (tt.2,tt.1)) spa) [\in] E.-1. 
  Proof.
    move => E;elim => [ // | [x y] spa Hr].
    by rewrite map_cons !allset_cons Hr.
  Qed.
  
  Lemma allset_Rr: forall (X: set T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] R_(X) <-> (rcons p y) [\in] X.
  Proof.
    move => X x y p.
    elim: p x. 
    - rewrite /= /Rr; split => [/andP [/inP H1 _] | /andP [/inP H1 _]].
      by rewrite /mkset /= in H1;apply mem_set in H1;rewrite H1.
      by apply/andP;split;[ apply/inP;rewrite /mkset /= |].
    - move => z p Hr x; rewrite rcons_cons Lift_c 2!allset_cons.
      split => [ [? /Hr ?] // | [? ?]].
      by split;[| apply Hr].
  Qed.

  Lemma allset_Lr: forall (X: set T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] L_(X) <-> (x::p) [\in] X.
  Proof.
    move => X x y p.
    elim: p x. 
    - rewrite /= /Lr; split => [/andP [/inP H1 _] | /andP [/inP H1 _]].
      by rewrite /mkset /= in H1;apply mem_set in H1;rewrite H1.
      by apply/andP;split;[ apply/inP;rewrite /mkset /= |].
    - move => z p Hr x; rewrite rcons_cons Lift_c 2!allset_cons.
      split => [ [? /Hr ?] // | [? ?]].
      by split;[| apply Hr].
  Qed.
  
  Lemma allset_Dl: forall (X: set T) (E: relation T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] (Δ_(X)`;`E) -> (x::p) [\in] X.
  Proof.
    by move => X E x y p;rewrite DeltaLco allset_I => /andP [/allset_Lr H1 _].
  Qed.

  Lemma allset_Dr: forall (X: set T) (E: relation T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] (E`;`Δ_(X)) -> (rcons p y) [\in] X.
  Proof.
    by move => X E x y p;rewrite DeltaRco allset_I => /andP [_ /allset_Rr H1].
  Qed.

End allset2.

Notation "[L: x ; p ; y `\in` E ]" := ((Lift (x::(rcons p y))) [\in] E).

Section allset_Lifted.
  (** * properties of p [L\in] R for p: seq T  *)
  (** * with specified p endpoints *)
  
  Variables (T: Type).
  Definition allL (E: relation T) (p: seq T) (x y:T) := [L: x; p ;y `\in` E].
  
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
  
  Lemma allL_c: forall (E: relation T) (p: seq T) (x y z: T),
      allL E (z::p) x y <-> ((x, z) \in E) && allL E p z y.
  Proof.
    by move => E p x y z;split;[rewrite /allL rcons_cons Lift_c allset_cons |].
  Qed.

  Lemma allL_rc: forall (E: relation T) (p: seq T) (x y z: T),
      allL E (rcons p z) x y <-> ((z,y) \in E) && allL E p x z.
  Proof.
    move => E p x y z;split.
    by rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons;move => [-> /inP ->].
    by move => /andP [/inP ? ?];rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons. 
  Qed.
  
  Lemma allL_cat: forall (E: relation T) (p q: seq T) (x y z: T),
      allL E ((rcons p y) ++ q) x z <-> allL E p x y && allL E q y z.
  Proof.
    move => E p q x y z.
    rewrite /allL cat_rcons rcons_cat rcons_cons -cat_rcons Lift_cat_crc allset_cat.
    by split => [ [? ?] | /andP [? ?]];[apply/andP |].
  Qed.
  
  Lemma allL_subset: forall (E R: relation T) (p: seq T) (x y: T),
      (E `<=` R) -> allL E p x y -> allL R p x y.
  Proof.
    by move => E R p x y H1 H2;apply allset_subset with E.
  Qed.
  
  Lemma allL_WS_iff: forall (E: relation T) (W:set T) (p: seq T) (x y: T),
      allL (Δ_(W.^c) `;` E) p x y <-> (x::p) [\in] W.^c && allL E p x y.
  Proof.
    move => E W p x y.
    have H1: (L_(W.^c) `&` E) `<=` E by apply intersectionSr.
    have H2: (L_(W.^c) `&` E) `<=` L_(W.^c) by apply intersectionSl.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) E) as H4.    
    rewrite DeltaLco /allL allset_I.
    by split => /andP [/allset_Lr H5 H6];[apply /andP | apply /andP].
  Qed.
  
  Lemma allL_SW_iff: forall (E: relation T) (W:set T) (p: seq T) (x y: T),
      allL (E `;` Δ_(W.^c)) p x y <-> (rcons p y) [\in] W.^c && allL E p x y.
  Proof.
    move => E W p x y.
    have H1: (E `&` L_(W.^c)) `<=` E by apply intersectionSl.
    have H2: (E `&` L_(W.^c)) `<=` L_(W.^c) by apply intersectionSr.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` E) E) as H4.    
    rewrite DeltaRco /allL allset_I; split => /andP [H5 H6]. 
    by rewrite allset_Rr in H6; apply /andP; split. 
    by apply /andP; split;[| rewrite allset_Rr].
  Qed.
  
  Lemma allL_rev: forall (E: relation T) (p: seq T) (x y: T),
      allL E p x y <->  allL E.-1 (rev p) y x.
  Proof.
    move => E p x y. 
    have H1: (y :: rcons (rev p) x) = rev (x::(rcons p y)) by rewrite rev_cons rev_rcons -rcons_cons.
    by rewrite /allL allset_rev allset_inv H1 Lift_rev.
  Qed.
  
  Lemma allL_All: forall (E: relation T) (p: seq T) (x y: T),
      allL E p x y -> (x::p) [\in] (E.+)#_(y).
  Proof.
    move => E p x y.
    elim: p x. 
    by move => x;rewrite /allL /= => /andP [/inP H1 _];apply /andP;split;[apply mem_set;apply Fset_t1|].
    move => z p Hr x;rewrite allL_c => /andP [/inP H1 /Hr H2].
    move: (H2);rewrite allset_cons => [[H3 H4]].
    by rewrite allset_cons;split;[ apply Fset_t2; exists z |].
  Qed.
  
End allset_Lifted.

Section Suc_as_Lift. 
  (** * p [L\in] R <-> p [Suc\in] *)
    
  Variables (T: Type).

  (* begin snippet RPath_equiv:: no-out *)  
  Lemma RPath_equiv: forall (R:relation T) (p: seq T),  p [L\in] R <-> p [Suc\in] R.
  (* end snippet RPath_equiv *)  
  Proof.
    move => R p.
    (* we use seq_cases to explore the three cases *)
    pose proof seq_cases p as [H1 | [[x H1] | [q [x [y H1]]]]];rewrite H1.
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
  Definition Chrel  := [set ppa : (T * T)*(T * T) | (ppa.1).2 = (ppa.2).1].
  (* end snippet Chrel *)  
  
  Lemma Lift_Lift: forall (p:seq T), (Lift (Lift p)) [\in] Chrel. 
  Proof.
    move => p. 
    pose proof seq_cases p as [H1 | [[x H1] | [q [x [y H1]]]]].
    (* p = [::] *) by rewrite H1. 
    (* p = [::x] *) by rewrite H1. 
    (* p = x::(rcons q y) *)
    have H2: size(p) > 1 by rewrite H1 /= size_rcons.
    move: H2 => /seq_cc [q1 [x1 [x2 ->]]].
    elim: q1 x1 x2 => [ x' y' // | y' p' Hr z' x'].
    by rewrite 3!Lift_c allset_cons -Lift_c;split;[ |apply Hr].
  Qed.

  (* begin snippet DI:: no-out *)  
  Definition D := [set p:seq T | size(p) > 1].
  Definition I := [set p:seq (T*T) | size(p) > 0 /\ p [Suc\in] Chrel].
  (* end snippet DI *)
  
  Lemma Lift_image: forall (p: seq T),
      p \in D -> (Lift p) \in I.
  Proof.
    rewrite /D /I /mkset; move => p /inP H1;rewrite inP Lift_sz2.
    by split;[ | rewrite -RPath_equiv;apply Lift_Lift].
  Qed.

  Lemma UnLift_image: forall (p: seq (T*T)),
      p \in I -> (forall (z:T), (UnLift p z) \in D).
  Proof.
    move => p /inP [H1 _] z; apply inP.
    rewrite /D /mkset.
    elim: p H1 => [// | [x y] p _ /= _].
    elim: p y => [ // | [x' y'] p' _ z'].
    by rewrite UnLift_c /=. 
  Qed.

  Lemma Lift_UnLift: forall (p: seq (T*T)),
      p \in I -> (forall (z:T), Lift (UnLift p z) = p).
  Proof.
    move => p /inP [H1 H2] z; apply inP.
    elim: p H1 H2 => [// | [x y] p Hr H1 H2].
    rewrite UnLift_c.
    elim: p y x Hr H1 H2 => [y x _ _ _ /= // | [x' y'] p Hr y x H1 H2 H3].
    by apply inP.
    rewrite UnLift_c in H1.
    rewrite UnLift_c Lift_c.
    move: (H3). rewrite -RPath_equiv Lift_c allset_cons => [[H4 H5]].
    move: H4. rewrite /Chrel /mkset => [H4].
    have H6:  (Lift (x' :: UnLift p y'))= ((x', y') :: p)
      by apply inP; apply H1;[ | rewrite -RPath_equiv].
    apply inP. rewrite H6.
    by have -> : y=x' by [].
  Qed.
  
  (* begin snippet Lift_inj:: no-out *) 
  Lemma Lift_inj: forall (p q: seq T),
      p \in D -> Lift p = Lift q -> p = q.
  (* end snippet Lift_inj *) 
  Proof.
    rewrite /D /mkset.
    move => p q /inP H1 H2.
    move: (H1) => /Lift_sz2 H3. 
    have H4: size(q) > 1. by rewrite -Lift_sz2 -H2. 
    pose proof seq_crc H1 as [r [x [y H5]]].
    pose proof Lift_inv_sz2 H1 as H6.
    pose proof Lift_inv_sz2 H4 as H7.
    by rewrite -(H6 x) -(H7 x) H2. 
  Qed.
  
  Lemma Lift_inj': forall (p q: seq T),
      p \in D -> q \in D -> Lift p = Lift q -> p = q.
  Proof.
    move => p q /inP H1 /inP H2 H3.
    pose proof seq_crc H1 as [_ [x _]].
    have H4: UnLift (Lift p) x = UnLift (Lift q) x by rewrite H3.
    pose proof (UnLift_left x H1) as H5.
    pose proof (UnLift_left x H2) as H6.
    by rewrite -H5 -H6 H4.
  Qed.
  
  (* begin snippet Lift_surj:: no-out *) 
  Lemma Lift_surj: forall (p: seq (T*T)),
      p \in I -> exists q, q\in D /\ (Lift q)=p. 
  (* end snippet Lift_surj *) 
  Proof.
    move => p H0; move: (H0);rewrite /I /mkset => /inP [H1 H2].
    pose proof (seq_c H1) as [_ [[x _] _]].
    pose proof Lift_UnLift H0 x as H3.
    pose proof UnLift_image H0 x as H4.
    by exists (UnLift p x). 
  Qed.
  
  (** * extra results ? *)
  
  (* begin snippet Lift_Suc:: no-out *)  
  Lemma Lift_Suc: forall (p:seq T), (Lift p) [Suc\in] Chrel. 
  (* end snippet Lift_Suc *)  
  Proof.
    by move => p; rewrite -RPath_equiv; apply Lift_Lift.
  Qed.
  
  Lemma Lift_Chrel_n_imp: forall (n: nat) (spa : seq (T*T)),
      size(spa)= n.+2 -> (Lift spa) [\in] Chrel -> exists p: seq T, Lift p = spa.
  Proof.
    elim => [// | n Hr].
    - move => spa H1 H2.
      rewrite seq_rcrc0 in H1;move: H1 => [[x1 x2] [[y1 y2] H3]].
      move: H2; rewrite H3 allL0' /Chrel /mkset => /= [->].
      by (exists [::x1;y1;y2]).
    - move => spa H1 H2.
      have H4: size(spa) > 1 by rewrite H1.
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
  
  Lemma Lift_Chrel_n_iff: forall (n: nat) (spa : seq (T*T)),
      size(spa)= n.+2 -> ((Lift spa) [\in] Chrel <-> exists p: seq T, Lift p = spa).
  Proof.
    move => n spa H1;split;first by apply Lift_Chrel_n_imp with n.
    by move => [p <-]; apply Lift_Lift.
  Qed.
  
  Lemma Lift_Chrel_gt1: forall (spa : seq (T*T)),
      size(spa) > 1 -> ((Lift spa) [\in] Chrel <-> exists p: seq T, Lift p = spa).
  Proof.
    move => spa H1.
    have H0: forall (n : nat), 1 < n -> n = n.-2.+2
        by elim => [// | [// |n _ H2 ]];
                  pose proof ltn_predK H2;rewrite -H;apply succn_inj.
    have H2: (size(spa)).-2 >= 0 by [].
    split => [H3 | [p <-]].
    by apply Lift_Chrel_n_imp with (size(spa)).-2;[apply H0 |].
    by apply Lift_Lift.
  Qed.
  
  Lemma Lift_Chrel: forall (spa : seq (T*T)),
      ((Lift spa) [\in] Chrel <-> exists p: seq T, Lift p = spa).
  Proof.
    elim => [ | [x y] spa _ ];first by split => ?;[(exists [::]) |].
    elim: spa => [ | [z t] spa _]; first by split => [H2 | [p H2]];[(exists [::x;y])|].
    by apply Lift_Chrel_gt1.
  Qed.

  (* begin snippet Lift_lemma:: no-out *)  
  Lemma Lift_lemma:  image [set s | True] (@Lift T) 
                     = preimage (@Lift (T*T)) [set spa| spa [\in] Chrel].
  (* end snippet Lift_lemma *)  
  Proof. 
    rewrite /image /preimage /mkset predeqE => spa.
    by split => [[x _ <-] | /Lift_Chrel [p H1]];[ apply Lift_Lift | exists p].
  Qed.

  (* begin snippet Lift_lemma2:: no-out *)  
  Definition Im (n: nat):= image [set s | size(s)>n] (@Lift T).
  Definition Im1 (n: nat):= [set sp| exists p: seq T, Lift p = sp /\ size(p)>n].
  Definition Pre (n: nat):= 
    preimage (@Lift (T*T)) [set sp| sp [\in] Chrel /\ size(sp)> n].
  Definition Pre1 (n: nat):= [set sp| (Lift sp) [\in] Chrel /\ size(sp)>n].
  (* end snippet Lift_lemma2 *)  

  Lemma Lift_lemma2: (Im 2) = (Pre 0).
  Proof. 
    rewrite /Im /Pre /image /preimage /mkset predeqE => spa.
    split => [[x H1 <-] | [/Lift_Chrel [p H1] H2]]. 
    by split;[apply Lift_Lift | move: H1; rewrite 2!Lift_szn].
    by exists p;[rewrite -2!Lift_szn H1 |].
  Qed.

  Lemma Lift_lemma3: (Im 2) = (Im1 2).
  Proof. 
    rewrite /Im /Im1 /image /mkset predeqE => spa.
    by split => [[p H1 H2]|[p [H1 H2]]];(exists p).
  Qed.
    
  Lemma Lift_lemma4: (Pre 0) = (Pre1 1).
  Proof. 
    by rewrite /Pre /Pre1 /preimage /mkset predeqE => spa;rewrite Lift_szn.
  Qed.

End Lift_bijective.

Section epts.
  (** * endpoints  *)

  Variables (T: Type) (t:T).
  
  Definition He_D (p: seq T) := (head t p).

  Definition La_D (p: seq T) := (last t p).
  
  Definition In_D (p: seq T) := 
    behead (behead (belast t p)).

  Definition decomp (p: seq T) := (He_D p, In_D p, La_D p).
  Definition comp (tr: T*(seq T)* T) := tr.1.1::(rcons tr.1.2 tr.2).

  Lemma Lxx: forall (p:seq T), size(p)> 1 -> comp (decomp p) = p.
  Proof. 
    move => p.
    pose proof seq_cases p as [H1 | [[x H1] | [r [x [y H1]]]]];rewrite H1 //.
    move => _.
    by rewrite /decomp /comp /He_D /In_D /La_D /= belast_rcons last_rcons /=.
  Qed.

  Lemma Lyy: forall (tr: T*(seq T)* T),  decomp (comp tr) = tr.
  Proof. 
    move => [[x p] y].
    by rewrite /comp /decomp /In_D /La_D /He_D /=  belast_rcons last_rcons /=.
  Qed.
  
  Definition He_I (p: seq (T*T)) := He_D (UnLift p t).

  Definition La_I (p: seq (T*T)) := La_D (UnLift p t).
  
  Definition In_I (p: seq (T*T)) := In_D (UnLift p t).
  
  Definition D1 (x y :T) := [set p:seq T | He_D p = x /\ La_D p = y].
  Definition I1 (x y :T) := [set p:seq (T*T) | He_I p = x /\ La_I p = y ].
  
  Lemma Lift_epts_image: forall (p: seq T) (x y:T),
      p \in ((D1 x y)`&` (@D T))-> (Lift p) \in (I1 x y)`&` (@I T).
  Proof.
    move => p x y.
    move => /inP [[H1 H2] /inP H3].
    pose proof (Lift_image H3) as H4.
    move: H4 => /inP [H4 H5].
    rewrite inP /setI.
    split. 
    - rewrite /I1 /= /He_I /La_I.
      have -> : (UnLift (Lift p) t) = p 
        by rewrite Lift_sz2 in H4;apply: UnLift_left H4.
      by [].
    - by []. 
  Qed.

  Lemma UnLift_epts_image: forall (p: seq (T*T)) (x y:T),
      p \in ((I1 x y)`&` (@I T))-> (UnLift p t) \in (D1 x y)`&` (@D T).
  Proof.
    move => p x y.
    move => /inP [[H1 H2] /inP H3].
    pose proof (UnLift_image H3) t as H4.
    by rewrite inP /setI;split;[ | apply inP].
  Qed.

End epts.

Section seq_subsets.
  (** * p: seq T, p [\in] X and p [L\in] R] *)

  Variables (T: Type) (R: relation T) (X: set T).
  
  (* begin snippet Rpath_L1:: no-out *)  
  Lemma Rpath_L1: forall (p: seq T), p [\in] X -> p [L\in] (X `*` X). 
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
  
  Lemma Rpath_L2: forall (p: seq T), size(p) > 1 /\ p [L\in] (X `*` X) -> p [\in] X.
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

  Lemma Rpath_L3: forall (p: seq T), p [\in] X /\ p [L\in] R -> p [L\in] ((X `*` X)`&`R) . 
  Proof.
    move => p [/Rpath_L1 H1 H2].
    by apply allset_I; rewrite H1 H2.
  Qed.

  Lemma Rpath_L4: forall (p: seq T), size(p) > 1 /\ p [L\in] ((X `*` X)`&`R) -> p [\in] X /\ p [L\in] R.
  Proof.
    by move => p;rewrite allset_I;move => [H1 /andP [H2 H3]];split;[apply: Rpath_L2|].
  Qed.
  
  Lemma Rpath_iff1 : 
    [set p | size(p) > 0 /\ p [\in] X /\ p [L\in] R]
    = [set p | size(p) = 1 /\ (p [\in] X) ] `|` [set p | size(p) > 1 /\ p [L\in] ((X `*` X)`&`R)]. 
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
    [set p | p [\in] X /\ p [L\in] R] 
    = [set p | p = [::]] `|` [set p | size(p) > 0 /\ p [\in] X /\ p [L\in] R].
  Proof.
    rewrite /setU /mkset predeqE => [p].
    split.
    by elim: p => [[? _] // | t p _ ];[left | right].
    elim: p => [[_ /= // | [? _] //] | t p _ [? // | [_ [? ?]] //]].
  Qed.

  Lemma Rpath_iff :
    [set p | p [\in] X /\ p [L\in] R]
    =   [set p | p = [::]] 
          `|` [set p | size(p) = 1 /\ (p [\in] X) ] 
          `|` [set p | size(p) > 1 /\ p [L\in] ((X `*` X)`&`R)]. 
  Proof.
    rewrite -[RHS]setUA -[in RHS]Rpath_iff1 -[in RHS]Rpath_iff2.
    by [].
  Qed.

End seq_subsets.

Section seq_pairs_subsets.
  (** * p: seq (T*T), p [\in] E and p [L\in] R] *)
  
  Variables (T: Type).

  (* A relation on (T*T) (Ch for Chain) *)

  Definition REpaths (E: relation T) (R: relation (T*T)) := 
    [set p | p [\in] E /\ p [L\in] (@Chrel T) /\ p [L\in] R].
  
  Lemma REpath_iff1: forall (E: relation T) (R: relation (T*T)),
      [set p | p [\in] E /\ p [L\in] ((@Chrel T) `&` R)]
    = [set p | p = [::]] 
        `|` [set p | size(p) = 1 /\ (p [\in] E) ] 
        `|` [set p | size(p) > 1 /\ p [L\in] ((E `*` E)`&` ((@Chrel T) `&` R))]. 
  Proof.
    by move => E R;rewrite -[RHS]Rpath_iff.
  Qed.

  Lemma REpath_iff2: forall (E: relation T) (R: relation (T*T)),
      [set p | p [\in] E /\ p [L\in] ((@Chrel T) `&` R)]
      = [set p | p [\in] E /\ p [L\in] (@Chrel T) /\ p [L\in] R].
  Proof.
    move => E R. rewrite /mkset predeqE => p.
    split => [ [H1 /allset_I/andP [H2 H3]]// | [H1 [H2 H3]] ].
    by rewrite allset_I H1 H2 H3.
  Qed.

End seq_pairs_subsets.
  
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
