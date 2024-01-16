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

From RL Require Import  ssrel rel. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(* Notation used 
 * st is a sequence of elements of Type T
 * Variables (st: seq T).
 * stt is a sequence of elements of the product Type T*T 
 * Variables (stt: seq (T*T)).
 * On veut manipuler des relations sur T et des relations sur T*T 
 * Variables (R_T: relation T)
 * Variables (R_T2: relation T*T)
 *)

Reserved Notation "p [\in] X" (at level 4, no associativity). 
(* begin snippet all_notation:: no-out *)  
Notation "p [\in] X" := (all (fun x => x \in X) p). 
(* end snippet all_notation *)  

Section Types.
  (** * Needed Types *)
  Variables (T O: Type).
  Definition Eo (Z: Type) := prod (prod T T) Z.

End Types.

Section Utilities.
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
  
End Utilities.

Section Seq_lift. 
  (** * Lift operation on sequences *) 
    
  Variables (T: Type).
  Definition pair_rev (tt: T * T):=  (tt.2, tt.1). 
  
  (* begin snippet Lift:: no-out *)  
  Fixpoint Lift (p: seq T): seq (T * T) := 
    match p with 
    | x :: [:: y & p] as p1 => (x,y)::(Lift p1)
    | _ => @nil (prod T T)
    end.
  (* end snippet Lift *)  

  Section Lift_seq_props.
    
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
        Lift (rev p) = map pair_rev (rev (Lift p)). 
    Proof.
      elim => [// | x p Hr ];elim: p x Hr => [// | x' p _ x H1].
      by rewrite rev_cons rev_cons Lift_rcrc 
         -rev_cons H1 Lift_c rev_cons map_rcons /pair_rev.
    Qed.
    
    (** Left inverse of Lift when p is not the empty list *)

    Fixpoint UnLift (p: seq (T * T)) (x: T):= 
      match p with 
      | [::] => [::x]
      | [::(x,y) & p1 ] => [::x & UnLift p1 y]
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
    
  End Lift_seq_props.

End Seq_lift.

Section allset.
  (** * utility lemmata for seq function all used with sets*)

  Variables (T: Type) (X Y: set T) (p q: seq T) (x:T).

  (* begin snippet Sn:: no-out *)  
  Definition Sn (T:Type) (n: nat) (D: set T) := [set p | p [\in] D /\ size(p)=n].
  (* end snippet Sn *)
  
  Lemma allsetP: X x /\ p [\in] X <-> (x \in X) && (p [\in] X).
  Proof.
    by split => [[/mem_set -> ->] // | /andP [/set_mem H1 H2]].
  Qed.
  
  Lemma allset_consb: ((x::p) [\in] X) <-> (x \in X) && p [\in] X.
  Proof. by split. Qed.

  Lemma allset_cons:  ((x::p) [\in]  X) <->  X x /\ p [\in] X.
  Proof.
    by rewrite allset_consb allsetP.
  Qed.
  
  Lemma allset_subset: (X `<=` Y) -> (p [\in]  X) -> (p [\in] Y).
  Proof.
    elim: p => [ // | x' p' H1 H2 /andP [H3 H4]]. 
    apply/andP;split.
    by apply: mem_set;apply: H2; apply set_mem. 
    by apply H1.
  Qed.
  
  Lemma allset_rcons: (rcons p x) [\in] X <-> p [\in] X /\ X x.
  Proof.
    by rewrite all_rcons andC allsetP.
  Qed. 
    
  Lemma allset_rev: p [\in] X <->  (rev p) [\in] X.
  Proof.
    by rewrite all_rev.
  Qed. 
  
  Lemma allset_cat: (p++q) [\in] X <-> p [\in] X /\ q [\in] X.
  Proof.
    by rewrite all_cat;split => [/andP | [-> ->]].
  Qed.
  
End allset.

Section allset2.
  (** * all for seq (T *T) *)

  Variables (T: Type).
  
  Lemma allset_inv: forall (S: relation T) (spa: seq (T * T)), 
      spa [\in] S <-> (map (@pair_rev T) spa) [\in] S.-1. 
  Proof.
    move => S;elim => [ // | [x y] spa Hr].
    by rewrite map_cons !allset_cons Hr.
  Qed.

  Lemma allset_I: forall (R S: relation T) (spa: seq (T * T)), 
      spa [\in] (R `&` S) <-> spa [\in] R && spa [\in] S. 
  Proof.
    move => R S spa. 
    have H1: (R `&` S) `<=` S by apply intersectionSr.
    have H2: (R `&` S) `<=` R by apply intersectionSl.
    split => [H3 | ]. 
    by apply/andP;split;[apply: (allset_subset H2 H3)| apply: (allset_subset H1 H3)].
    elim: spa => [// |  x spa Hr /andP H3].
    move: H3; rewrite !allset_cons => [[[H3 H4] [H5 H6]]].
    by split;[rewrite /setI /mkset | apply Hr;apply/andP].
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
  
  Lemma allset_Dl: forall (X: set T) (S: relation T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] (Δ_(X)`;`S) -> (x::p) [\in] X.
  Proof.
    by move => X S x y p;rewrite DeltaLco allset_I => /andP [/allset_Lr H1 _].
  Qed.

  Lemma allset_Dr: forall (X: set T) (S: relation T) (x y: T) (p: seq T),
      (Lift (x::(rcons p y))) [\in] (S`;`Δ_(X)) -> (rcons p y) [\in] X.
  Proof.
    by move => X S x y p;rewrite DeltaRco allset_I => /andP [_ /allset_Rr H1].
  Qed.

End allset2.

Section allset_Lifted.
  (** *  all on a lifted sequence  *)
  
  Variables (T: Type).
  Definition allL (S: relation T) (p: seq T) (x y:T) := 
    (Lift (x::(rcons p y))) [\in] S.

  Lemma allL0 : forall (S: relation T) (x y : T),
      allL S [::] x y = ((x,y) \in S).
  Proof.
    by move => S x y;rewrite /allL Lift_c /andP /= andbT. 
  Qed.

  Lemma allL0' : forall (S: relation T) (x y : T),
      allL S [::] x y <-> S (x,y).
  Proof.
    by move => S x y;rewrite allL0;split=> [/set_mem H1 // | /inP H1]. 
  Qed.
  
  Lemma allL_c: forall (S: relation T) (p: seq T) (x y z: T),
      allL S (z::p) x y <-> ((x, z) \in S) && allL S p z y.
  Proof.
    by move => S p x y z;split;[rewrite /allL rcons_cons Lift_c allset_cons |].
  Qed.

  Lemma allL_rc: forall (S: relation T) (p: seq T) (x y z: T),
      allL S (rcons p z) x y <-> ((z,y) \in S) && allL S p x z.
  Proof.
    move => S p x y z;split.
    by rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons;move => [-> /inP ->].
    by move => /andP [/inP ? ?];rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons. 
  Qed.
  
  Lemma allL_cat: forall (S: relation T) (p q: seq T) (x y z: T),
      allL S ((rcons p y) ++ q) x z <-> allL S p x y && allL S q y z.
  Proof.
    move => S p q x y z.
    rewrite /allL cat_rcons rcons_cat rcons_cons -cat_rcons Lift_cat_crc allset_cat.
    by split => [ [? ?] | /andP [? ?]];[apply/andP |].
  Qed.
  
  Lemma allL_subset: forall (S R: relation T) (p: seq T) (x y: T),
      (S `<=` R) -> allL S p x y -> allL R p x y.
  Proof.
    by move => S R p x y H1 H2;apply allset_subset with S.
  Qed.
  
  Lemma allL_WS_iff: forall (S: relation T) (W:set T) (p: seq T) (x y: T),
      allL (Δ_(W.^c) `;` S) p x y <-> all (fun x => x \in W.^c) (x::p) && allL S p x y.
  Proof.
    move => S W p x y.
    have H1: (L_(W.^c) `&` S) `<=` S by apply intersectionSr.
    have H2: (L_(W.^c) `&` S) `<=` L_(W.^c) by apply intersectionSl.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` S) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` S) S) as H4.    
    rewrite DeltaLco /allL allset_I.
    by split => /andP [/allset_Lr H5 H6];[apply /andP | apply /andP].
  Qed.
  
  Lemma allL_SW_iff: forall (S: relation T) (W:set T) (p: seq T) (x y: T),
      allL (S `;` Δ_(W.^c)) p x y <-> all (fun x => x \in W.^c) (rcons p y) && allL S p x y.
  Proof.
    move => S W p x y.
    have H1: (S `&` L_(W.^c)) `<=` S by apply intersectionSl.
    have H2: (S `&` L_(W.^c)) `<=` L_(W.^c) by apply intersectionSr.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` S) L_(W.^c)) as H3.
    pose proof (@allset_subset (T*T) (L_(W.^c) `&` S) S) as H4.    
    rewrite DeltaRco /allL allset_I; split => /andP [H5 H6]. 
    by rewrite allset_Rr in H6; apply /andP; split. 
    by apply /andP; split;[| rewrite allset_Rr].
  Qed.
  
  Lemma allL_rev: forall (S: relation T) (p: seq T) (x y: T),
      allL S p x y <->  allL S.-1 (rev p) y x.
  Proof.
    move => S p x y. 
    have H1: (y :: rcons (rev p) x) = rev (x::(rcons p y)) by rewrite rev_cons rev_rcons -rcons_cons.
    by rewrite /allL allset_rev allset_inv H1 Lift_rev.
  Qed.
  
  Lemma allL_All: forall (S: relation T) (p: seq T) (x y: T),
      allL S p x y -> all (fun x => x \in (S.+)#_(y)) (x::p).
  Proof.
    move => S p x y.
    elim: p x. 
    by move => x;rewrite /allL /= => /andP [/inP H1 _];apply /andP;split;[apply mem_set;apply Fset_t1|].
    move => z p Hr x;rewrite allL_c => /andP [/inP H1 /Hr H2].
    move: (H2);rewrite allset_cons => [[H3 H4]].
    by rewrite allset_cons;split;[ apply Fset_t2; exists z |].
  Qed.
  
End allset_Lifted.

Section Edge_paths.
  (** * (edge) paths equivalent definitions with the help of all and Lift  *) 
    
  Variables (T: Type).
  
  (* The definition of (edge) paths of length greater or equal to one *)
  
  (* begin snippet EPath1:: no-out *) 
  Definition EPath1 (S: relation T):=[set p: seq T| (Lift p) [\in] S /\ size(p) >= 2].
  (* end snippet EPath1 *)

  (* an equivalent definition not using the lift operation *)
  Inductive EPath (S: relation T): seq T -> Prop :=
  | pp_void : EPath S [::]
  | pp_two (x: T) (ep: seq T) : 
    EPath S ep ->
    ep = [::] \/ (exists (y: T), exists (ep1: seq T), ep = [::y & ep1] /\ S (x,y))
    -> EPath S ([:: x & ep]).
  
  Definition EPath1' (S: relation T) := [set p: seq T | EPath S p /\ size(p) >= 2].

  Section EPath1_EPath1'.

    (* intermediate Lemma *)
    Lemma Epath_equiv_rc_: forall (S:relation T) (p: seq T) (x y: T),
        (Lift (x::(rcons p y))) [\in] S <-> EPath S (x::(rcons p y)).
    Proof.
      split.
      - elim: p x y => [ //= x y /andP [/inP H2 _] | z p Hr x y ].
        by apply pp_two;[ apply pp_two;[constructor | left] | right; exists y, [::]].
        rewrite rcons_cons Lift_c allset_cons andC;
            by move => [H1 H2];apply pp_two;[ apply Hr | right; exists z, (rcons p y)].
      - move => H.
        elim/EPath_ind: H => [// | x' y' ep H1 [-> // | [y1 [ep1 [H2 H3]]]]].
        by rewrite H2 in H1 *; rewrite Lift_c allset_cons //.
    Qed.
    
    Lemma Epath_equiv: forall (S:relation T) (p: seq T),
        (Lift p ) [\in] S <-> EPath S p.
    Proof.
      move => S p.
      (* we use seq_cases to explore the three cases *)
      pose proof seq_cases p as [H1 | [[x' H1] | [x' [y' [q H1]]]]];rewrite H1.
      by split => H;[apply pp_void | ].
      by split => H;[apply pp_two;[apply pp_void | left] | ].
      by rewrite Epath_equiv_rc_.
    Qed.
    
    Lemma Epath_eq: forall (S:relation T),  EPath1 S = EPath1' S.
    Proof.
      move => S.
      rewrite /EPath1 /EPath1' /mkset predeqE => p.
      split => [[H1 H2] | [H1 H2]].
      by split;[rewrite -Epath_equiv |].
      by split;[rewrite Epath_equiv  |].
    Qed.

  End EPath1_EPath1'.

End Edge_paths.

Section Lift2.
  (** * two ways to check edge paths *) 
  
  Variables (T: Type).

  (* A relation on (T*T) (Ch for Chain) *)
  (* begin snippet Chrel:: no-out *)  
  Definition Chrel  := [set ppa : (T * T)*(T * T) | (ppa.1).2 = (ppa.2).1].
  (* end snippet Chrel *)  

  Lemma Chrel_eq: forall (pa1 pa2: (T*T)), Chrel (pa1,pa2) <-> pa1.2 = pa2.1.
  Proof. by []. Qed.

  Lemma Lift_Lift: forall (p:seq T), (Lift (Lift p)) [\in] Chrel. 
  Proof.
    move => p. 
    pose proof seq_cases p as [H1 | [[x H1] | [q [x [y H1]]]]].
    (* p = [::] *) by rewrite H1. 
    (* p = [::x] *) by rewrite H1. 
    (* p = x::(rcons q y) *)
    have H2: size(p) > 1 by rewrite H1 /= size_rcons.
    pose proof seq_cc H2 as [q1 [x1 [x2 H3]]].
    rewrite H3 Epath_equiv; clear H1 H2 H3.
    elim: q1 x1 x2 => [ x' y' | y' p' Hr z' x'];first by constructor;constructor.
    by rewrite Lift_c;apply pp_two;[ | right; exists (x',y'), (Lift [::y' &p'])].
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

  Lemma Lift_lemma:  image [set s | True] (@Lift T) 
                     = preimage (@Lift (T*T)) [set spa| spa [\in] Chrel].
  Proof. 
    rewrite /image /preimage /mkset predeqE => spa.
    by split => [[x _ <-] | /Lift_Chrel [p H1]];[ apply Lift_Lift | exists p].
  Qed.

  Lemma Lift_lemma1:  
    image [set s | size(s) > 2] (@Lift T) 
    = preimage (@Lift (T*T)) [set spa| spa [\in] Chrel /\ size(spa)> 0].
  Proof. 
    rewrite /image /preimage /mkset predeqE => spa.
    split => [[x H1 <-] | [/Lift_Chrel [p H1] H2]]. 
    by split;[apply Lift_Lift | move: H1; rewrite 2!Lift_szn].
    by exists p;[rewrite -2!Lift_szn H1 |].
  Qed.
  
  Lemma Lift_lemma2:
    preimage (@Lift (T*T)) [set spa| spa [\in] Chrel /\ size(spa)> 0] 
    = [set spa | (Lift spa) [\in] Chrel /\ size(spa) > 1].
  Proof. 
    rewrite /preimage /mkset predeqE => spa. 
    by rewrite Lift_szn.
  Qed.

  Lemma Lift_lemma3:
    image [set s | size(s) > 2] (@Lift T) 
    =  [set spa | exists p: seq T, Lift p = spa /\ size(p) > 2].
  Proof. 
    rewrite /image /mkset predeqE => spa.
    by split => [[p H1 H2]|[p [H1 H2]]];(exists p).
  Qed.

  (* begin snippet EPath2new:: no-out *) 
  Definition EPath2'' (S: relation T):=
    [set spa | spa [\in] S /\ (Lift spa) [\in] Chrel /\ size(spa) > 0].
  (* end snippet EPath2new *)
  
  (* begin snippet EPath3new:: no-out *) 
  Definition EPath3'' (S: relation T):=
    [set spa | spa [\in] S /\ (exists p, (Lift p) =spa /\ size(p) > 1)].
  (* end snippet EPath3new *)
  
  Lemma EP2_lemma: forall (S: relation T), 
      EPath2'' S = [set spa | spa [\in] S] `&` [set spa | (Lift spa)  [\in] Chrel /\ size(spa) > 0].
  Proof.
    by move => S;rewrite /EPath2'' /setI /mkset predeqE => spa.
  Qed.

  Lemma EP3_lemma: forall (S: relation T), 
      EPath3'' S =[set spa | spa [\in] S] `&` [set spa | (exists p, (Lift p) =spa /\ size(p) > 1)].
  Proof.
    by move => S;rewrite /EPath3'' /setI /mkset predeqE => spa.
  Qed.

  Lemma EP_equiv: forall (S: relation T), 
      EPath2'' S = EPath3'' S.
  Proof.
    move => S;rewrite /EPath2'' /EPath3'' /setI /mkset predeqE => spa.
    split. 
    move => [H1 [/Lift_Chrel [p H2] H3]].
    split. by []. exists p. split. by []. by rewrite -Lift_sz2 H2.
    move => [H1 [p [H2 H3]]].
    split. by []. split. rewrite Lift_Chrel. by exists p. by rewrite -H2  Lift_sz2.
  Qed.
  
End Lift2.

Section Seq_liftO. 

  (** * from (seq: A) (seq:O) to seq: A *A * O *)
  
  Variables (T: Type).
  (* orientation  *)
  (* begin snippet O:: no-out *)
  Inductive O := | P | N.
  (* end snippet O *)
  Definition O_rev (o:O) := match o with | P => N | N => P end.
  
  Record Svo := { sv: seq T; so: seq O; len: size(sv) = (size(so)).+1}.

  Lemma test: forall (sv : seq T) (so : seq O), 
       size(so) > 0 
       -> size(sv) = (size(so)).+1 
       -> size(behead sv)  = (size(behead so)).+1.
  Proof.
    move => sv so.
    elim: so sv. 
    move => so. by [].
    move => o so' Hr so /= H1 H2. 
    by rewrite size_behead H2.
  Qed.

  Lemma svo_rec : forall (svo: Svo),
      size(so svo) > 0 
      -> size(behead (sv svo)) = (size(behead (so svo))).+1.
  Proof.
    move => svo H1. apply: (test H1 (len svo)).
  Qed.

  Lemma test1: forall (s : Svo), size (sv s) = (size(so s)).+1.
  Proof.
    by move => [a b c].
  Qed.
  
  (* begin snippet Oedge:: no-out *)  
  Definition Oedge (S: relation T): set (T*T*O) :=
    fun (oe: Eo T O) => match oe with | (e,P) => S e | (e,N) => S.-1 e end.
  (* end snippet Oedge *)

  Lemma Oedge_rev: forall (S: relation T) (x y: T),
      Oedge S (x,y,P) = Oedge S (y,x,N).
  Proof.
    by move => S x y.
  Qed.
  
  Lemma Oedge_inv: forall (S: relation T) (x y: T) (o:O),
      Oedge S (x,y,o) = Oedge S.-1 (x,y, O_rev o).
  Proof.
    by move => S x y; elim. 
  Qed.

  (* begin snippet pair:: no-out *)  
  Fixpoint pair (spa: seq (T * T)) (so: seq O):= 
    match spa, so with 
    | pa::spa, o::so => (pa,o)::(pair spa so)
    | pa::spa, [::] => (pa,P)::(pair spa [::])
    |  _ , _ => @nil (Eo T O)
    end.
  (* end snippet pair *)  
  Lemma pair_c: forall (spa: seq (T * T)) (so: seq O) (pa: T * T),
      pair (pa::spa) so = (pa,head P so )::(pair spa (behead so)).
  Proof.
    elim => [ so pa // | pa1 spa Hr so pa ]; first by elim: so => [// | o so _ //].
    elim: so => [// | o so _ ].
    have -> : pair [:: pa, pa1 & spa] (o :: so) = (pa,o)::(pair [::pa1 & spa] so) by [].
    by rewrite Hr.
  Qed.

  Lemma pair_cat: forall (p q: seq (T * T)) (sop soq: seq O),
      size sop = size p ->
      pair (p++q) (sop++soq) = (pair p sop) ++ (pair q soq).
  Proof.
    elim => [ q sop soq /eqP //= /nilP -> //= | ].
    move => a p Hr q sop soq H1.
    elim: sop H1 Hr => [// | so1 sop H1 H2 H3].
    rewrite cat_cons cat_cons pair_c //=.
    have H4: size sop = size p. by rewrite /size in H2; apply succn_inj.
    have -> : pair (p ++ q) (sop ++ soq) = pair p sop ++ pair q soq 
      by apply H3.
    by [].
  Qed.
  
  Fixpoint unpair_A (spao: seq (Eo T O)) :=
    match spao with 
    | [::] => [::]
    | (pa,o)::spao => (pa)::(unpair_A spao)
    end.

  Lemma unpair_A_c: forall (spao: seq (Eo T O)) (pa: T * T) (o: O),
      unpair_A ((pa,o)::spao) = pa::(unpair_A spao).
  Proof.
    by [].
  Qed.
  
  Lemma pair_invl: forall (spa: seq (T * T)) (so: seq O),
      unpair_A (pair spa so) = spa.
  Proof.
    elim => [// | pa spa Hr so].
    elim: so Hr => [ Hr // | o so _ Hr ];
                  match goal with _ => by rewrite pair_c unpair_A_c Hr end.
  Qed.
  
  Fixpoint unpair_O (spao: seq (Eo T O)) :=
    match spao with 
    | [::] => [::]
    | (pa,o)::spao => o::(unpair_O spao)
    end.

  Fixpoint pair_o (spa: seq (T * T)) (o: O):= 
    match spa with
    | [::] => @nil (Eo T O)
    | pa::spa => (pa,o)::(pair_o spa o)
    end.
    
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

  (** pair_o as  pair *)
  Lemma pair_o_iff: forall (spa: seq (T * T)) (o: O),
      pair_o spa o = pair spa (nseq (size spa) o).
  Proof.
    by elim => [ // | pa spa Hr o ];rewrite pair_c pair_o_c Hr.
  Qed.

  (* begin snippet LiftO:: no-out *)  
  Definition LiftO (sa: seq T) (so: seq O) := pair (Lift sa) so.
  (* end snippet LiftO *)  
  
  Definition Lifto (sa: seq T) (o: O) := pair_o (Lift sa) o.
  
  Section LiftO_seq_props.
    
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
    
    Definition UnLiftO_A (p: seq (Eo T O)) (x: T) := UnLift (unpair_A p) x.
    
    Definition UnLiftO_O (p: seq (Eo T O)) := unpair_O p.
    
    Lemma UnLiftO_A_c: forall (p: seq (Eo T O)) (x y: T) (o:O),
        UnLiftO_A ((x, y, o) :: p) x = [::x & UnLiftO_A p y].
    Proof.
      by [].
    Qed.
    
    Lemma LiftO_A_inv: forall (p : seq T) (so: seq O) (x y: T) (o:O),
        UnLiftO_A (LiftO [::x,y & p] [::o & so]) x = [::x,y & p].
    Proof.
      by move => p so x y o;rewrite /LiftO /UnLiftO_A pair_invl Lift_inv.
    Qed.

    Lemma LiftO_A_inv1: forall (p : seq T) (so: seq O) (x y: T) (o:O),
        UnLiftO_A (LiftO (x::(rcons p y)) [::o & so]) x = (x::(rcons p y)).
    Proof.
      by move => p so x y o;rewrite /LiftO /UnLiftO_A pair_invl Lift_inv1.
    Qed.
    
    Lemma LiftO_A_inv2: forall (p : seq T) (so: seq O) (x y: T) (o:O),
        p <> [::] -> UnLiftO_A (LiftO p so) (head x p) = p.
    Proof.
      by move => p so x y o H1;rewrite /LiftO /UnLiftO_A pair_invl Lift_inv2.
    Qed.
    
  End LiftO_seq_props.
  
  Section Lifto_seq_props.
    (** Lifto properties herited from Lift *) 
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
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    elim/last_ind => [o x y // | p t Hr o x z].
    by rewrite /Lifto Lift_crc H1. 
  Qed.

  Lemma Lifto_head1: forall (p:seq T) (o:O) (x z: T),
      head (last x p, z ,o) (Lifto (x::p) o) = (x, head z p, o).
  Proof.
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    elim/last_ind => [o x y // | p t Hr o x z].
    by rewrite /Lifto Lift_crc H1. 
  Qed.
  
  Lemma Lift_o_cons: forall (p:seq T) (o:O) (x y z: T),
      Lifto (x::(rcons (z::p) y)) o = (x,z,o)::(Lifto (z::(rcons p y)) o).
  Proof.
    move => p o x y z;rewrite Lifto_crc //.
  Qed.
  
  Lemma Lift_o_start_end: forall (p q: seq T) (x y t: T),
      exists (x' y': T) (r: seq (Eo T O)), 
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
  
  Lemma Lifto_inv1: forall (p: seq T) (x y: T),
      UnLiftO_A (Lifto (x::(rcons p y)) N) x = x::(rcons p y).
  Proof.
    by move => p x y;rewrite /Lifto /UnLiftO_A pair_o_iff pair_invl Lift_inv1.
  Qed.

  Lemma Lifto_inv3: forall (p q: seq T) (x y t: T),
      UnLiftO_A ((Lifto (x::(rcons p t)) N)++(Lifto (t::(rcons q y)) P )) x =
        x :: rcons (rcons p t ++ q) y.
  Proof.
    move => p q x y t;rewrite /Lifto /UnLiftO_A. 
    rewrite !pair_o_iff -pair_cat.
    by rewrite pair_invl -Lift_cat_crc -rcons_cat Lift_inv1.
    by rewrite size_nseq.
  Qed.

  End Lifto_seq_props.

  (* begin snippet EoPath1:: no-out *)  
  
  (* end snippet EoPath1 *)
  
End Seq_liftO.


Section PathRel.
  (** * transitive closure and paths
   * the main result here is that the relation in AxA obtained 
   * by fun (x y : T) => (exists (p: seq T), AllL S p x y)
   * is the relation S.+ the transitive closure of S 
   *)

  Variables (T: Type) (S: relation T).
  
  (* relation based on paths: take care that the path p depends on (x,y) *)
  Definition PathRel_n (S: relation T) (n:nat) :=
    [set x | (exists (p: seq T), size(p)=n /\ allL S p x.1 x.2)].

  (* composition and existence of paths coincide *)
  Lemma Itern_iff_PathReln : forall (n:nat), S^(n.+1) =  PathRel_n S n.
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
  
  (* relation based on paths: take care that the path p depends on (x,y) *)
  Definition PathRel (S: relation T) := 
    [set x | (exists (p: seq T), allL S p x.1 x.2)].
  
  (* R.+ =  PathRel R *)
  Lemma clos_t_iff_PathRel: S.+ =  PathRel S.
  Proof.
    rewrite /mkset predeqE => [[x y]].
    split => [H1 | [p H1]].
    - apply clos_t_iterk in H1.
      move: H1 => [n H1].
      rewrite  Itern_iff_PathReln /PathRel_n in H1.
      move: H1 => [p [H1 H2]].
      by (exists p).
    - have H2:  PathRel_n S (size p) (x, y) by (exists p).
      rewrite -Itern_iff_PathReln in H2.
      by apply iterk_inc_clos_trans in H2.
  Qed.

End PathRel.

Section PathRel_Examples.
  (* Applications *)
  
  Variables (T: Type) (S: relation T) (W: set T).

  Lemma clos_t_to_paths_l : forall (x y: T),
      (Δ_(W.^c) `;` S).+ (x, y) ->
      (exists (p: seq T), all (fun x => x \in W.^c) (x::p) /\ allL S p x y
                     /\ all (fun x => x \in ((Δ_(W.^c) `;` S).+)#_(y)) (x::p)).
  Proof.
    move => x y; rewrite {1}clos_t_iff_PathRel; move => [p /= H1]; exists p.
    move: (H1) => /allL_WS_iff/andP [H2 H2'].
    apply allL_All in H1;apply allset_cons in H1;move: H1=> [/inP H1 H1'].
    by rewrite -allset_consb H1 H1' andbT.
  Qed.
  
  Lemma clos_t_to_paths_r : forall (x y: T),
      (S `;` Δ_(W.^c)).+ (x, y) ->
      (exists (p: seq T), (all (fun z => z \in W.^c) (rcons p y) /\ allL S p x y)
                     /\ all (fun z => z \in ((Δ_(W.^c) `;` S.-1).+)#_(x)) (y::(rev p))).
  Proof.
    move => x y; rewrite {1}clos_t_iff_PathRel; move  => [p H1]; exists p.
    rewrite allL_rev inverse_compose DeltaE_inverse /= in H1.
    move: (H1) => /allL_WS_iff/andP /= [/andP [/inP H2 H3] H2'].
    apply allL_All in H1;apply allset_cons in H1;move: H1=> [/inP /= H1 H1'].
    by rewrite H1 H1' andbT allL_rev H2' allset_rcons allset_rev H3. 
  Qed.
  
End PathRel_Examples.

Section Active_relation.
  (** * relation on EO where EO = (AxA)xO
   * this section is to be merged with previous stuffs 
   *)
  Variables (T: Type).
  
  (* A relation on (Eo) *)
  Definition ComposeOe' (oe1 oe2: Eo T O):= oe1.1.2 = oe2.1.1.

  Definition ComposeOe := 
    [set eo : (Eo T O) * (Eo T O) | eo.1.1.2 = eo.2.1.1].
  
  Lemma ComposeOe_eq: forall (x y z t: T) (o1 o2:O),
      ComposeOe ((x,y,o1), (z,t,o2)) <-> y = z.
  Proof. by []. Qed.

  (* Active as a relation on Eo) *)
  Definition ActiveOe (W: set T) (S: relation T) := 
    [set oe : (Eo T O) * (Eo T O) | 
      Oedge S oe.1 /\ Oedge S oe.2 /\ (ComposeOe oe)
      /\ match (oe.1.2,oe.2.2, oe.1.1.2) with 
        | (P,P,v) => W.^c v
        | (N,N,v) => W.^c v
        | (N,P,v) => W.^c v
        | (P,N,v) => (Fset S.* W) v
        end].
    
  Lemma ActiveOe_Oedge: forall (W: set T) (S: relation T) (eo : (Eo T O) * (Eo T O)),
      (ActiveOe W S) eo -> Oedge S eo.1 /\ Oedge S eo.2.
  Proof.
    by move => W S eo [H1 [H2 _]].
  Qed.

  Lemma ActiveOe_Compose: forall (W: set T) (S: relation T) (eo : (Eo T O) * (Eo T O)),
      eo \in (ActiveOe W S) -> ComposeOe eo. 
  Proof.
    by move => W S eo /inP [_ [_ [H3 _]]].
  Qed.
  
  Lemma ActiveOe_o: forall (W: set T) (S: relation T) (x y z: T) (o:O),
      (ActiveOe W S) ((x,y,o),(y,z,o)) <-> (Oedge S (x,y,o)) /\ (Oedge S (y,z,o)) /\ W.^c y.
  Proof.
    move => W S x y z o;rewrite /ActiveOe /mkset /ComposeOe /=.
    case: o.
    by split => [[? [? [_ ?]]] // | [? [? ?]]].
    by split => [[? [? [_ ?]]] // | [? [? ?]]].
  Qed.
  
  Lemma ActiveOeT: forall (W: set T) (S: relation T) (x u v z t: T) (o1 o2 o3 o4:O),
      (Fset S.* W) x 
      /\ ActiveOe W S ((u,x,o1), (x,v,o2)) /\ ActiveOe W S ((z,x,o3), (x,t,o4))
      -> ActiveOe W S ((u,x,o1), (x,t,o4)).
  Proof.
    move => W S x u v z t o1 o2 o3 o4.
    case: o1;case: o2; case:o3; case:o4;
      by move => [H0 [[H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]]]].
  Qed.
  
  Lemma ActiveOe_rev: forall (W:set T) (S: relation T) (e1 e2: (T * T)) (o:O),
      (ActiveOe W S).-1 ((e1,o), (e2,o)) <-> ActiveOe W S.-1 ((e2,O_rev o), (e1,O_rev o)).
  Proof.
    by move => W S [x1 y1] [x2 y2] o; case: o. 
  Qed.

End Active_relation.

Section Active_paths. 
  (** * Active paths  *)
  Variables (T: Type) (W: set T) (S: relation T).
  (* orientation  *)
  Definition EO := Eo T O.
  
  (* Active is now almost expressed as a transitive closure 
   * on an lifted space (A * A) * O as it uses AllL *)
  Definition Active_path
    (W: set T) (S: relation T) (p: seq EO) (x y: T) :=
    match p with 
    | [::] => x = y 
    | [::eo1] => eo1.1.1 = x /\  eo1.1.2 = y /\  Oedge S eo1 
    | eo1 :: [:: eo2 & p]
      => eo1.1.1 = x /\ (last eo2 p).1.2 = y 
        /\ allL (ActiveOe W S) (belast eo2 p) eo1 (last eo2 p)
    end.
  
  Definition R_o (o:O):= match o with | P => S | N=> S.-1 end.

  Lemma R_o': forall (o:O) (xy: T*T),
      R_o o xy <-> match o with | P => S xy | N=> S.-1 xy end.
  Proof.
    by move => o xy; case: o.
  Qed.

  (** increase active path by left addition *)
  Lemma Active_path_cc: forall (p: seq EO) (eo1 eo2:  EO) (y: T),
      Active_path W S [:: eo1, eo2 & p] eo1.1.1 y
      <-> Active_path W S [:: eo2 & p] eo2.1.1 y /\ ActiveOe W S (eo1, eo2).
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
  
  Lemma Active_path_cc_ht: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W S [:: eo1, eo2 & p] x y -> 
      x = eo1.1.1 /\ y = (last eo2 p).1.2.
  Proof.
    by move => p eo1 eo2 x y [H1 [H2 _]].
  Qed. 
  
  Lemma Active_path_cc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W S [:: eo1, eo2 & p] x y -> ActiveOe W S (eo1, eo2) .
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_cc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_cc [_ H1].
  Qed.
  
  Lemma Active_path_crc: forall  (p: seq EO) (eo1 eo2:  EO),
      Active_path W S (eo1::(rcons p eo2)) eo1.1.1 eo2.1.2
      <-> allL (ActiveOe W S) p eo1 eo2.
  Proof.
    elim => [ | eo p H1] eo1 eo2;
           first by split;[move => [_ [_ /= H2]] |move => H1;split;[ |split]].
    split; rewrite rcons_cons.
    move => /Active_path_cc [H2 /inP H3]. 
    by rewrite allL_c; apply/andP; split;[ | apply H1].
    by move => H2;split;[ | split;[ rewrite last_rcons | rewrite belast_rcons last_rcons]].
  Qed.
  
  Lemma Active_path_crc_ht: forall  (p: seq EO) (eo1 eo2: EO) (x y: T),
      Active_path W S (eo1::(rcons p eo2)) x y -> eo1.1.1 = x /\  eo2.1.2 = y.
  Proof.
    move => p eo1 eo2 x y;rewrite headI;move => [H1 [H2 _]].
    by elim: p H2 => [ //= | a p _ //=]; rewrite last_rcons.
  Qed.
  
  Lemma Active_path_crc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W S (eo1::(rcons p eo2)) x y
      -> ActiveOe W S (eo1, (head eo2 p)) /\ ActiveOe W S ((last eo1 p), eo2).
  Proof.
    elim => [eo1 eo2 x y [_ [/= _ /allL0' H4]] // | eo3 p H1 eo1 eo2 x y].
    rewrite rcons_cons. move => H2.
    pose proof Active_path_cc_ht H2 as [H3 H4].
    pose proof Active_path_cc_a H2 as H5.
    move: H2;rewrite H3 Active_path_cc;move => [H6 H7].
    apply H1 in H6 as [H6 H8].
    by split;[ | rewrite last_cons].
  Qed.
  
  Lemma Active_path_rcrc: forall (p: seq EO) (eo1 eo2:  EO),
      Active_path W S (rcons (rcons p eo1) eo2) (head eo1 p).1.1 eo2.1.2
      <-> Active_path W S (rcons p eo1) (head eo1 p).1.1 eo1.1.2
        /\ ActiveOe W S (eo1, eo2).
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

  Lemma Active_path_rcrc_ht: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W S (rcons (rcons p eo1) eo2) x y 
      -> x = (head eo1 p).1.1 /\ y= eo2.1.2.
  Proof.
    elim => [ | eo p H1] eo1 eo2 x y; first by move => [H1 [H2 _]]; split.
    by rewrite !rcons_cons => /Active_path_crc_ht [H2 H3].
  Qed.

  Lemma Active_path_rcrc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W S (rcons (rcons p eo1) eo2) x y 
      -> ActiveOe W S (eo1, eo2).
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_rcrc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_rcrc [_ H1].
  Qed.

  Lemma Active_path_rc_hto: forall (p: seq EO) (eo1:  EO) (x y: T),
      Active_path W S (rcons p eo1) x y ->
      x = (head eo1 p).1.1 /\ y = eo1.1.2 
      /\ Oedge S eo1 /\ Oedge S (head eo1 p).
  Proof.
    elim => [eo1 x y [H2 [H3 H4]] // | eo2 p _ eo1 x y H1]. 
    by pose proof Active_path_crc_ht H1 as [H2 H3];
    pose proof Active_path_crc_a H1 as [[H4 _] [_ [H8 _]]].
  Qed.
  
  Lemma Active_path_c_hto: forall (p: seq EO) (eo1:  EO) (x y: T),
      Active_path W S (eo1::p) x y -> 
      x = eo1.1.1 /\ y = (last eo1 p).1.2
      /\ Oedge S eo1 /\ Oedge S (last eo1 p).
  Proof.
    elim => [eo1 x y [H1 [H2 H3]] // | eo2 p _ eo1 x y H1]. 
    pose proof Active_path_cc_ht H1 as [H2 H3];
      pose proof Active_path_cc_a H1 as [H4 [H5 _]]. 
    rewrite lastI in H1.
    by pose proof Active_path_rc_hto H1 as [_ [_ [H8 _]]].
  Qed.
    
  Lemma Active_path_split: forall (p q: seq EO) (eop eoq:  EO) (x y: T),
      Active_path W S ((rcons p eop)++ eoq::q) x y
      -> Active_path W S (rcons p eop) x eop.1.2
        /\ Active_path W S (eoq::q) eoq.1.1 y
        /\ ActiveOe W S (eop, eoq).
  Proof.
    elim => [ q eop eoq x y // | z p Hr q eop eoq x y ].
    - rewrite cat_rcons cat0s => H1.
      pose proof Active_path_cc_ht H1 as [H2 _].
      pose proof Active_path_cc_a H1 as [H3 _].
      by move: H1; rewrite H2 Active_path_cc; move => [H4 H5];split.
    - elim/last_ind: q Hr eop eoq x y.
      + move => _ eop eoq x y.
        rewrite -cat_rcons cats0 => H1.
        pose proof Active_path_rcrc_ht H1 as [H2 H3].
        move: H1; rewrite H2 H3 Active_path_rcrc; move => [H4 H5]. 
        by pose proof H5 as [H6 [H7 _]].
      + move => q1 t _ H1 eo1 eo2 x y H3.
        rewrite rcons_cons cat_cons -rcons_cons -rcons_cat in H3.
        pose proof Active_path_crc_ht H3 as [H4 H5].
        move: H3; rewrite -H4 -H5.
        move => /Active_path_crc /allL_cat/andP [H6 /allL_c/andP [/inP H7 H8]]. 
        by rewrite rcons_cons Active_path_crc Active_path_crc.
  Qed.
  
  Lemma Active_path_cat: forall (p q: seq EO) (eop eoq :EO) (x y z: T),
      ActiveOe W S (eop, eoq)
      /\ Active_path W S (rcons p eop) x y 
      /\ Active_path W S (eoq::q) y z
      -> Active_path W S (rcons p eop++ eoq::q) x z.
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

  Lemma Active_path_iff: forall (p q: seq EO) (eop eoq :EO) (x y z: T),
      ActiveOe W S (eop, eoq)
      /\ Active_path W S (rcons p eop) x y 
      /\ Active_path W S (eoq::q) y z
      <-> Active_path W S (rcons p eop++ eoq::q) x z /\ y= eop.1.2.
  Proof.
    move => p q eop eoq x y z.
    split => [ [H1 [H2 H3]] | [H1 H2]].
    - pose proof Active_path_rc_hto H2 as [_ [H4 _]].
      by split;[apply Active_path_cat with y | ].
    - pose proof Active_path_split H1 as [H3 [H4 H5]].
      pose proof H5 as [_ [H7 [H8 _]]].
      by split;[ | split;[rewrite H2 | rewrite H2 H8]].
  Qed.
  
  Lemma Active_path_cat': forall (p q: seq EO) (x y z: T),
      (exists (p' q': seq EO), exists (eop eoq: EO),
          p = rcons p' eop /\ q = eoq::q' /\  ActiveOe W S (eop, eoq))
      /\ Active_path W S p x y 
      /\ Active_path W S q y z
      -> Active_path W S (p++q) x z.
  Proof.
    move => p q x y z [[p1 [q1 [eop [eoq [H1 [H2 H3]]]]]] [H4 H5]].
    by rewrite H1 H2; apply Active_path_cat with y; rewrite -H1 -H2.
  Qed.

  
  Section Active_path_unique. 

    (** * If there exists an active path from x to y there exists a walk from x to y
        we just prove that when a variable is repeated twice we can shorten the
        active path * to prove the general property, we have maybe to switch from
        Type to eqType to use unique * in seq ?  *)
    
    Lemma Oedge_Fset:  forall (u v: T), Oedge S (u,v, P) /\ S.*#W v -> S.*#W u.
    Proof.
      move => u v [H1 H2]. 
      move: H2 => [w [H2 H3]].
      have H4: (S `;` S.* ) (u,w) by (exists v).
      have H5:  (S.+ `<=` S.*) by apply clos_t_clos_rt.
      have H6: S.* (u, w) by rewrite r_clos_rt_clos_t in H4 ;apply H5 in H4.
      by (exists w).
    Qed.
  
    Lemma Active_path_Fset:  forall (p: seq T) (x y: T),
        Active_path W S ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ S.*#W (last y p) -> S.*#W x. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        move => x y [[_ [_ H2]] H3].
        by apply Oedge_Fset with y.
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc. 
        move => [[H1 H2] H3].
        have H4: S.*#W y by apply Hr with z.
        move: H2 => [H2 _].
        by apply Oedge_Fset with y.
    Qed.
    
    Lemma Active_path_Fset':  forall (p: seq T) (x y: T),
        Active_path W S ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ S.*#W (last y p) -> S.*#W y. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        by move => x y [[_ [_ H2]] H3].
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc.
        move => [[H1 H2] H3].
        have H4: S.*#W z by apply Hr with y.
        move: H2 => [_ [H2 _]].
        by apply Oedge_Fset with z.
    Qed.
    
    Lemma Active_path_shorten_L1: forall (p: seq EO) (x y z u v w: T),
        Active_path W S [::(x,y,P),(y,z,P) & (rcons (rcons p (u,v,N)) (v,w,N))] x w
        -> exists (q: seq T), Active_path W S (Lifto [::x,y & q] P) x (last y q) 
                        /\ (Fset S.* W) (last y q).
    Proof. 
      elim => [x y z u v w| ].
      - rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons Active_path_rcrc.
        have -> : [:: (x, y, P); (y, z, P)] = rcons [:: (x, y, P)]  (y, z, P) by [].
        rewrite Active_path_rcrc /head.
        move => [[H1 [H'2 [H'3 [/ComposeOe_eq H'4 H'5]]]] [H3 [H4 [_ H6]]]].
        by (exists [::z]).
      - move => [[t s] o] p Hr x y z u v w.
        rewrite rcons_cons rcons_cons Active_path_cc.
        elim: p Hr.
        + move => Hr [H1 H2].
          move: (H1); rewrite Active_path_cc => [[_ [_ [_ [/ComposeOe_eq H3 _]]]]];
                                               rewrite <- H3 in *.
          elim: o H1 => [ /Hr [q [H1 H4]] | ].
          ++ exists [:: z & q].
             by rewrite Lifto_c Lifto_c Active_path_cc -Lifto_c /last_cons. 
          ++ exists [::z].
             move: H1 => /Active_path_cc [H1 [_ [_ [_ H7]]]]. 
             move: (H2) => [H2' [H2'' _]].
             rewrite !Lifto_c Active_path_cc -Lifto_c /last.
             by split.
        + move => [[a b] o2] p _ H1 H2.
          move: (H2);rewrite Active_path_cc rcons_cons rcons_cons;
            move => [[_ [_ [_ [/ComposeOe_eq H6 _]]]] _].
          rewrite <- H6 in *; clear H6.
          elim: o H2 => [[H2 H3] | ].
          ++ apply H1 in H2;move:H2 => [q H2].
             exists [::z].
             move: H2;rewrite Lifto_c => [[H2 H4]].
             rewrite /Lifto /Lift /pair_o.
             rewrite Active_path_cc last_cons /last.
             move: (H3) => [H5 [H6 _]].
             specialize Active_path_Fset' with q y z => H7.
             by split;[split | apply H7].
          ++ move => [H2 H3].
             pose proof H2 as H5.
             rewrite Active_path_cc in H2.
             rewrite Active_path_crc in H2.
             move: H2 => [H2 [_ [_ [_ H8 ]]]].
             exists [::z];rewrite last_cons /last.
             split. 
             by rewrite /= allL0'.
             by [].
    Qed.
    
    Lemma Active_path_shorten_L2: forall (p: seq EO) (x y z u w: T),
        Active_path W S [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> S.*#W y. 
    Proof. 
      move => p x y z u w H1.
      pose proof Active_path_shorten_L1 H1 as [q H2].
      rewrite Lifto_c in H2.
      by apply  Active_path_Fset' in H2.
    Qed.

    Lemma Active_path_shorten_L3: forall (p: seq EO) (x y z u w: T),
        Active_path W S [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> ActiveOe W S ((x,y,P), (y,w,N)).
    Proof. 
      move => p x y z u w H1.
      move: (H1) => /Active_path_shorten_L2 H2.
      pose proof Active_path_cc_a H1 as [H3 _].
      move: (H1); rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons. 
      move => /Active_path_rcrc_a [_ [H4 _]].
      by [].
    Qed.
    
    (* the only complex case is (o1 o2 o3 o4)= ( P P N N) which was is treated 
       in the previous lemmata *) 
    Lemma Active_path_shorten: forall (p: seq EO) (x y z u w: T) (o1 o2 o3 o4:O) ,
        Active_path W S [::(x,y,o1),(y,z,o2) & (rcons (rcons p (u,y,o3)) (y,w,o4))] x w
        -> ActiveOe W S ((x,y,o1), (y,w,o4)).
    Proof. 
      move => p x y z u w o1 o2 o3 o4 H1. 
      move: (H1); rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons. 
      move => /Active_path_rcrc_a [_ [H2 [_ H3]]].
      move: o1 o2 o3 o4 H1 H2 H3.
      case; case; case; case;
        move => H1 H2 H3;
               pose proof Active_path_cc_a H1 as [H4 [_ [_ H5]]];
               move: H5 => //= H5;move: H3 => //= H3.
      by apply Active_path_shorten_L3 with p z u.
    Qed.
    
  End Active_path_unique. 
   
End Active_paths.   

Section Active. 
  (** * The Active relation as a relation on AxA *)

  Variables (T: Type). 
  
  Definition Active (W: set T) (S: relation T) (x y: T) :=
   (exists (p: seq (Eo T O)), Active_path W S p x y).

  Definition D_separated  (W: set T) (S: relation T) (x y: T) := 
    ~(Active W S x y).

  Lemma Deployment_to_Active_path:
    forall (W: set T) (S: relation T) (p: seq T) (x y: T) (o:O),
      ( all (fun x => x \in W.^c) p /\ allL (R_o S o) p x y )
        <-> Active_path W S (Lifto (x::(rcons p y)) o) x y.
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
      move => x y H1 /Active_path_cc [H2 [H3 [H4 [H5 H6]]]]. 
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
          split;[ | move: H4 => [_ [_ [_ H4]]]].
        by elim: o H2 H4 H5 => _ H4 H5.
        by elim: o H2 H4 H5 => _ /= H4 H5.
        rewrite allL_c H5 andbT.
        by elim: o H2 H4 H5 => _ [/= /inP H4 _] _ /=.
  Qed.
  
  Lemma Deployment_to_Active: forall (W: set T) (S: relation T) (p: seq T) (x y: T),
      (all (fun x => x \in W.^c) p /\ allL S p x y) -> Active W S x y.
  Proof.
    move => W S p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) P); apply Deployment_to_Active_path;split.
  Qed.

  Lemma Deployment_inv_to_Active: forall (W: set T) (S: relation T) (p: seq T) (x y: T),
      (all (fun x => x \in W.^c) p /\ allL S.-1 p x y) -> Active W S x y.
  Proof.
    move => W S p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) N); apply Deployment_to_Active_path;split.
  Qed.

End Active. 


Section Wip.
  (** * test to check how to prove that active path can be chosen uniq *)

  (* we use eqType here *)
  Variables (T: eqType).
  
  Lemma trunck_seq: forall (x: T) (p: seq T),
      ((x \in p) /\ exists (p1:seq T) , x \notin p1 /\ exists p2, (p= p1 ++ (x::p2)))
      \/ ~ (x \in p).
  Proof.
    move => x' p.
    elim: p => [ | x p [[H1 [p1 [H2 [p2 H3]]]] | H1] ].
    - by right.
    - left; split;first by rewrite in_cons H1 orbT.
      case Hx: (x'== x). 
      + by move: Hx => /eqP <-;(exists [::]);split;[|exists p].
      + by exists(x::p1);split;[rewrite in_cons Hx H2 | (exists p2); rewrite H3].
            - case Hx: (x'== x);last by right;rewrite in_cons Hx /=.
              left;split;first by rewrite in_cons Hx /=.
              by exists[::]; split;[ | exists p; move: Hx => /eqP ->].
  Qed.

  (* general property of seq *)
  Lemma trunck_seq_rev: forall (x: T) (p: seq T),
      ((x \in p) /\ exists (p1 p2:seq T), x \notin p2 /\ p= p1 ++ (x::p2))
      \/ ~ (x \in p).
  Admitted.
  
  (* P is compatible with truncation *)
  Axiom trunck_seq_P: forall (x: T) (p p1 p2: seq T) (P: T -> (seq T) -> Prop),
      P x p -> p = p1 ++ (x::p2) -> P x p2.
  
  (* existence with uniq *)
  Lemma P_uniq: forall (x: T) (p: seq T) (P: T-> (seq T) -> Prop),
      P x p -> exists (p2:seq T), x \notin p2 /\ P x p2.
  Proof.
    move => x p P H1.
    case Hx: (x \in p); last first.
    by (exists p);split;[rewrite Hx /= |].
    pose proof trunck_seq_rev x p as [[_ [p1 [p2 [H3 H4]]]] | H2].
    - exists p2. split. by []. by apply: (trunck_seq_P H1 H4).
    - by [].
  Qed.
           
End Wip.
