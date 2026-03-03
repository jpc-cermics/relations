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
(* a node path is a sequence (seq T)                                          *)
(* an edge path is a sequence of pairs (seq T*T)                              *)
(*    p [\in] X    ==  all the elements of a node path p are in X               *)
(*    spt [\in] R  ==  all the elements of an edge path spt satisfy relation R  *)
(*    p [Suc\in] R ==  the successive elements of the node paths p satisfy      *)
(*                  relation R. Just for sanity check and replaced by         *)
(*                  p [L\in]  R in practice.                                    *)
(*    Lift st     == an edge path built from a node path                      *)
(*    p [L\in]  R  == same as (p [Suc\in] R) but using a Lift                     *)
(*    UnLift spt  == Left inverse of Lift (spt: seq (T*T))                    *)
(* Seq_utilities: some utilities for sequences                                *)
(* Lift_props: properties of the Lift mapping                                 *)
(* allset: utilities for st [\in] X, X: set T                                   *)
(* allset2: utilities for spt [\in] R, R: relation T                            *)
(* Lift_in: properties of [L\in]                                                *)
(* allset_Lifted: properties of st [L\in] R for st: seqT                        *) 
(*                with specified endpoints                                    *)
(* Suc_as_Lift: st [L\in] R <-> st [Suc\in] R                                     *)
(* Lift_bijective: Lift is a bijection between                                *)
(*                 D:= [set p:seq T | size(p) > 1] and Lift D                 *)
(* Endpoints_and_Deployment: endpoints and Deployments                        *)
(* seq_subsets: properties of p: seq T, p [\in] X and p [L\in] R]                 *)
(* seq_pairs_subsets: p: seq (T*T), p [\in] E and p [L\in] R]                     *)
(* PathRel: transitive closure and paths                                      *)
(* pair: sequences in  seq (T*T*O)                                            *)
(* pair_lift1: pair combined with Lift                                        *)
(* Seq_lifto: Lifto that is LiftO with constant orientation along the path    *)
(* Active_relation: D_U and active relation                                   *)
(* Active: The D_separated and Active relation as a relation on TxT           *)
(* PathRel_Examples: Utilities                                                *)
(******************************************************************************)

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
(* From mathcomp Require Import zify. *)
Set Warnings "parsing coercions".

From RL Require Import rel. 

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

(* begin snippet Lift:: no-out *)  
Fixpoint Lift (T: Type) (st: seq T): seq (T*T) := 
  match st with 
  | x :: [:: y & st] as st1 => (x,y)::(Lift st1)
  | _ => Nil (T*T)
  end.
(* end snippet Lift *)  

(* begin snippet Liftnota:: no-out *)
Notation "s [L\in] R" := (Lift s) [\in] R.
(* end snippet Liftnota *)

(* another equivalent definition *)
Definition Lift' (T: Type) (t:T) (st: seq T) := 
  (behead (pairmap pair t st)).

(** * s [Suc\in] R: consecutive elements of s satisfy relation R *)
(** * we later prove that: s [L\in] R <-> s [Suc\in] R *)
  
Inductive RPath (T: Type) (R: relation T): seq T -> Prop :=
| pp_void : RPath R [::]
| pp_two (t: T) (st: seq T) : 
  RPath R st ->
  st = [::] \/ (exists (t': T), exists (st': seq T), st = [::t' & st'] /\ R (t,t'))
  -> RPath R ([:: t & st]).
  
(* begin snippet RPath:: no-out *)  
Notation "s [Suc\in] R" := (RPath R s).
(* end snippet RPath *)  

(** Left inverse of Lift *)
Fixpoint UnLift (T: Type) (spt: seq (T*T)) (t: T):= 
  match spt with 
  | [::] => [::t]
  | [::(t1,t2) & spt1 ] => [::t1 & UnLift spt1 t2]
  end.
  
(* begin snippet allL:: no-out *)  
Definition allL (T: Type) (R:relation T) st x y := (x::(rcons st y)) [L\in] R.
(* end snippet allL *)    

Section Seq_utilities.
  (** * some utilities for sequences *)
  
  Context {T : Type}.
  Implicit Types (s p q: seq T) (n: nat).
  
  Lemma seq_rc s: (0 < size s) -> exists s' x, s = (rcons s' x).
  Proof. by elim:s => [//| x s _ _];exists (belast x s), (last x s);rewrite lastI. Qed.

  Lemma seq_c s: (0 < size s) -> exists s' x, s = x::s'.
  Proof. by elim:s  => [ // | x s _ _]; exists s, x. Qed.
  
  Lemma seq_rcrc s: 1 < size s -> exists s' x y, s = (rcons (rcons s' x) y).
  Proof.
    move => H1.
    have /seq_rc [q [x H2]]: 0 < size s by apply: (leq_ltn_trans _ H1).
    have /seq_rc [r [z H3]]: 0 < size q by rewrite H2 size_rcons ltnS in H1.
    by exists r,z,x;rewrite H2 H3.
  Qed.
  
  Lemma seq_crc s: 1 < size s -> exists s' x y, s = x::(rcons s' y).
  Proof.
    move => H1.
    have /seq_rc [r [y H3]]: 0 < size s by apply: leq_ltn_trans _ H1.
    have /seq_c [q [x H5]]: 0 < size r by rewrite H3 size_rcons ltnS in H1.
    by exists q,x,y;rewrite H3 H5.
  Qed.
  
  Lemma seq_cc s: 1 < size s -> exists s' x y, s = [::x,y &s'].
  Proof.
    move => H1.
    have /seq_c [r [y H3]]: 0 < size s by apply: leq_ltn_trans _ H1.
    have /seq_c [q [x H5]]: 0 < size r by rewrite H3 ltnS in H1.
    by exists q,y,x;rewrite H3 H5.
  Qed.
  
  Lemma seq_1 s: size s = 1 <-> exists (x:T), s = [::x].
  Proof.
    split; last by move => [x H1];rewrite H1.
    by elim:s => [// | x s _ /= /succn_inj/size0nil ->];exists x.
  Qed. 
  
  Lemma seq_rcrc0 s: size s = 2 <-> exists (x y:T), s = [::x;y].
  Proof.
    split => [/[dup] H1 | [x [y ->]] //]. 
    have /seq_rcrc [q [x [y ->]]]: 1 < size s by rewrite -H1.
    by rewrite !size_rcons => /succn_inj/succn_inj/size0nil -> /=;exists x, y.
  Qed.
  
  Lemma seq_n n s: size s = n.+1 -> exists s',exists x, s = [::x & s'] /\ size(s') = n.
  Proof.
    elim: n s => [[// | t s /=/succn_inj ? /= ] | n _ s H1];first by exists s, t. 
    have /seq_c [q [x H3]]: 0 < size(s)  by rewrite H1. 
    by move: H1;rewrite H3 /= => /succn_inj H1;exists q, x. 
  Qed.
  
  Lemma seq_rcn n s: size s = n.+1 -> exists s',exists x, s = rcons s' x /\ size(s') = n.
  Proof.
    elim: n s => [[// | t s /= /succn_inj/size0nil ->] | n Hn s H1];first by exists [::], t.
    have /seq_rc [s' [x H3]]: size(s) > 0  by rewrite H1. 
    by move: H1; rewrite H3 size_rcons => /succn_inj H1;(exists s', x).
  Qed.
  
  Lemma seq_cases s:
      s=[::] \/ (exists x, s=[::x]) \/ exists (s':seq T), exists (x y:T), s=x::(rcons s' y).
  Proof.
    elim:s  => [| x s _]; first by left.
    elim: s => [| y s _]; first by right;left;(exists x).
    have /seq_crc [q [x' [y' H2]]]: size([:: x, y & s]) > 1 by [].
    by right;right;exists q;exists x';exists y';rewrite H2.
  Qed.

  Lemma seq_cases1 s:
      s=[::] \/ (exists x, s=[::x]) \/ exists (s':seq T), exists (x y:T), s=[::x,y & s'].
  Proof.
    elim: s => [| x s _]; first by left.
    elim: s => [ | y s _]; first by right;left;(exists x).
    have /seq_cc [q [x' [y' H2]]]: size([:: x, y & s]) > 1 by [].
    by right;right;exists q;exists x';exists y';rewrite H2.
  Qed.

  Lemma last_rev s t: last t (rev s) = head t s.
  Proof. by elim: s t => [//| t1 st1 _ t];rewrite rev_cons last_rcons /=.  Qed.

  Lemma last_dv s x y i: i < size s -> last x s = last y s.
  Proof.
    elim/last_ind: s x y i => [// | s z Hr x y i].
    by rewrite size_rcons ltnS leq_eqVlt 2!last_rcons => /orP [/eqP ?|?].
  Qed.
  
  Lemma seq_split (x: T) (n:nat) s:
    n.+1 < size s 
    -> s = (rcons (take n s) (nth x s n)) ++ ((nth x s n.+1) :: (drop n.+2 s)).
  Proof.
    move => H1.
    have H2: n < size s by apply: leq_ltn_trans;last first;[apply: H1|].
    move: H2 H1 => /(@take_nth T x n s) H3 /(@drop_nth T x n.+1 s) H4.
    by rewrite -H3 -H4  cat_take_drop.
  Qed.
  
  Lemma head_rcons s t t': head t (rcons s t') = head t' s.
  Proof. by elim:s.  Qed.

  Lemma nth_dv s x y i: i < size s -> nth x s i = nth y s i.
  Proof.
    elim/last_ind: s x y i => [//| s z Hr x y i].
    rewrite size_rcons ltnS leq_eqVlt 2!nth_rcons => /orP [/eqP <- | H1].
    by rewrite eq_refl ltnn.
    by rewrite H1;apply: Hr.
  Qed.

End Seq_utilities.

Section allset.
  (** * utilities for st [\in] X, X: set T *)

  Context {T : Type}.
  Implicit Types (X Y: set T) (st: seq T) (x:T).
    
  Lemma allsetP X st x: X x /\ st [\in] X <-> (x \in X) && (st [\in] X).
  Proof. by split => [[/mem_set -> ->] // | /andP [/set_mem H1 H2]].  Qed.
  
  Lemma allset_consb X st x: ((x::st) [\in] X) <-> (x \in X) && st [\in] X.
  Proof. by split. Qed.
  
  Lemma allset_cons  X st x: ((x::st) [\in]  X) <-> X x /\ st [\in] X.
  Proof. by rewrite allset_consb allsetP. Qed.
  
  Lemma allset_subset X Y st: (X `<=` Y) -> (st [\in] X) -> (st [\in] Y).
  Proof.
    elim:st => [// | x' st' H1 H2 /andP [H3 H4]]. 
    by apply/andP;split;[apply/mem_set/H2/set_mem |apply: H1].
  Qed.
  
  Lemma allset_rcons X st x: (rcons st x) [\in] X <-> st [\in] X /\ X x.
  Proof. by rewrite all_rcons andC allsetP.  Qed. 
    
  Lemma allset_rev X st: st [\in] X <-> (rev st) [\in] X.
  Proof. by rewrite all_rev. Qed. 
  
  Lemma allset_cat X st st': (st++st') [\in] X <-> st [\in] X /\ st' [\in] X.
  Proof. by rewrite all_cat;split => [/andP | [-> ->]].  Qed.

  (** XXX faire les liens avec les predicats  all_predI all_predT *) 
  Lemma allset_I X Y st: st [\in] (X `&` Y) <-> st [\in] X && st [\in] Y. 
  Proof. 
    split => [H3 | ];first by apply/andP;split;apply: (allset_subset _ H3).
    elim: st => [// | x spa Hr /andP];rewrite !allset_cons => [[[? ?] [? ?]]].
    by split;[rewrite /setI /mkset | apply Hr;apply/andP].
  Qed.
  
End allset.

Section allset2.
  (** * extra utilities for spt [\in] R, R: relation T *)
  Context {T: Type}.
  Implicit Types (R: relation T) (X Y: set T) (spt: seq (T*T)) (x y:T).

  Lemma allset_inv R (spt: seq (T*T)): spt [\in] R <-> (map (fun tt => (tt.2,tt.1)) spt) [\in] R^-1. 
  Proof. by elim:spt  => [ // | [x y] spt Hr];rewrite map_cons !allset_cons Hr. Qed.

End allset2.

Section Lift_facts. 
  (** * properties of the Lift mapping *)

  Context {T : Type}.
  Implicit Types (T : Type) (st: seq T) (x y z: T) (spt: seq (T*T)).
  
  Lemma Lift_eq: forall (t:T) (st:seq T), Lift st = Lift' t st.
  Proof.
    move => t;elim => [// | t1 s _];elim: s t1 => [// | t2 s H1 t1 //]. 
    have -> : Lift [:: t1, t2 & s] = (t1,t2)::(Lift [::t2 & s]) by split.
    by rewrite H1.
  Qed.
  
  Lemma Lift_cc st x y:  Lift [::x,y & st] = [::(x,y) & Lift [::y & st]].
  Proof.  by split. Qed.

  Lemma Lift_crc st x y:
    Lift (x::(rcons st y)) = (x,(head y st))::(Lift (rcons st y)).
  Proof. by rewrite headI Lift_cc. Qed.
  
  Lemma Lift_rcrc st x y:
    Lift (rcons (rcons st x) y) =  rcons (Lift (rcons st x)) (x,y).
  Proof.
    elim:st => [// | z st Hr ].
    rewrite [in RHS]rcons_cons [in RHS]Lift_crc [in RHS]rcons_cons -[in RHS]Hr.
    by rewrite ![in LHS]rcons_cons [in LHS]Lift_crc head_rcons.
  Qed.
  
  Lemma Lift_rcc st x y: Lift (rcons (x::st) y) = rcons (Lift (x::st)) (last x st,y).
  Proof. by rewrite lastI Lift_rcrc. Qed.
  
  Lemma Lift_last st (pt: T*T) x y: last pt (Lift (x::(rcons st y))) = (last x st, y).
  Proof.
    elim/last_ind: st => [ // | st z _ ].
    by rewrite -2!rcons_cons Lift_rcrc 2!last_rcons.
  Qed.

  Lemma Lift_head st pt x y: head pt (Lift (x::(rcons st y))) = (x,head y st).
  Proof.
    by elim/last_ind: st => [// | st z _ ];rewrite Lift_crc head_rcons /=.
  Qed.
  
  Lemma head_Lift st pt: size(st) > 1 -> (head pt (Lift st)).1 = head pt.1 st.
  Proof.
    elim:st => [// | z st _];rewrite ltnS -/size => H1.
    by elim: st z H1 => [z // | u st _ z H2];rewrite Lift_cc /=.
  Qed.
  
  Lemma last_Lift st pt: size(st) > 1 -> (last pt (Lift st)).2 = last pt.1 st.
  Proof.
    elim/last_ind:st => [//| st z _ ];rewrite size_rcons ltnS => H1.
    by elim/last_ind: st z H1 => [z //|st u _ z H2];rewrite Lift_rcrc 2!last_rcons. 
  Qed.
  
  Lemma Lift_cat_rc: forall (st st':seq T) (y z: T),
      Lift ((rcons st y) ++ (rcons st' z)) =
        Lift (rcons st y) ++ Lift (y::rcons st' z).
  Proof.
    elim => [q y z // | t st Hr q y z].
    rewrite rcons_cons cat_cons -rcons_cat Lift_crc rcons_cat Hr. 
    have H2: head z (rcons st y ++ q) = head y st
      by elim/last_ind: q y z => [y z | q z' Hr' y z];
                                [rewrite cats0 head_rcons | rewrite -rcons_cat head_rcons Hr'].
    by rewrite H2 -cat_cons -Lift_crc.
  Qed.

  Lemma Lift_cat_rc': forall (st st':seq T) (y z: T),
      Lift ((rcons st y) ++ (rcons st' z)) =
        Lift (rcons st y) ++ Lift (y::rcons st' z).
  Proof.
    elim => [q y z // | t st Hr q y z].
    rewrite rcons_cons cat_cons -rcons_cat Lift_crc rcons_cat Hr. 
    have ->: head z (rcons st y ++ q) = head y st by rewrite headI cat_cons /=.
    by rewrite -cat_cons -Lift_crc.
  Qed.

  Lemma Lift_cat_crc: forall (st st':seq T) (x y z: T),
      Lift (x::(rcons st y) ++ (rcons st' z)) =
        Lift(x::(rcons st y)) ++ Lift (y::rcons st' z).
  Proof.
    elim => [q x y z // | t st Hr q x y z].
    by rewrite Lift_crc [in RHS]cat_cons -Lift_cat_rc.
  Qed.
  
  Lemma Lift_rev st: Lift (rev st) = map (fun tt =>(tt.2, tt.1)) (rev (Lift st)). 
  Proof.
    elim:st => [// | x st Hr ];elim: st x Hr => [// | x' st _ x H1].
    by rewrite rev_cons rev_cons Lift_rcrc -rev_cons H1 Lift_cc rev_cons map_rcons.
  Qed.
  
  Lemma UnLift_c spt x y z: UnLift ((x, y) :: spt) z = [::x & UnLift spt y].
  Proof. by []. Qed.

  Lemma UnLift_sz spt z: size (UnLift spt z) = size (spt) +1.
  Proof.
    by elim:spt z => [// z | [t t'] spt Hr z];rewrite UnLift_c /= Hr 2!addn1.
  Qed.

  Lemma Lift_inv1: forall (st : seq T) (x y z: T),
      UnLift (Lift (x::(rcons st y))) z = (x::(rcons st y)).
  Proof.
    by elim => [// | y st Hr x' x z]; rewrite Lift_cc UnLift_c Hr.
  Qed.

  Lemma UnLift_left x st: size (st) > 1 -> UnLift (Lift st) x = st.
  Proof. by move => /seq_crc [q [x' [y H2]]];rewrite H2;apply Lift_inv1. Qed.
  
  Lemma Lift_inv2 st x:  st <> [::] ->  UnLift (Lift st) (head x st) = st.
  Proof.
    pose proof seq_cases st as [-> | [[x' ->] | [r [x' [y ->]]]]];rewrite //. 
    by move => _; apply: Lift_inv1.
  Qed.
  
  Lemma Lift_inv_sz2 st: size(st) > 1 -> (forall (x:T), UnLift (Lift st) x = st).
  Proof.
    pose proof seq_cases st as [-> | [[x -> ] | [r [x [y ->]]]]];rewrite //.
    by move => _ x1; apply Lift_inv1.
  Qed.
  
  Lemma Lift_inv st x y z:  UnLift (Lift [::x,y & st]) z = [::x,y & st].
  Proof.  by apply Lift_inv_sz2. Qed.
  
  Lemma Lift_bc st x (y:T*T) spt : Lift (x :: st) = y :: spt -> x = y.1.
  Proof.
    move: y => [y1 y2].
    by pose proof seq_cases st as [H1 | [[x' H1] | [r [x' [y' H1]]]]];
    rewrite H1; [ | rewrite /= => [[?]] |rewrite Lift_cc => [[?] _ _]].
  Qed.
  
  Lemma Lift_sz st: size(st) > 1 -> size (Lift st) = (size st) -1.
  Proof.
    move => H1;pose proof seq_cc H1 as [q [x [y H2]]];rewrite H2;clear H2. 
    elim: q x y => [x y // | z q Hr x y].
    have H2: size ((x, y) :: Lift [:: y, z & q]) = 1+ size(Lift [:: y, z & q]) by [].
    by rewrite Hr in H2;rewrite Lift_cc H2 /= addnC [RHS]subn1 subn1 addn1 /=.
  Qed.

  Lemma Lift_sz' st: size(st) > 1 -> size (Lift st) = (size st) -1.
  Proof.
    move => /seq_cc [q [x [y ->]]];elim: q x y => [x y // | z q Hr x y].
    have H2: size ((x, y) :: Lift [:: y, z & q]) = 1+ size(Lift [:: y, z & q]) by [].
    by rewrite Hr in H2;rewrite Lift_cc H2 /= addnC [RHS]subn1 subn1 addn1 /=.
  Qed.

  Lemma Lift_sz2 st: size(Lift st) > 0 <-> size (st) > 1.
  Proof. by elim:st => [// | x st ]; elim: st x => [// | x st Hr y H1 // H2]. Qed.

End Lift_facts.

Section Lift_in_facts. 
  (** * properties of [L\in] *)

  Context {T: Type}.
  Implicit Types (R S: relation T) (X Y: set T) (st: seq T) (x y z:T).

  Lemma Lift_in_c R st x: (x::st) [L\in] R -> st [L\in] R.
  Proof. by elim: st x => [// | y st Hr x];rewrite Lift_cc allset_cons => -[_ ?] //. Qed.
  
  Lemma Lift_in_rc R st y: (rcons st y) [L\in] R -> st [L\in] R.
  Proof. by elim/last_ind: st y => [// | y st Hr x];rewrite Lift_rcrc allset_rcons => -[_ ?] //. Qed.

  Lemma Lift_in_head R st x y: 0 < size (st) -> (x::st) [L\in] R -> R (x, head y st).
  Proof. by move => /seq_c [s' [x' ->]];rewrite /head allset_cons => -[? _]. Qed.

  Lemma Lift_in_last R st x y: 0 < size (st) -> (rcons st y) [L\in] R -> R (last x st,y).
  Proof. by move => /seq_rc [s' [x' ->]];rewrite last_rcons Lift_rcrc allset_rcons => -[_ ?]. Qed.

  Lemma Lift_in_splitl R st x y: 0 < size (st) -> (x::st) [L\in] R -> R (x, head y st) /\ st [L\in] R. 
  Proof. by move => ? ?;split;[apply: Lift_in_head | apply: (@Lift_in_c R st x)]. Qed.

  Lemma Lift_in_splitr R st x y: 0 < size (st) -> (rcons st y) [L\in] R -> st [L\in] R /\ R (last x st,y).
  Proof. by move => ? ?;split;[apply: (@Lift_in_rc R st y) | apply: Lift_in_last]. Qed.
  
  Lemma Lift_in2nth R st z: st [L\in] R <-> (forall n, n.+1 < size st -> R ((nth z st n),(nth z st n.+1))). 
  Proof.
    split. 
    + elim: st => [// | x [//| x' st Hr /Lift_in_splitl H1 n /=]]. 
      have: 0 < size (x' :: st) by []; move => /(H1 z);rewrite /head => -[H2 /Hr/(_ n.-1) H3].
      case H4: (n== 0);first by move :H4 => /eqP -> _ /=.
      move: H4 => /neq0_lt0n /[dup] H4 /ltn_predK H5.
      move: H3; rewrite H5 => H6 H7.
      rewrite -{1}H5 -nth_behead /=.
      by have: n < size (x' :: st) by []; move => /H6 H8.
    + elim: st => [// | x st _ H1];elim: st x H1  => [ // | x' st' /(_ x') Hr x H1].
      rewrite Lift_cc allset_cons.
      split; first by move: H1 => /(_ 0) /= H1; apply: H1.
      apply: Hr => n. 
      by move: H1 => /(_ n.+1);rewrite -nth_behead /= => H1 /H1 H2.
  Qed.

  Lemma Lift_in_F R st y: (rcons st y) [L\in] R -> st [\in] (R.+)#_(y).
  Proof.
    elim: st y  => [// | x st Hr y];rewrite rcons_cons. 
    elim: st Hr => [_ | z st _ H1];first by rewrite /= => /andP [/inP /(@Fset_t1 _ R)/inP -> _].
    rewrite Lift_crc 2!allset_cons => [[? /H1 /[dup] ?]];rewrite allset_cons => -[? ?].
    by split;[apply Fset_t2; exists z|].
  Qed.
  
  Lemma Lift_in_FF R st y z:  (rcons st y) [L\in] R -> y \in R.+#_(z) -> st [\in] R.+#_(z).
  Proof. by move => /Lift_in_F H2 /(@Fset_t5 _ R) H4;apply: (@allset_subset _ _ _ _ H4 H2). Qed.
  
  Lemma Lift_in_rev R st: st [L\in] R <-> (rev st) [L\in] R^-1. 
  Proof. by rewrite allset_rev allset_inv Lift_rev. Qed.
  
  Lemma Lift_in_A R st x: (x::st) [L\in] R -> st [\in] (x)_:#R.+.
  Proof. by rewrite Lift_in_rev rev_cons => /Lift_in_F H1;rewrite allset_rev /Aset TclosIv.
  Qed.
  
  Lemma Lift_in_AA R st x y: (y::st) [L\in] R -> y \in (x)_:#R.+ -> st [\in] (x)_:#R.+.
  Proof.
    move => /[dup] H1 /Lift_in_A H2 H3. 
    have H4: (y)_:#R.+ `<=` (x)_:#R.+ by rewrite /Aset TclosIv;apply: Fset_t5;rewrite -TclosIv.
    by apply allset_subset with (y)_:#R.+.
  Qed.
  
  Lemma Lift_inI R S st: st [L\in] R /\ st [L\in] S <-> st [L\in] (R `&` S).
  Proof. by rewrite allset_I;split;move => /andP H1. Qed.
  
  (** * properties of  p: seq T, p [\in] X and p [L\in] R] *)

  Lemma all2lift st X: st [\in] X -> st [L\in] (X `*` X). 
  Proof.
    elim: st => [// | x'];elim => [// | x st _ H1 /allset_cons [? /[dup] /allset_cons [? _] /H1 ?]]. 
    by rewrite Lift_cc allset_cons.
  Qed.

  Lemma lift2all st X x x': [::x, x' & st] [L\in] (X `*` X) -> [::x, x' & st] [\in] X.
  Proof.
    elim: st x x' => [x x' // | x st Hr y y'].
    by rewrite Lift_cc allset_cons => -[/= [/inP -> /inP ->] _].
    by rewrite Lift_cc allset_cons => -[[H1 _] /Hr H2];rewrite allset_cons.
  Qed.

  (* begin snippet RpathLone:: no-out *)  
  Lemma Rpath_L1 st X: st [\in] X -> st [L\in] (X `*` X). 
  (* end snippet RpathLone *)  
  Proof. by apply: all2lift. Qed.
  
  Lemma Rpath_L2 st X: size(st) > 1 /\ st [L\in] (X `*` X) -> st [\in] X.
  Proof. by move => [/seq_cc [st' [x [y ->]]] +];apply: lift2all. Qed.
  
  Lemma Rpath_L3 st X R: st [\in] X /\ st [L\in] R -> st [L\in] ((X `*` X)`&`R) . 
  Proof. by move => [/Rpath_L1 H1 H2];apply allset_I; rewrite H1 H2. Qed.

  Lemma Rpath_L4 st X R: size(st) > 1 /\ st [L\in] ((X `*` X)`&`R) -> st [\in] X /\ st [L\in] R.
  Proof. by rewrite allset_I;move => [H1 /andP [H2 H3]];split;[apply: Rpath_L2|]. Qed.
  
  Lemma Rpath_iff1 X R: 
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
  
  Lemma Rpath_iff2 X R: 
    [set st | st [\in] X /\ st [L\in] R] 
    = [set st | st = [::]] `|` [set st | size(st) > 0 /\ st [\in] X /\ st [L\in] R].
  Proof.
    rewrite /setU /mkset predeqE => [st].
    split.
    by elim: st => [[? _] // | t st _ ];[left | right].
    elim: st => [[_ /= // | [? _] //] | t st _ [? // | [_ [? ?]] //]].
  Qed.

  Lemma Rpath_iff X R:
    [set st | st [\in] X /\ st [L\in] R]
    =   [set st | st = [::]] 
          `|` [set st | size(st) = 1 /\ (st [\in] X) ] 
          `|` [set st | size(st) > 1 /\ st [L\in] ((X `*` X)`&`R)]. 
  Proof. by rewrite -[RHS]setUA -[in RHS]Rpath_iff1 -[in RHS]Rpath_iff2. Qed.

End Lift_in_facts. 

Section allset_Lifted.
  (** * properties of st [L\in] R for st: seq T  *)
  (** * with specified endpoints *)

  Context {T: Type}.
  Implicit Types (R: relation T) (X Y: set T) (st: seq T) (x y z:T).
  
  Lemma allL0 R x y:  allL R [::] x y = ((x,y) \in R).
  Proof. by rewrite /allL Lift_cc /andP /= andbT. Qed.

  Lemma allL0' R x y:  allL R [::] x y <-> R (x,y).
  Proof. by rewrite allL0;split=> [/set_mem H1 // | /inP H1]. Qed.
  
  Lemma allL_c R st x y z: allL R (z::st) x y <-> ((x, z) \in R) && allL R st z y.
  Proof. by split;[rewrite /allL rcons_cons Lift_cc allset_cons |]. Qed.

  Lemma allL_rc R st x y z: allL R (rcons st z) x y <-> ((z,y) \in R) && allL R st x z.
  Proof.
    split.
    by rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons;move => [-> /inP ->].
    by move => /andP [/inP ? ?];rewrite /allL -rcons_cons Lift_rcc allset_rcons last_rcons. 
  Qed.

  Lemma allset_Rr X x y st: (Lift (x::(rcons st y))) [\in] R_(X) <-> (rcons st y) [\in] X.
  Proof.
    elim: st x => [| z st Hr x];last first.
    by rewrite rcons_cons Lift_cc 2!allset_cons;split => [[? /Hr ?] // | [H1 /Hr H2]].
    rewrite /= /Rr;split => [/andP [/inP/=/mem_set -> _ //] | /andP [/inP H1 _]].
    by rewrite andbT;apply/inP. 
  Qed.

  Lemma allset_Lr X x y st: (Lift (x::(rcons st y))) [\in] L_(X) <-> (x::st) [\in] X.
  Proof.
    elim: st x => [| z st Hr x];last first.
    by rewrite rcons_cons Lift_cc 2!allset_cons;split => [[? /Hr ?] //|[? /Hr ?]].
    rewrite /= /Lr; split => [/andP [/inP/=/mem_set -> _ //] | /andP [/inP H1 _]].
    by rewrite andbT;apply/inP. 
  Qed.
  
  Lemma allset_Dl X R x y st: (Lift (x::(rcons st y))) [\in] (Δ_(X)`;`R) -> (x::st) [\in] X.
  Proof. by rewrite DeltaLco allset_I => /andP [/allset_Lr H1 _]. Qed.
  
  Lemma allset_Dr X R x y st: (Lift (x::(rcons st y))) [\in] (R`;`Δ_(X)) -> (rcons st y) [\in] X.
  Proof. by rewrite DeltaRco allset_I => /andP [_ /allset_Rr H1]. Qed.
  
  Lemma allL_splitl R st x y:  allL R st x y <-> (x::st) [L\in] R /\ R ((last x st), y).
  Proof. 
    split;first by rewrite /allL -rcons_cons => H1;apply: (@Lift_in_splitr _ R (x::st) x y). 
    elim/last_ind: st x y => [x y [_ ?] // | st x' Hr x y [H1 +]];first  by rewrite allL0'.
    by rewrite /allL -rcons_cons Lift_rcc last_rcons allset_rcons.
  Qed.
  
  Lemma allL_splitr R st x y:  allL R st x y <-> R (x, head y st) /\ (rcons st y) [L\in] R. 
  Proof. 
    split;first by move: (@Lift_in_splitl _ R (rcons st y) x y);rewrite head_rcons size_rcons => H2;apply: H2.
    elim: st x y => [x y [? _] // | x' st Hr x y [ H1 H2]];first by rewrite allL0'.
    by rewrite /allL  Lift_crc allset_cons.
  Qed.
  
  Lemma allL_split R st x y: allL R st x y <-> R (x, head y st) /\ st [L\in] R /\ R ((last x st), y).
  Proof.
    split;first by move => /[dup] /allL_splitr [? _] /allL_splitl [/(@Lift_in_c T R) ? ?].
    move => [H1 [H2 H3]];rewrite allL_splitl;split; last by [].
    elim/last_ind: st x y H1 H2 H3 => [// | s y _ x' y']. 
    by rewrite head_rcons last_rcons allL_splitr => ? ? _.
  Qed.
  
  Lemma allL_nth R st x y z: 
    allL R st x y 
    <-> R (x, nth y st 0)
      /\ (forall n, n.+1 < size st -> R ((nth z st n),(nth z st n.+1)))
      /\ R (nth x st (size st).-1, y).
  Proof. by rewrite allL_split (@Lift_in2nth T R st z) nth0 -nth_last. Qed.

  Lemma allL_cat R st st' x y z: 
    allL R ((rcons st y) ++ st') x z <-> allL R st x y && allL R st' y z.
  Proof.
    rewrite /allL cat_rcons rcons_cat rcons_cons -cat_rcons Lift_cat_crc allset_cat.
    by split => [ [? ?] | /andP [? ?]];[apply/andP |].
  Qed.
  
  Lemma allL_subset S R st x y: (S `<=` R) -> allL S st x y -> allL R st x y.
  Proof. by move => ? ? ;apply allset_subset with S. Qed.
  
  Lemma allL_WS_iff R X st x y: allL (Δ_(X) `;` R) st x y <-> (x::st) [\in] X && allL R st x y.
  Proof.
    have H1: (L_(X) `&` R) `<=` R by apply: subIsetr.
    have H2: (L_(X) `&` R) `<=` L_(X) by apply: subIsetl.
    pose proof (@allset_subset (T*T) (L_(X) `&` R) L_(X)) as H3.
    pose proof (@allset_subset (T*T) (L_(X) `&` R) R) as H4.    
    rewrite DeltaLco /allL allset_I.
    by split => /andP [/allset_Lr H5 H6];[apply /andP | apply /andP].
  Qed.
  
  Lemma allL_SW_iff R X st x y: allL (R `;` Δ_(X)) st x y <-> (rcons st y) [\in] X && allL R st x y.
  Proof.
    have H1: (R `&` L_(X)) `<=` R by apply: subIsetl.
    have H2: (R `&` L_(X)) `<=` L_(X) by apply: subIsetr.
    pose proof (@allset_subset (T*T) (L_(X) `&` R) L_(X)) as H3.
    pose proof (@allset_subset (T*T) (L_(X) `&` R) R) as H4.    
    rewrite DeltaRco /allL allset_I; split => /andP [H5 H6]. 
    by rewrite allset_Rr in H6; apply /andP; split. 
    by apply /andP; split;[| rewrite allset_Rr].
  Qed.
  
  Lemma allL_rev R st x y: allL R st x y <->  allL R^-1 (rev st) y x.
  Proof. by rewrite Lift_in_rev rev_cons rev_rcons. Qed.
  
  Lemma allL_All R st x y: allL R st x y -> (x::st) [\in] (R.+)#_(y).
  Proof. by rewrite /allL -rcons_cons; apply: Lift_in_F.  Qed.

  Lemma allL_AllA R st x y: allL R st x y -> (rcons st y) [\in] (x)_:#(R.+).
  Proof. by rewrite allL_rev => /allL_All;rewrite /Aset TclosIv -all_rev rev_cons revK. Qed.

  Lemma allL_Lift_in_rc R st x y: allL R st x y -> (rcons st y) [L\in] R.
  Proof. by elim:st x y => [x y // | x' st _ x y];rewrite allL_c rcons_cons => /andP [_ ?]. Qed.

  Lemma allL_Lift_in_c R st x y: allL R st x y -> (x:: st) [L\in] R.
  Proof. by elim/last_ind: st x y => [x y // | st x' Hr x y];rewrite allL_rc => /andP [_ H1]. Qed.

  Lemma allL_lastR R s x y z i: i < size s -> allL R s x y -> R (last z s, y).
  Proof.
    move => H1;rewrite allL_splitl => -[_ H2].
    by have <- : last x s = last z s by apply: last_dv;apply:H1. 
  Qed.
  
  Lemma nth_L0' st x y z: nth z (x::(rcons st y)) 1 = nth y st 0.
  Proof. 
    case H1: (size st == 0);first by move: H1 => /eqP/size0nil -> /=.
    by move: H1 => /neq0_lt0n H1;rewrite /= nth_rcons H1;apply: nth_dv.
  Qed.
  
  Lemma nth_L0'' R st x y z: 
    R (nth z (x::(rcons st y)) 0, nth z (x::(rcons st y)) 1) = R(x,nth y st 0).
  Proof. by rewrite nth_L0'.  Qed.
  
  Lemma nth_L1 st x y z: 
    nth z (x :: rcons st y) (size st) = nth x st (size st).-1.
  Proof.
    case H1: ((size st) == 0);first by move: H1 => /eqP/size0nil -> /=.
    move: H1 => /neq0_lt0n /[dup] H1 /ltn_predK H2.
    have H3: (size st).-1 < size st by rewrite H2. 
    rewrite -H2 /= nth_rcons H3.
    by have ->: (nth z st (size st).-1) = (nth x st (size st).-1) by apply: nth_dv.
  Qed.
  
  Lemma nth_L1' st x y z: nth z (x :: rcons st y) (size st).+1 = y.
  Proof. by rewrite /= nth_rcons ltnn eq_refl. Qed.
    
  Lemma nth_L1'' R st x y z: 
    R (nth z (x::(rcons st y)) (size st), nth z (x::(rcons st y)) (size st).+1) 
          = R(nth x st (size st).-1 , y ).
  Proof. by rewrite nth_L1 nth_L1'. Qed.
  
  Lemma nth_L2 st x y z (n: nat): 
    0 < n < size st -> nth z (x :: rcons st y) n = nth z st n.-1.
  Proof.
    move => /andP [H1 H1'].
    have H2: n.-1.+1 = n by apply: (@ltn_predK 0 n H1). 
    rewrite -1!H2 /= nth_rcons. 
    by have ->: n.-1 < size st by apply: ltn_trans _ H1';rewrite ltn_predL.
  Qed.
  
  Lemma nth_L2' st x y z (n: nat): 
    0 < n < size st -> nth z (x :: rcons st y) n.+1 = nth z st n.
  Proof.
    move => /andP [H1 H1'].
    have H2: n.-1.+1 = n by apply: (@ltn_predK 0 n H1).
    by rewrite -1!H2 /= nth_rcons H2 H1'. 
  Qed.
  
  Lemma nth_L3 st y z : nth y st 0 = (nth z (rcons st y) 0).
  Proof. by rewrite -(@nth_L0' st y y z) /=. Qed.
  
  Lemma nth_L6 n st y z:
    n < (size st) -> nth z (rcons st y) n = nth y st n.
  Proof. move => H0;rewrite nth_rcons H0;by apply: nth_dv. Qed.

  Lemma nth_L7 n st y z:
    n = (size st) ->  nth z (rcons st y) n = y.
  Proof. by move => ->;rewrite nth_rcons ltnn eq_refl /=. Qed.
  
  Lemma allL_nth' R st x y z:
    allL R st x y 
    <-> (forall n, n <= size st -> R ((nth z (x::(rcons st y)) n), (nth z (x::(rcons st y)) n.+1))).
  Proof. 
    rewrite (allL_nth R st x y z).
    split. 
    + move => [H4 [H5 H6]] n H7.
      case H8: (n == 0);first by move: H8 => /eqP ->; rewrite nth_L0''. 
      case H9: (n == (size st));first by move: H9 => /eqP ->;rewrite nth_L1''.
      have H10: 0 < n < size st
        by move: H8 H7 => /neq0_lt0n ->;rewrite leq_eqVlt H9 orFb => ->.
      move: (H10) => /[dup] /(@nth_L2 st x y z n) -> /(@nth_L2' st x y z n) ->.
      move: H10 => /andP [H10 H10'].
      have H11: n.-1.+1 = n by apply: (@ltn_predK 0 _). 
      move: H5 => /(_ n.-1);rewrite H11 => H5.
      by apply: H5.
    + move => H1.
      split. 
      by move: H1 => /(_ 0) /= H1;rewrite (nth_L3 st y z);apply: H1.
      split.
      ++ move: H1 => + n H2 => /(_ n.+1) H1.
         have H3: n < size st by apply/(ltn_trans _ H2)/ltnSn. 
         move: (H3) => /[dup] /(@nth_L6 n st y z) + /H1 /= => ->. 
         move: (H2) => /(@nth_L6 n.+1 st y z) ->.
         have ->: nth y st n = nth z st n by apply: nth_dv. 
         have ->: nth y st n.+1 = nth z st n.+1 by apply: nth_dv. 
         exact.
      ++ move: H1 => /(_ (size st)) H1.
         (have: size st <= size st by apply: leqnn) => {}/H1 /=.
         rewrite nth_L7;last by exact. 
         case H1: (size st == 0);first by move: H1 => /eqP /size0nil -> /=.
         move: H1 => /neq0_lt0n H1.
         have H3: (size st).-1.+1 = size st by apply: (@ltn_predK 0 _). 
         have H4: (size st).-1 < size st by rewrite ltn_predL.
         rewrite -1!H3 /= nth_rcons H4.
         have ->: nth z st (size st).-1 = nth x st (size st).-1 by apply: nth_dv.
         exact.
  Qed.
  
End allset_Lifted.

Section Suc_as_Lift. 
  (** * st [L\in] R <-> st [Suc\in] R *)
  (* st [Suc\in] R is more natural to define a path and st [L\in] R is more computational 
   * for sanity check we prove that the two are equivalent
   *)
  Context {T: Type}.
  Implicit Types (T : Type) (R: relation T) (X Y: set T) (st: seq T) (x y z:T).
  
  (* begin snippet RPathequiv:: no-out *)  
  Lemma RPath_equiv st R: st [L\in] R <-> st [Suc\in] R.
  (* end snippet RPathequiv *)  
  Proof.
    (* we use seq_cases to explore the three cases *)
    pose proof seq_cases st as [H1 | [[x H1] | [q [x [y H1]]]]];rewrite H1.
    by split => H;[apply pp_void | ].
    by split => H;[apply pp_two;[apply pp_void | left] | ].
    clear H1.
    split.
    - elim: q x y => [ //= x y /andP [/inP H2 _] | z q Hr x y ].
      by apply pp_two;[ apply pp_two;[constructor | left] | right; exists y, [::]].
      rewrite rcons_cons Lift_cc allset_cons andC;
        by move => [H1 H2];apply pp_two;[ apply Hr | right; exists z, (rcons q y)].
    - move => H.
      elim/RPath_ind: H => [// | x' y' ep H1 [-> // | [y1 [ep1 [H2 H3]]]]].
      by rewrite H2 in H1 *; rewrite Lift_cc allset_cons //.
  Qed.

End Suc_as_Lift. 

Section Lift_bijective.
  (** * Lift is a bijection between D:= [set p:seq T | size(p) > 1] and Lift D *)

  Context {T: Type}.
  Implicit Types (T : Type) (R: relation T) (X Y: set T) (st: seq T) (x y z:T) (spt: seq (T*T)).
  
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
    by rewrite 3!Lift_cc allset_cons -Lift_cc;split;[ |apply Hr].
  Qed.

  (* begin snippet DI:: no-out *)  
  Definition Lift_Dom {T: Type}:= [set st:seq T| size(st) > 1].
  Definition Lift_Im  {T: Type}:= [set spt:seq (T*T)| size(spt) > 0 
                                                      /\ spt [L\in] Chrel].
  (* end snippet DI *)
  
  Lemma Lift_image st: st \in Lift_Dom -> (Lift st) \in Lift_Im.
  Proof.
    rewrite /Lift_Dom /Lift_Im /mkset => /inP H1;rewrite inP Lift_sz2.
    by split;[ | apply Lift_Lift].
  Qed.
  
  Lemma UnLift_image (spt: seq (T*T)): 
    spt \in Lift_Im -> (forall (z:T), (UnLift spt z) \in Lift_Dom).
  Proof.
    move => /inP [H1 _] z; apply inP.
    rewrite /Lift_Dom /mkset.
    elim: spt H1 => [// | [x y] spt _ /= _].
    elim: spt y => [ // | [x' y'] st' _ z'].
    by rewrite UnLift_c /=. 
  Qed.
  
  Lemma Lift_UnLift spt: spt \in Lift_Im -> (forall (z:T), Lift (UnLift spt z) = spt).
  Proof.
    move => /inP [H1 H2] z; apply inP.
    elim: spt H1 H2 => [// | [x y] st Hr H1 H2].
    rewrite UnLift_c.
    elim: st y x Hr H1 H2 => [y x _ _ _ /= // | [x' y'] st Hr y x H1 H2 H3].
    by apply inP.
    rewrite UnLift_c in H1.
    rewrite UnLift_c Lift_cc.
    move: (H3). rewrite Lift_cc allset_cons => [[H4 H5]].
    move: H4. rewrite /Chrel /mkset => [H4].
    have H6:  (Lift (x' :: UnLift st y'))= ((x', y') :: st)
      by apply inP; apply H1. 
    apply inP. rewrite H6.
    by have -> : y=x' by [].
  Qed.
  
  (* begin snippet Liftinj:: no-out *) 
  Lemma Lift_inj st st': st \in Lift_Dom -> Lift st = Lift st' -> st = st'.
  (* end snippet Liftinj *) 
  Proof.
    rewrite /Lift_Dom /mkset.
    move => /inP H1 H2.
    move: (H1) => /Lift_sz2 H3. 
    have H4: size(st') > 1  by rewrite -Lift_sz2 -H2. 
    pose proof seq_crc H1 as [r [x [y H5]]].
    pose proof Lift_inv_sz2 H1 as H6.
    pose proof Lift_inv_sz2 H4 as H7.
    by rewrite -(H6 x) -(H7 x) H2. 
  Qed.
  
  Lemma Lift_inj' st st': st \in Lift_Dom -> st' \in Lift_Dom -> Lift st = Lift st' -> st = st'.
  Proof.
    move => /inP H1 /inP H2 H3.
    pose proof seq_crc H1 as [_ [x _]].
    have H4: UnLift (Lift st) x = UnLift (Lift st') x by rewrite H3.
    pose proof (UnLift_left x H1) as H5.
    pose proof (UnLift_left x H2) as H6.
    by rewrite -H5 -H6 H4.
  Qed.
  
  (* begin snippet Liftsurj:: no-out *) 
  Lemma Lift_surj spt: spt \in Lift_Im -> exists st, st\in Lift_Dom /\ Lift st=spt. 
  (* end snippet Liftsurj *) 
  Proof.
    move => H0; move: (H0);rewrite /Lift_Im /mkset => /inP [H1 H2].
    pose proof (seq_c H1) as [_ [[x _] _]].
    pose proof Lift_UnLift H0 x as H3.
    pose proof UnLift_image H0 x as H4.
    by exists (UnLift spt x). 
  Qed.
  
  (* a surjectivy result on a larger set *)
  Lemma Lift_Chrel spt: (Lift spt) [\in] Chrel <-> exists st: seq T, Lift st = spt.
  Proof.
    elim:spt => [ | [x y] spt _ ];first by split => ?;[(exists [::]) |].
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

Section PathRel.
  (** * transitive closure and paths
   * the main result here is that the relation in TxT obtained 
   * by fun (x y : T) => (exists (p: seq T), AllL E p x y)
   * is the relation E.+ the transitive closure of E 
   *)

  Variables (T: Type).
  
  (* relation based on paths: take care that the path p depends on (x,y) *)
  Definition PathRel_n (R: relation T) (n:nat) :=
    [set x | (exists (p: seq T), size(p)=n /\ allL R p x.1 x.2)].

  (* composition and existence of paths coincide *)
  Lemma Itern_iff_PathReln  (R: relation T) : forall (n:nat), R^(n.+1) =  PathRel_n R n.
  Proof.
    elim => [ | n' H].
    - rewrite /iter /PathRel_n DeltaCl /mkset predeqE => [[x y]].
      split => [ H | ].
      by (exists [::]); rewrite allL0' /=.
      by move => [p [/size0nil -> /allL0' H2]].
    - rewrite -add1n iter_compose H /iter DeltaCl /mkset predeqE => [[x y]].
      split => [[z [/= /inP H1 [p [H2 /= H3]]]] |[p [H1 H2]]];
                first by (exists (z::p));rewrite -H2 allL_c H3 andbT H1. 
      elim: p H1 H2 => [ // | z p' _ H1].
      move: H1;rewrite /size -/size -/addn1 => /succn_inj H1.
      rewrite allL_c /= => [/andP [/inP H2 H3]].
      by exists z;split;[ | exists p'].
  Qed.
  
  (* R.+ =  PathRel R *)
  (* begin snippet TCP:: no-out *)  
  Lemma TCP (R: relation T) : R.+ = [set vp | exists p, allL R p vp.1 vp.2 ].
  (* end snippet TCP *)  
  Proof.
    rewrite predeqE => -[x y];split => [/(@Tclos_iterk T) [n] | [p H1]].
    by rewrite  Itern_iff_PathReln /PathRel_n => -[p [H1 H2]];(exists p).
    have: PathRel_n R (size p) (x, y) by (exists p).
    by rewrite -Itern_iff_PathReln;apply: iterk_sub_Tclos.
  Qed.
  
  Lemma allL_to_Tclos  (R: relation T) : forall (st: seq T) x y, allL R st x y -> R.+ (x,y).
  Proof. by move => st x y; rewrite TCP; exists st. Qed.
  
  Lemma TCP'' (R: relation T) (X: set T): 
    (Δ_(X) `;` R).+ = [set vp | exists p, (vp.1::p) [\in] X /\ allL R p vp.1 vp.2 ].
  Proof.
    rewrite {1}TCP predeqE => -[x y].
    split; first by move => [p /allL_WS_iff /andP [H1 H2]];(exists p).
    by move => [p /andP/allL_WS_iff ?];(exists p).
  Qed.

  Lemma Tclos_to_paths_l R (X: set T) st x y:
    allL (Δ_(X) `;` R) st x y <-> (x::st) [\in] X /\ allL R st x y /\ (x :: st) [\in] (Δ_(X) `;` R).+#_(y).
  Proof.
    split;last by rewrite allL_WS_iff => -[-> [-> _]].
    by move => /[dup] /allL_WS_iff/andP [? ?] /(@allL_All _ (Δ_(X) `;` R) st x y) ?. 
  Qed.
  
  Lemma Tclos_to_paths_l' R (X: set T) st x y:
      allL (Δ_(X) `;` R) st x y <-> (x::st) [\in] X /\ allL R st x y /\ (x :: st) [\in] R.+#_(y).
  Proof.
    split;last by rewrite allL_WS_iff => -[-> [-> _]].
    by move => /allL_WS_iff/andP [? +] => /[dup] ? /(@allL_All _ R st x y) ?. 
  Qed.

  Lemma Tclos_to_paths_r R (X: set T) st x y:
    allL (R `;` Δ_(X)) st x y <-> (rcons st y) [\in] X /\ allL R st x y /\ ((rcons st y) [\in] x _:#(R `;` Δ_(X)).+). 
  Proof.
    split;last by rewrite allL_SW_iff => -[-> [-> _]].
    by move => /[dup] /allL_SW_iff/andP [? ?] /(@allL_AllA _ (R `;` Δ_(X)) st x y) ?. 
  Qed.
  
  Lemma Tclos_to_paths_r' R (X: set T) st x y:
    allL (R `;` Δ_(X)) st x y <-> (rcons st y) [\in] X /\ allL R st x y /\ ((rcons st y) [\in] x _:#R.+). 
  Proof.
    split; first by move => /allL_SW_iff/andP [? +] => /[dup] ? /(@allL_AllA _ R st x y) ?. 
    by rewrite allL_SW_iff => -[-> [-> _]].
  Qed.
  
End PathRel.
