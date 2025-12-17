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

  (* XXXX headI permet de passer d'un rcons a un cons *)

  Context {T : Type}.
  Implicit Types (T : Type) (s: seq T).
  
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
    split => [H1 |[x [y H1]]];last by rewrite H1.
    have /seq_rcrc [q [x [y H3]]]: 1 < size s by rewrite -H1.
    move: H1;rewrite H3 size_rcons size_rcons => /eqP H1.
    have /nilP H4: size q == 0 by [].
    by exists x,y;rewrite H4.
  Qed.

  Lemma seq_n n s: size s = n.+1 -> exists s',exists x, s = [::x & s'] /\ size(s') = n.
  Proof.
    elim: n s => [| n Hn s H1].
    by elim => [_ // | t s H1 /= /succn_inj/size0nil ->];exists [::], t.
    have /seq_c [q [x H3]]: size(s) > 0  by rewrite H1. 
    by move: H1;rewrite H3 /= => /succn_inj H1;exists q, x. 
  Qed.
  
  Lemma seq_rcn n s: size s = n.+1 -> exists s',exists x, s = rcons s' x /\ size(s') = n.
  Proof.
    elim: n s => [| n Hn s H1].
    by elim => [_ // | t s _ /= /succn_inj/size0nil ->]; exists [::], t.
    have /seq_rc [s' [x H3]]: size(s) > 0  by rewrite H1. 
    by move: H1; rewrite H3 size_rcons => /succn_inj H1;(exists s', x).
  Qed.
  
  Lemma seq_cases s:
      s=[::] \/ (exists x, s=[::x]) \/ exists (s':seq T), exists (x y:T), s=x::(rcons s' y).
  Proof.
    elim:s  => [| x s _]; first by left.
    elim: s => [ | y s _]; first by right;left;(exists x).
    right;right.
    have /seq_crc [q [x' [y' H2]]]: size([:: x, y & s]) > 1 by [].
    by exists q;exists x';exists y';rewrite H2.
  Qed.

  Lemma seq_cases1 s:
      s=[::] \/ (exists x, s=[::x]) \/ exists (s':seq T), exists (x y:T), s=[::x,y & s'].
  Proof.
    elim: s => [| x s _]; first by left.
    elim: s => [ | y s _]; first by right;left;(exists x).
    right;right.
    have /seq_cc [q [x' [y' H2]]]: size([:: x, y & s]) > 1 by [].
    by exists q;exists x';exists y';rewrite H2.
  Qed.

  Lemma last_rev s t: last t (rev s) = head t s.
  Proof. by elim: s t => [//| t1 st1 _ t];rewrite rev_cons last_rcons /=.  Qed.

End Seq_utilities.

Section allset.
  (** * utilities for st [\in] X, X: set T *)

  Context {T : Type}.
  Implicit Types (T : Type) (X Y: set T) (st: seq T) (x:T).
    
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
    
  Lemma allset_rev X st: st [\in] X <->  (rev st) [\in] X.
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
  Implicit Types (T : Type) (R: relation T) (X Y: set T) (spt: seq (T*T)) (x y:T).

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
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    elim:st => [// | z st Hr ].
    rewrite [in RHS]rcons_cons [in RHS]Lift_crc [in RHS]rcons_cons -[in RHS]Hr.
    by rewrite ![in LHS]rcons_cons [in LHS]Lift_crc H1. 
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
    have H1: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim. 
    by elim/last_ind: st => [// | st z _ ];rewrite Lift_crc H1 /=.
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
    by move => _; apply Lift_inv1.
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

  Lemma Lift_sz2 st: size(Lift st) > 0 <-> size (st) > 1.
  Proof. by elim:st => [// | x st ]; elim: st x => [// | x st Hr y H1 // H2]. Qed.

End Lift_facts.

Section Lift_in_facts. 
  (** * properties of [L\in] *)

  Context {T: Type}.
  Implicit Types (T : Type) (R S: relation T) (X Y: set T) (st: seq T) (x y z:T).

  Lemma Lift_in_c R st x: (x::st) [L\in] R -> st [L\in] R.
  Proof. by elim: st x => [// | y st Hr x];rewrite Lift_cc allset_cons => -[_ ?] //. Qed.
  
  Lemma Lift_in_rc R st y: (rcons st y) [L\in] R -> st [L\in] R.
  Proof. by elim/last_ind: st y => [// | y st Hr x];rewrite Lift_rcrc allset_rcons => -[_ ?] //. Qed.

  Lemma Lift_in_head R st x y: 0 < size (st) -> (x::st) [L\in] R -> R (x, head y st).
  Proof.  by move => /seq_c [s' [x' ->]];rewrite /head allset_cons => -[? _]. Qed.

  Lemma Lift_in_last R st x y: 0 < size (st) -> (rcons st y) [L\in] R -> R (last x st,y).
  Proof.  by move => /seq_rc [s' [x' ->]];rewrite last_rcons Lift_rcrc allset_rcons => -[_ ?]. Qed.

  Lemma Lift_in_splitl R st x y: 0 < size (st) -> (x::st) [L\in] R -> R (x, head y st) /\ st [L\in] R. 
  Proof.  by move => ? ?;split;[apply: Lift_in_head | apply: (@Lift_in_c R st x)]. Qed.

  Lemma Lift_in_splitr R st x y: 0 < size (st) -> (rcons st y) [L\in] R -> st [L\in] R /\ R (last x st,y).
  Proof.  by move => ? ?;split;[apply: (@Lift_in_rc R st y) | apply: Lift_in_last]. Qed.
  
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
  Implicit Types (T : Type) (R: relation T) (X Y: set T) (st: seq T) (x y z:T).
  
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
    have H0: forall (q: seq T) (x' y': T), head y' (rcons q x') = head x' q by elim.
    split;first by move: (@Lift_in_splitl _ R (rcons st y) x y);rewrite H0 size_rcons => H2;apply: H2.
    elim: st x y => [x y [? _] // | x' st Hr x y [ H1 H2]];first by rewrite allL0'.
    by rewrite /allL  Lift_crc allset_cons.
  Qed.
  
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
  (* begin snippet TCP':: no-out *)  
  (* Lemma TCP' (R: relation T) : R.+ = [set vp | exists p, (Lift (vp.1::(rcons p vp.2))) [\in] R]. *)
  Lemma TCP' (R: relation T) : R.+ = [set vp | exists p, allL R p vp.1 vp.2 ].
  (* end snippet TCP' *)  
  Proof.
    rewrite predeqE => -[x y];split => [/(@clos_t_iterk T) [n] | [p H1]].
    by rewrite  Itern_iff_PathReln /PathRel_n => -[p [H1 H2]];(exists p).
    have: PathRel_n R (size p) (x, y) by (exists p).
    by rewrite -Itern_iff_PathReln;apply: iterk_inc_clos_trans.
  Qed.
  
  Lemma allL_to_clos_t  (R: relation T) : forall (st: seq T) x y, allL R st x y -> R.+ (x,y).
  Proof. by move => st x y; rewrite TCP'; exists st. Qed.
  
  Lemma TCP'' (R: relation T) (X: set T): 
    (Δ_(X) `;` R).+ = [set vp | exists p, (vp.1::p) [\in] X /\ allL R p vp.1 vp.2 ].
  Proof.
    rewrite {1}TCP' predeqE => -[x y].
    split; first by move => [p /allL_WS_iff /andP [H1 H2]];(exists p).
    by move => [p /andP/allL_WS_iff ZZ];(exists p).
  Qed.

  Lemma clos_t_to_paths_l R (X: set T) st x y:
    allL (Δ_(X) `;` R) st x y <-> (x::st) [\in] X /\ allL R st x y /\ (x :: st) [\in] (Δ_(X) `;` R).+#_(y).
  Proof.
    split;last by rewrite allL_WS_iff => -[-> [-> _]].
    by move => /[dup] /allL_WS_iff/andP [? ?] /(@allL_All _ (Δ_(X) `;` R) st x y) ?. 
  Qed.
  
  Lemma clos_t_to_paths_l' R (X: set T) st x y:
      allL (Δ_(X) `;` R) st x y <-> (x::st) [\in] X /\ allL R st x y /\ (x :: st) [\in] R.+#_(y).
  Proof.
    split;last by rewrite allL_WS_iff => -[-> [-> _]].
    by move => /allL_WS_iff/andP [? +] => /[dup] ? /(@allL_All _ R st x y) ?. 
  Qed.

  Lemma clos_t_to_paths_r R (X: set T) st x y:
    allL (R `;` Δ_(X)) st x y <-> (rcons st y) [\in] X /\ allL R st x y /\ ((rcons st y) [\in] x _:#(R `;` Δ_(X)).+). 
  Proof.
    split;last by rewrite allL_SW_iff => -[-> [-> _]].
    by move => /[dup] /allL_SW_iff/andP [? ?] /(@allL_AllA _ (R `;` Δ_(X)) st x y) ?. 
  Qed.
  
  Lemma clos_t_to_paths_r' R (X: set T) st x y:
    allL (R `;` Δ_(X)) st x y <-> (rcons st y) [\in] X /\ allL R st x y /\ ((rcons st y) [\in] x _:#R.+). 
  Proof.
    split; first by move => /allL_SW_iff/andP [? +] => /[dup] ? /(@allL_AllA _ R st x y) ?. 
    by rewrite allL_SW_iff => -[-> [-> _]].
  Qed.
  
End PathRel.

(* orientation  *)
(* begin snippet OO:: no-out *)
Inductive O := | P | N.
(* end snippet OO *)

(* begin snippet Oedge:: no-out *)  
Definition Oedge {T: Type} (R: relation T): set (T*T*O) :=
  [set oe: T*T*O | (match oe with | (e,P) => R e | (e,N) => R^-1 e end)].
(* end snippet Oedge *)
  
(* begin snippet ChrelO:: no-out *)  
Definition ChrelO {T: Type} := [set ppa: (T*T*O)*(T*T*O) | (ppa.1.1).2 = (ppa.2.1).1].
(* end snippet ChrelO *)  

(* begin snippet Atr:: no-out *)  
Definition A_tr {T: Type} (X: set T) (R: relation T) := 
  ChrelO `&` 
    [set oe : (T*T*O) * (T*T*O)| match (oe.1.2,oe.2.2, oe.1.1.2) with 
                                 | (P,P,v) => X.^c v | (N,N,v) => X.^c v | (N,P,v) => X.^c v
                                 | (P,N,v) => (Fset R.* X) v end].
(* end snippet Atr *)
 
(* begin snippet ActiveOe:: no-out *)  
Definition ActiveOe {T: Type} (X: set T) (R: relation T) :=  
  ((Oedge R) `*` Oedge R) `&` (A_tr X R).
(* end snippet ActiveOe *)  

(* Equivalent definition see ActiveOe_iff used in proofs *)
Definition ActiveOe' {T: Type} (X: set T) (R: relation T) := 
  [set oe : (T*T*O) * (T*T*O) | 
    Oedge R oe.1 /\ Oedge R oe.2 /\ (ChrelO oe)
    /\ match (oe.1.2,oe.2.2, oe.1.1.2) with 
      | (P,P,v) => X.^c v
      | (N,N,v) => X.^c v
      | (N,P,v) => X.^c v
      | (P,N,v) => (Fset R.* X) v
      end].

(* Active is now almost expressed as a transitive closure 
 * on an lifted space (A * A) * O as it uses AllL *)
(* begin snippet Aeop:: no-out *)  
Definition Active_path
  {T: Type} (X: set T) (R: relation T) (p: seq (T*T*O)) (x y: T) :=
  match p with 
  | [::] => x = y 
  | [::eo1] => eo1.1.1 = x /\  eo1.1.2 = y /\  Oedge R eo1 
  | eo1 :: [:: eo2 & p]
    => eo1.1.1 = x /\ (last eo2 p).1.2 = y 
      /\ allL (ActiveOe' X R) (belast eo2 p) eo1 (last eo2 p)
  end.
(* end snippet Aeop *)

Definition O_rev (o:O) := match o with | P => N | N => P end.

Definition R_o {T: Type} (R: relation T) (o:O):= 
  match o with | P => R | N=> R^-1 end.

(** * The D_separated and Active relation as a relation on TxT *)
  
(* begin snippet Dseparated:: no-out *)  
Definition D_separated {T: Type} (W: set T) (E: relation T) (x y: T) := 
  ~(exists (p: seq (T*T*O)), Active_path W E p x y).
(* end snippet Dseparated *)  

(* begin snippet Active:: no-out *)  
Definition Active {T: Type} (W: set T) (E: relation T) (x y: T) :=
  (exists (p: seq (T*T*O)), Active_path W E p x y).
(* end snippet Active *)  

Section Active_paths.
  (** * D_U and active relation *)
  
  Context {T: Type}.
  Implicit Types (W X: set T) (R: relation T) (o: O) (p: seq (T*T*O)).

  Lemma R_o' R o (xy: T*T): 
      R_o R o xy <-> match o with | P => R xy | N=> R^-1 xy end.
  Proof. by case: o. Qed.
  
  Lemma Active_path1 R X:  forall (eo1: T*T*O), 
    Active_path X R [::eo1] eo1.1.1 eo1.1.2 <-> Oedge R eo1. 
  Proof. by move => eo1;rewrite /Active_path;split => [[? [? ?]]// | //]. Qed.
  
  (** * case [:: eo1, eo2 & p] *)
  Lemma Active_path_cc' R X: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) ,
      Active_path X R [:: eo1, eo2 & p] eo1.1.1 (last eo2 p).1.2
      <-> Active_path X R [:: eo2 & p] eo2.1.1 (last eo2 p).1.2 /\ ActiveOe' X R (eo1, eo2).
  Proof.
    elim => [ | eo3 p _] eo1 eo2.
    - split;first by move => [_ [/= _ /allL0' /[dup] ?] [H1 [H2 _]]]. 
      by move => [[_ [<- H3]] /inP H4] /=; rewrite allL0.
    - split;first by move => [? [/= ? /= /allL_c/andP [/inP ? ?]]].
      by move => [[_ [H3 H4]] /inP H5] /=;rewrite allL_c;split;[|split;[|apply /andP]].
  Qed.
  
  Lemma Active_path_cc_ht R X p: forall (eo1 eo2: T*T*O) (x y: T),
      Active_path X R [:: eo1, eo2 & p] x y -> x = eo1.1.1 /\ y = (last eo2 p).1.2.
  Proof. by move => eo1 eo2 x y [H1 [H2 _]]. Qed. 
  
  Lemma Active_path_cc R X:  forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path X R [:: eo1, eo2 & p] x y
      <-> (x = eo1.1.1 /\ y = (last eo2 p).1.2) 
        /\ Active_path X R [:: eo2 & p] eo2.1.1 y 
        /\ ActiveOe' X R (eo1, eo2).
  Proof.
    move => p eo1 eo2 x y;split.
    by move => /[dup] /Active_path_cc_ht [-> ->] /Active_path_cc' [H3 H4].
    by move => [[-> ->] [H2 H3]]; apply/Active_path_cc'.
  Qed.

  Lemma Active_path_cc_a R X: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path X R [:: eo1, eo2 & p] x y -> ActiveOe' X R (eo1, eo2) .
  Proof. by move => p eo1 eo2 x y /Active_path_cc [_ [_ ?]]. Qed.
  
  
  (** * case (eo1::(rcons p eo2)) *)

  Lemma Active_path_crc' R X: forall  (p: seq (T*T*O)) (eo1 eo2: T*T*O),
      Active_path X R (eo1::(rcons p eo2)) eo1.1.1 eo2.1.2
      <-> allL (ActiveOe' X R) p eo1 eo2.
  Proof.
    elim => [ | eo p H1] eo1 eo2;first by split;[move => [_ [_ /= ?]] |move => ?].
    split; rewrite rcons_cons.
    by move => /Active_path_cc [_ [H2 /inP H3]];rewrite allL_c H3 andTb -H1.
    by move => H2;split;[ | split;[ rewrite last_rcons | rewrite belast_rcons last_rcons]].
  Qed.
  
  Lemma Active_path_crc_ht R X: forall  (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path X R (eo1::(rcons p eo2)) x y -> eo1.1.1 = x /\  eo2.1.2 = y.
  Proof.
    move => p eo1 eo2 x y;rewrite headI;move => [H1 [H2 _]].
    by elim: p H2 => [ //= | a p _ //=]; rewrite last_rcons.
  Qed.
  
  Lemma Active_path_crc_a R X p (eo1 eo2: T*T*O): 
      Active_path X R (eo1::(rcons p eo2))  eo1.1.1 eo2.1.2
      ->  ActiveOe' X R (eo1, (head eo2 p)) /\  ActiveOe' X R ((last eo1 p), eo2).
  Proof. by move  => /Active_path_crc' /[dup] /allL_splitl [_ H2] /allL_splitr [H3 _].  Qed.
  
  Lemma Active_path_crc R X: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path X R (eo1::(rcons p eo2)) x y
      <-> (x = eo1.1.1 /\ y= eo2.1.2) /\ allL (ActiveOe' X R) p eo1 eo2.
  Proof. 
    move => p eo1 eo2 x y.
    split;last by move => [[-> ->] /Active_path_crc' H3].
    move => /[dup] /Active_path_crc_ht [H1 H2] +;rewrite -H1 -H2. 
    by move => /Active_path_crc' H3.
  Qed.

  (** * case  (rcons (rcons p eo1) eo2) *)
  
  Lemma Active_path_rcrc' R X: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O),
      Active_path X R (rcons (rcons p eo1) eo2) (head eo1 p).1.1 eo2.1.2
      <-> Active_path X R (rcons p eo1) (head eo1 p).1.1 eo1.1.2 /\ ActiveOe' X R (eo1, eo2).
  Proof.
    elim => [ | eo p H1] eo1 eo2.
    - split; last by  move => [_ H2] /=;rewrite allL0'.
      by move => [_ [_ /= /allL0' H3]];move: (H3) => [H1 _].  
    - rewrite !rcons_cons Active_path_crc'.
      split; first by move => /allL_rc/andP [/inP H2 H3];rewrite Active_path_crc.
      by rewrite Active_path_crc'  => -[H2 /inP H3]; rewrite allL_rc;apply/andP.
  Qed.
  
  Lemma Active_path_rcrc_ht R X: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path X R (rcons (rcons p eo1) eo2) x y 
      -> x = (head eo1 p).1.1 /\ y= eo2.1.2.
  Proof.
    elim => [ | eo p H1] eo1 eo2 x y; first by move => [H1 [H2 _]]; split.
    by rewrite !rcons_cons => /Active_path_crc_ht [H2 H3].
  Qed.

  Lemma Active_path_rcrc_a R X: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y: T),
      Active_path X R (rcons (rcons p eo1) eo2) x y 
      -> ActiveOe' X R (eo1, eo2).
  Proof.
    move => p eo1 eo2 x y /[dup] /Active_path_rcrc_ht [H2 H3].
    by rewrite H2 H3; move => /Active_path_rcrc' [_ H1].
  Qed.

  Lemma Active_path_rcrc R X: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (x y:T),
      Active_path X R (rcons (rcons p eo1) eo2) x y
      <-> (x = (head eo1 p).1.1 /\ y= eo2.1.2)
        /\ Active_path X R (rcons p eo1) (head eo1 p).1.1 eo1.1.2 /\ ActiveOe' X R (eo1, eo2).
  Proof.
    move => p eo1 eo2 x y;split.
    by move => /[dup] /Active_path_rcrc_ht [-> ->] /Active_path_rcrc' [H3 H4].
    by move => [[-> ->] [H2 H3]]; apply/Active_path_rcrc'.
  Qed.


  (**  case (rcons p eo1) *)
  Lemma Active_path_rc_hto R X: forall (p: seq (T*T*O)) (eo1: T*T*O) (x y: T),
      Active_path X R (rcons p eo1) x y ->
      x = (head eo1 p).1.1 /\ y = eo1.1.2 /\ Oedge R eo1 /\ Oedge R (head eo1 p).
  Proof.
    elim => [eo1 x y [H2 [H3 H4]] // | eo1 p _ eo2 x y]. 
    move => /Active_path_crc [[H1 H2] H3].
    move: H3 => /[dup] /allL_splitl [_ +] /allL_splitr [+ _].
    by move  => -[_ [/= H4 _]] -[/= H5 _].
  Qed.
  
  Lemma Active_path_c_hto R X: forall (p: seq (T*T*O)) (eo1: T*T*O) (x y: T),
      Active_path X R (eo1::p) x y -> 
      x = eo1.1.1 /\ y = (last eo1 p).1.2
      /\ Oedge R eo1 /\ Oedge R (last eo1 p).
  Proof.
    elim => [eo1 x y [H1 [H2 H3]] // | eo2 p Hr eo1 x y]. 
    move => /Active_path_cc [[H1 H2] [/Hr [_ [_ [_ H3]]] +]].
    by move => -[/= H4 _].
  Qed.

  (* compatibility with old version *)
  Lemma Active_path_cc_old R X: forall (p: seq (T*T*O)) (eo1 eo2: T*T*O) (y: T),
      Active_path X R [:: eo1, eo2 & p] eo1.1.1 y
      <-> Active_path X R [:: eo2 & p] eo2.1.1 y /\ ActiveOe' X R (eo1, eo2).
  Proof.
    move => p eo1 eo2 y. 
    split; first by move /Active_path_cc => [H1 [H2 H3]].
    move => [/[dup] H1 /Active_path_c_hto [_ [H2' _]] H3].
    rewrite H2' in H1.
    by rewrite Active_path_cc H2'. 
  Qed.
    
  Lemma Active_path_split R X : forall (p q: seq (T*T*O)) (eop eoq: T*T*O) (x y: T),
      Active_path X R ((rcons p eop)++ eoq::q) x y
      -> Active_path X R (rcons p eop) x eop.1.2
        /\ Active_path X R (eoq::q) eoq.1.1 y
        /\ ActiveOe' X R (eop, eoq).
  Proof.
    elim => [ q eop eoq x y // | z p Hr q eop eoq x y ].
    + rewrite cat_rcons cat0s => /Active_path_cc [[H1 H2] [H3 H4]]. 
      by move: H4 => /[dup] ? [? _]. 
    + elim/last_ind: q Hr eop eoq x y.
      + move => _ eop eoq x y.
        rewrite -cat_rcons cats0 Active_path_rcrc => -[[-> ->] [H3 +]].
        by rewrite Active_path1 => /[dup] H4 [_ [H6 _]].
      + move => q1 t _ H1 eo1 eo2 x y H3.
        rewrite rcons_cons cat_cons -rcons_cons -rcons_cat in H3.
        pose proof Active_path_crc_ht H3 as [H4 H5].
        move: H3; rewrite -H4 -H5.
        move => /Active_path_crc' /allL_cat/andP [H6 /allL_c/andP [/inP H7 H8]]. 
        by rewrite rcons_cons Active_path_crc Active_path_crc. 
  Qed.

  Lemma Active_path_cat R X: forall (p q: seq (T*T*O)) (eop eoq: T*T*O) (x y z: T),
      ActiveOe' X R (eop, eoq)
      /\ Active_path X R (rcons p eop) x y 
      /\ Active_path X R (eoq::q) y z
      -> Active_path X R (rcons p eop ++ eoq::q) x z.
  Proof.
    elim. 
    - move => q eop eoq x y z [H1 [H2 H3]].
      have -> : rcons [::] eop ++ eoq :: q = [:: eop, eoq & q] by [].
      pose proof Active_path_rc_hto H2 as [H4 _].
      pose proof Active_path_c_hto H3 as [H6 [H7 _]].
      by rewrite H4 Active_path_cc -H6.
    - move => eo1 p1 Hr q eop eoq x y z [H1 [H2 H3]]. 
      rewrite rcons_cons cat_cons.
      rewrite rcons_cons in H2.
      elim/last_ind: q Hr H1 H2 H3.
      + move => _ /inP H1 H2 H3.
        pose proof Active_path_crc_ht H2 as [H4 H5].
        have [H7 H8]: y = eoq.1.1 /\ z = eoq.1.2 by move: H3 => [H3 [H3' _]].
        move:H2; rewrite -H4 -H5 Active_path_crc => -[[H9 H10] H11].
        by rewrite cats1 H8 Active_path_crc allL_rc H1 andTb. 
      + move => q1 eoq1 _ _ /inP H2 H3 H4.
        pose proof Active_path_crc_ht H3 as [H5 H6].
        pose proof Active_path_crc_ht H4 as [H7 H8].
        move: H3;rewrite -H5 -H6 Active_path_crc => -[_ H3]. 
        move: H4;rewrite -H7 -H8 Active_path_crc => -[_ H4]. 
        rewrite -rcons_cons -{1}cat_rcons -/rcons -rcons_cat.
        by rewrite Active_path_crc allL_cat H4 andbT allL_rc H2 H3.
  Qed.
  

  Lemma Active_path_iff R X: forall (p q: seq (T*T*O)) (eop eoq: T*T*O) (x y z: T),
      ActiveOe' X R (eop, eoq)
      /\ Active_path X R (rcons p eop) x y 
      /\ Active_path X R (eoq::q) y z
      <-> Active_path X R (rcons p eop++ eoq::q) x z /\ y= eop.1.2.
  Proof.
    move => p q eop eoq x y z.
    split => [ [H1 [H2 H3]] | [H1 H2]].
    - pose proof Active_path_rc_hto H2 as [_ [H4 _]].
      by split;[apply Active_path_cat with y | ].
    - pose proof Active_path_split H1 as [H3 [H4 H5]].
      pose proof H5 as [_ [H7 [H8 _]]].
      by split;[ | split;[rewrite H2 | rewrite H2 H8]].
  Qed.

  Lemma Active_path_cat' R X: forall (p q: seq (T*T*O)) (x y z: T),
      (exists (p' q': seq (T*T*O)), exists (eop eoq: T*T*O),
          p = rcons p' eop /\ q = eoq::q' /\  ActiveOe' X R (eop, eoq))
      /\ Active_path X R p x y 
      /\ Active_path X R q y z
      -> Active_path X R (p++q) x z.
  Proof.
    move => p q x y z [[p1 [q1 [eop [eoq [H1 [H2 H3]]]]]] [H4 H5]].
    by rewrite H1 H2; apply Active_path_cat with y; rewrite -H1 -H2.
  Qed.

End Active_paths.

Section pair. 
  (** * sequences of oriented arcs i.e seq (T*T*O) *)

  Context {T: Type}.
  Implicit Types (stt: seq (T*T)) (so:seq O).
  
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
    rewrite 2!pair_c 2!Lift_cc 2!allset_cons.
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
    rewrite unpair_c Lift_cc allset_cons.
    split => [ [H1 /Hr' H2] /= |].
    - rewrite /Extend /mkset /= -inP in H1.
      by rewrite  H1 andbC andbT.
    - rewrite unpair_c Lift_cc allset_cons.
      move => [H1 H2].
      split. by [].
      apply Hr'.
      by rewrite unpair_c.
  Qed.

End pair.

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

Section Active_paths_simple. 
  (** * Active paths with constant orientation *)
  
  Context {T: Type}.
  Implicit Types (T : Type) (W: set T) (E: relation T) (p: seq T) (x y: T) (o:O).
  
  Lemma Active_path_simple E W: forall (p: seq T) (x y: T) (o:O),
      p [\in] W.^c /\ allL (R_o E o) p x y 
      <-> Active_path W E (Lifto (x::(rcons p y)) o) x y.
  Proof.
    split.
    + elim: p x y => [x y [_ /allL0' /R_o' _] // | x1 p _ x y]. 
      rewrite allset_consb allL_c => -[ /andP [H2 H'2] /andP [/inP H3 H4]].
      rewrite Lifto_crc Lifto_rcc Active_path_crc' /=. 
      elim: p x x1 H3 H2 H'2 H4 => [x x1 H3 /inP H1 _ /allL0' H4 // | ].  
      ++ by rewrite allL0 /=; apply mem_set; split;case: o H3 H4 => /R_o' H3 /R_o' H4.
      ++ move => z p H1 x1 x H3 /inP H2 /allset_cons [H4 H4'] /allL_c/andP [/inP H5 H6] /=. 
         rewrite Lifto_c allL_c;apply /andP;split; last first. 
         by apply: (H1 x z H5 _ H4' H6); apply mem_set. 
         clear H1 H6;apply mem_set.         
         by case: o H3 H5 => /R_o' H3 /R_o' H5. 
    + elim: p x y;
        first by move => x y //= [_ [_ H]];
                        split; elim: o H => H;[ | | apply /allL0'/R_o' | apply /allL0'/R_o'].
      
      move => z p H1 x y; rewrite Lift_o_cons;elim: p x y H1. 
      move => x y H1 /Active_path_cc_old H2. 
      move: H2;move => [H2 [H3 [H4 [H5 H6]]]].
      elim: o H1 H2 H3 H4 H5 H6 => /= H1 H2 H3 H4 H5 H6.
      rewrite andbT.
      split. apply mem_set. by []. rewrite /allL /=.
      by move: H3 => /inP ->;move: H4 => /inP ->.
      rewrite andbT.
      split. apply mem_set. by []. rewrite /allL /=.
      by move: H3 => /inP ->;move: H4 => /inP ->.
      (* size p >= 2 *)
      move => t p _ x y H2;rewrite Lift_o_cons;move => /Active_path_cc_old [/H2 [H3 H5] H4].
      split.
        rewrite allset_cons andC. 
        split;[ | move: H4 => [_ [_ [_ H4]]]].
        by elim: o H2 H4 H5 => _ H4 H5.
        by elim: o H2 H4 H5 => _ /= H4 H5.
        rewrite allL_c H5 andbT.
        by elim: o H2 H4 H5 => _ [/= /inP H4 _] _ /=.
  Qed.
  
End Active_paths_simple.  

(* 
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
  

Section Extended_Oriented_Paths.
      
  (** * pair combined with Lift *)
  Variable (T:Type) (tv:T) (ptv: T*T).
  
  (* begin snippet LiftO:: no-out *)  
  Definition LiftO (st: seq T) (so: seq O) := pair (Lift st) so.
  (* end snippet LiftO *)  
  
  (* begin snippet LiftOp:: no-out *)  
  Definition LiftOp (stso: (seq T)*(seq O)) := pair (Lift stso.1) stso.2.
  (* end snippet LiftOp *)  
  
  
  Definition UnLiftO (p: seq (T*T*O)) (x: T) :=
    (UnLift (unpair p).1 x, (unpair p).2).

  Definition UnLiftO1 (p: seq (T*T*O)) (x: T) := UnLift (unpair p).1 x.
  
  Lemma Oedge_rev: forall (E: relation T) (x y: T),
      Oedge E (x,y,P) = Oedge E (y,x,N).
  Proof.
    by move => E x y.
  Qed.
  
  Lemma Oedge_inv: forall (E: relation T) (x y: T) (o:O),
      Oedge E (x,y,o) = Oedge E^-1 (x,y, O_rev o).
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
 
  Lemma A_tr_P1: forall(W: set T) (E: relation T), A_tr W E = ChrelO `&` (A_tr W E).
  Proof.
    by move => W E;rewrite /A_tr setIA setIid.
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
        by pose proof (@ActiveOe_ChrelO T);apply allset_subset with (ActiveOe W E);
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
*)


Section Active_path_unique. 
  
  Variables (T: Type). 

  Lemma ChrelO_eq: forall (x y z t: T) (o1 o2:O),
      ChrelO ((x,y,o1), (z,t,o2)) <-> y = z.
  Proof. by []. Qed.
  
    (** * If there exists an active path from x to y there exists a walk from x to y
        we just prove that when a variable is repeated twice we can shorten the
        active path * to prove the general property, we have maybe to switch from
        Type to eqType to use unique * in seq ?  *)
    
    Lemma Oedge_Fset R X:  forall (u v: T), Oedge R (u,v, P) /\ R.*#X v -> R.*#X u.
    Proof.
      move => u v [H1 [w [H2 H3]]]. 
      have H4: (R `;` R.* ) (u,w) by (exists v).
      have H5:  (R.+ `<=` R.*  ) by apply clos_t_clos_rt.
      have H6: R.* (u, w) by rewrite r_clos_rt_clos_t in H4 ;apply H5 in H4.
      by (exists w).
    Qed.

    Lemma Active_path_Fset R X:  forall (p: seq T) (x y: T),
        Active_path X R ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ R.*#X (last y p) -> R.*#X x. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        move => x y [[_ [_ H2]] H3].
        by apply Oedge_Fset with y.
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc.
        move => [[[H1 H1'] [H2 H3]] H4].
        have H5: R.*#X y by apply Hr with z.
        move: H3 => [H3 _].
        by apply Oedge_Fset with y.
    Qed.

    Lemma Active_path_Fset' R X:  forall (p: seq T) (x y: T),
        Active_path X R ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ R.*#X (last y p) -> R.*#X y. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        by move => x y [[_ [_ H2]] H3].
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc.
        move => [[[H1 H1'] [H2 H3]] H4].
        have H5: R.*#X z by apply Hr with y.
        move: H3 => [_ [H3 _]].
        by apply Oedge_Fset with z.
    Qed.

    Lemma Active_path_shorten_L1 R X: forall (p: seq (T*T*O)) (x y z u v w: T),
        Active_path X R [::(x,y,P),(y,z,P) & (rcons (rcons p (u,v,N)) (v,w,N))] x w
        -> exists (q: seq T), Active_path X R (Lifto [::x,y & q] P) x (last y q) 
                        /\ (Fset R.* X) (last y q).
    Proof. 
      elim => [x y z u v w| ].
      - rewrite -4!rcons_cons Active_path_rcrc'.
        have -> : [:: (x, y, P); (y, z, P)] = rcons [:: (x, y, P)]  (y, z, P) by [].
        rewrite Active_path_rcrc' /head.
        move => [[H1 [H'2 [H'3 [/ChrelO_eq H'4 H'5]]]] [H3 [H4 [_ H6]]]].
        by (exists [::z]).
      - move => [[t s] o] p Hr x y z u v w.
        rewrite rcons_cons rcons_cons Active_path_cc_old.
        elim: p Hr.
        + move => Hr [H1 H2].
          move: (H1);
            rewrite Active_path_cc_old => [[_ [_ [_ [/ChrelO_eq H3 _]]]]];
                                               rewrite <- H3 in *.
          elim: o H1 => [ /Hr [q [H1 H4]] | ].
          ++ exists [:: z & q].
             by rewrite Lifto_c Lifto_c Active_path_cc_old  -Lifto_c /last_cons.
          ++ exists [::z].
             move: H1 => /Active_path_cc_old H1. 
             move: H1;move => [H1 [_ [_ [_ H7]]]].
             move: (H2) => [H2' [H2'' _]].
             rewrite !Lifto_c Active_path_cc_old -Lifto_c /last.
             by split.
        + move => [[a b] o2] p _ H1 H2.
          move: (H2);rewrite Active_path_cc_old rcons_cons rcons_cons;
            move => [[_ [_ [_ [/ChrelO_eq H6 _]]]] _].
          rewrite <- H6 in *; clear H6.
          elim: o H2 => [[H2 H3] | ].
          ++ apply H1 in H2;move:H2 => [q H2].
             exists [::z].
             move: H2;rewrite Lifto_c => [[H2 H4]].
             rewrite /Lifto /Lift /pair_o.
             rewrite Active_path_cc_old last_cons /last.
             move: (H3) => [H5 [H6 _]].
             specialize Active_path_Fset' with R X q y z => H7.
             by split;[split | apply H7].
          ++ move => [H2 H3].
             pose proof H2 as H5.
             rewrite Active_path_cc_old in H2.
             rewrite Active_path_crc in H2.
             move: H2;move => [H2 [_ [_ [_ H8 ]]]].
             exists [::z];rewrite last_cons /last.
             split. 
             by rewrite /= allL0'.
             by [].
    Qed.

    Lemma Active_path_shorten_L2  R X: forall (p: seq (T*T*O)) (x y z u w: T),
        Active_path X R [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> R.*#X y. 
    Proof. 
      move => p x y z u w H1.
      pose proof Active_path_shorten_L1 H1 as [q H2].
      rewrite Lifto_c in H2.
      by apply  Active_path_Fset' in H2.
    Qed.

    Lemma Active_path_shorten_L3 R X: forall (p: seq (T*T*O)) (x y z u w: T) (o1 o2 o3 o4:O) ,
        Active_path X R [::(x,y,o1),(y,z,o2) & (rcons (rcons p (u,y,o3)) (y,w,o4))] x w
        -> ActiveOe' X R ((x,y,o1), (y,z,o2)) /\ ActiveOe' X R ((u,y,o3),(y,w,o4)).
    Proof.
      move => p x y z u w o1 o2 o3 o4 /[dup] + /Active_path_cc [_ [_ H3]].
      by rewrite -4!rcons_cons => /Active_path_rcrc [_ [_ H4]]. 
    Qed.

    Lemma Active_path_shorten_L4 R X: forall (p: seq (T*T*O)) (x y z u w: T),
        Active_path X R [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> ActiveOe' X R ((x,y,P), (y,w,N)).
    Proof. 
      by move => p x y z u w /[dup] /Active_path_shorten_L2 ?
               /Active_path_shorten_L3 [[? _] [_ [? _]]].
    Qed.
    
    Lemma Active_path_shorten R X: forall (p: seq (T*T*O)) (x y z u w: T) (o1 o2 o3 o4:O) ,
        Active_path X R [::(x,y,o1),(y,z,o2) & (rcons (rcons p (u,y,o3)) (y,w,o4))] x w
        -> ActiveOe' X R ((x,y,o1), (y,w,o4)).
    Proof. 
      move => p x y z u w. 
      case;case;case;case;
        move => /[dup] H1 /Active_path_shorten_L3 [[H2 [_ [_ H4]]] [_ [H3 [_ H5]]]];
             by [ | move: H1 => /Active_path_shorten_L4 H1].
    Qed.
    
End Active_path_unique. 
