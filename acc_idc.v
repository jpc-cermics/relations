(* -*- Encoding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Coq Require Import Program.Wf.

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

Section Definitions.
  (** * following 
      https://proofwiki.org/wiki/Infinite_Sequence_Property_of_Strictly_Well-Founded_Relation
   *)

  Variables (T : Type).

  Definition minimal_elt (R: relation T) (S: set T) (x:T) :=
    x\in S /\ forall (y:T), y \in S -> R (y,x) -> y=x.

  Definition well_founded_rel_1 (R: relation T) 
    := forall (S: set T), ~ (S = set0) ->
                     exists m, m \in S /\ (forall s, s \in S -> ~ (s = m) -> ~ (R (s,m))).
  
  Definition well_founded_rel_2 (R: relation T) 
    := forall (S: set T),  ~ (S = set0) -> exists x, minimal_elt R S x.

  Definition strictly_minimal_elt (R: relation T) (S: set T) (x:T) :=
    x\in S /\ forall (y:T), y \in S -> ~ R (y,x).
  
  Definition strictly_well_founded_rel_v1 (R: relation T) 
    := forall (S: set T), ~ (S = set0) -> exists x, strictly_minimal_elt R S x.

  Definition strictly_well_founded_rel_v2 (R: relation T) 
    := forall (S: set T), ~ (S = set0) -> exists m, m \in S /\ (forall s, s \in S -> ~ R (s,m)).
  
  (** * irreflexive: ∀x, (x,x)∉R *)
  Definition strictly_well_founded_rel_v3 (R: relation T) 
    :=  irreflexive R /\ well_founded_rel_1 R. 
  
  (** total (or left total)  *) 
  Definition total_rel (R: relation T) := forall x, exists y, R (x,y).

  Definition iic (R: relation T) := exists f : nat -> T, forall n, R ((f n),(f (S n))).  
  (** * axiom of dependent choice *) 
  Axiom DC: forall (R: relation T),  total_rel R -> iic R. 
  
  (** right total *) 
  Definition right_total_rel (R: relation T) := forall y, exists x, R (x,y).
  
  (** * infinite descending chain *)
  Definition idc (R: relation T) := exists f : nat -> T, forall n, R ((f (S n)),(f n)).

  Definition restr_rel (R: relation T) (X: set T)
    :=[set xy : X*X | R ((sval xy.1), (sval xy.2))].
  
  (** * With the DC axiom we have that 
      R well_founded_rel <-> ~ idc 
   *)

  (** * when a relation is well_founded we can use a transfinite induction *)

  Definition well_founded_induction (R:relation T) (P: T-> Prop):= 
    (forall x, (forall y, R(y,x) -> P(y)) -> P x) -> (forall x, P x).
  
  Definition idc_from (R:relation T) a0:=
    exists f : nat -> T, f 0 = a0 /\ forall n, R ((f (S n)),(f n)).

  (** * well_founded_induction: See coq/theories/Init/Wf.v *)
  Lemma well_founded_ind_irreflexive (R : relation T) (wfR : well_founded (curry R)): 
    forall x y : T, R (x,y) -> x = y -> False.
  Proof.
    move => x y + H1;rewrite -H1 => Ryy; clear H1 y.
    elim: (wfR x) Ryy => [y accy IHy Ryy].
    apply (IHy _ Ryy Ryy).
  Qed.
  
  (* Print Acc.  Print well_founded. *)
  
  Lemma well_founded_ind_antisym  (R : relation T) (wfR : well_founded (curry R)):
        forall x y : T, R (x,y) -> R (y,x) -> False.
  Proof.
    intros x y Rxy Ryx. red in wfR.
    induction (wfR y) as [y _ IHy] in x, Rxy, Ryx. clear wfR.
    specialize (IHy _ Rxy). apply (IHy _ Ryx Rxy).
  Qed.
  
End Definitions. 

Section wfr_properties. 
  (** * Properties of well founded relations.  *)

  Variables (T : Type).

  Lemma in_set1: forall (x y:T), x \in [set y] <-> x = y.
  Proof. by move => x y;rewrite inE /set1 /mkset. Qed.
  
  Lemma well_founded_rel_equiv (R: relation T):
    well_founded_rel_1 R <->  well_founded_rel_2 R.
  Proof.
    split. 
    - move => + S => /(_ S) H1 /H1 [s [H2 H3]].
      exists s;split => [// | s' H4 H5].
      have [->// | H6]: (s' = s ) \/ ~(s' = s) by apply: EM.
      by pose proof ((H3 s') H4 H6).
    - move => H1 S /H1 [m [H2 H3]].
      exists m. split => [// | s H4 H5 H6].
      by have: s = m by apply: ((H3 s) H4 H6).
  Qed.

End wfr_properties. 

Section swfr_properties.
  (** * Properties of strictly well founded relations.  *)

  Variables (T : Type).
  
  Lemma swfr_irreflexive (R: relation T) :
    strictly_well_founded_rel_v2 R -> irreflexive R. 
  Proof.
    move => H1 x.
    have H2: [set x] = set0 -> False
      by (have H3: x \in [set x] by rewrite inP);move => H4;rewrite H4 in_set0 in H3.
    rewrite  /strictly_well_founded_rel_v2 in H1.
    move: H2 => /H1 [m [/in_set1 -> H3]].
    by apply: H3;rewrite in_set1.
  Qed.

  (* A relation, R, is antisymmetric if (a,b) in R implies (b,a) is not in R, unless a=b.
     It is asymmetric if (a,b) in R implies (b,a) is not in R, even if a=b. *)
  
  Lemma swfr_asymetric (R: relation T):
    strictly_well_founded_rel_v2 R -> R `&` R.-1 = set0.
  Proof. 
    move => H1; rewrite predeqE => [[x y]].
    split; last by [].
    move => [H2 H3].
    rewrite -inE in_set0.
    have [H4 H4']: x \in [set x] /\ y \in [set y] by split;rewrite in_set1.
    have H5: x \in [set x;y] by rewrite in_setU H4.
    have H5': y \in [set x;y] by rewrite in_setU H4' orbC.
    have H6: ~ ([set x;y] = set0) by move => H1'; rewrite H1' in_set0 in H5.
    rewrite  /strictly_well_founded_rel_v2 in H1.
    move: H6 H5' H5 => /H1 [m [H6 H7]] /H7 H5' /H7 H5.
    by move: H6 H5 H5'; rewrite in_setU => /orP [/in_set1 -> |/in_set1 ->].
  Qed.

  Lemma swfr_antisymetric (R: relation T):
    strictly_well_founded_rel_v2 R -> antisymmetric R. 
  Proof. 
    move => H1 x y H2 H3.
    have: (R `&` R.-1) (x,y) by split.
    by move: (swfr_asymetric H1) => ->. 
  Qed.

  Lemma strictly_well_founded_rel_v1_v2 (R: relation T):
    strictly_well_founded_rel_v1 R <-> strictly_well_founded_rel_v2 R.
  Proof. by split; move => H1 S /H1 [x [H2 H3]];(exists x). Qed. 

  Lemma awfr_swfr (R: relation T):
    irreflexive R -> well_founded_rel_1 R 
    -> strictly_well_founded_rel_v2 R.
  Proof.
    move => H1 + S => /[apply] [[m [H2 H3]]].
    exists m;split => [// | s /H3 H4].
    by have [-> // | /H4 H5 //]: (s=m ) \/ ~(s=m) by apply: EM.
  Qed.

  Lemma swfr_aswfr (R: relation T):
    strictly_well_founded_rel_v2 R
    -> irreflexive R /\ well_founded_rel_1 R.
  Proof.
    move => H1; split =>[|S H2];first by apply: swfr_irreflexive.
    rewrite /strictly_well_founded_rel_v2 in H1.
    move: (H1 S) H2 =>  /[apply] [[s [H2 H3]]].
    by exists s;split => [// | t /H3 H4 _ //].
  Qed.

  (** * third defintion *)
  Lemma strictly_well_founded_rel_v2_v3 (R: relation T):
    strictly_well_founded_rel_v2 R <-> strictly_well_founded_rel_v3 R. 
  Proof. 
    by split => [| [H1 H2]];[apply: swfr_aswfr | apply: awfr_swfr].
  Qed.

  Lemma not_swfr_right_total (R: relation T): 
    ~ (strictly_well_founded_rel_v2 R) 
    -> exists (X: set T), right_total_rel (@restr_rel T R X).
  Proof.
    rewrite /strictly_well_founded_rel_v2.
    rewrite -existsNE => [[X H1]].
    move: H1;rewrite not_implyE => [[H2 /forallNP H3]].
    
    (* a set is also a Type *)
    have H4: forall (y: X), exists (z: X), (@restr_rel T R X) (z,y).
    move => [y1 H1].
    move: H3 => /(_ y1); rewrite not_andE => [[ H3 // | H3]].
    move: H3; rewrite -existsNE => [[z H5]].
    move: H5; rewrite not_implyE => [[H5 /contrapT H6]].
    by (exists (exist _ z H5)).

    by exists X.
  Qed.

  (** * here we need axiom DC *) 
  Lemma not_swfr_idc (R: relation T): 
    (exists (X: set T), right_total_rel (@restr_rel T R X)) -> (idc R).
  Proof.
    move => [X H1].
    have H7: @total_rel X (@restr_rel T R.-1 X)
      by move => x;move: H1 => /(_ x) [z1 HH];(exists z1).
    move: H7 => /DC [f H8];exists (fun n => (sval (f n)));move => n.
    by move: (H8 n);rewrite /restr_rel /inverse /mkset /=.
  Qed.
  
  Lemma idc_not_swfr (R: relation T): 
    (idc R) -> ~ (strictly_well_founded_rel_v2 R).
  Proof.
    move => [f H1] H2.
    have H3: (f 0) \in [set x | exists n, x= f n] by rewrite inP /mkset; exists 0.
    have H4: ~ ([set x | exists n, x= f n]= set0) by move => H5; rewrite H5 in_set0 in H3.
    move: H4 => /H2 [m [/inP [n H4] H5]].
    have H6: (f n.+1) \in [set x | (exists n : nat, x = f n)]
        by rewrite inP /mkset; exists (n.+1).
    move: H6 => /H5 H6.
    by rewrite H4 in H6.
  Qed.

End swfr_properties.


Section Paper_properties. 
  
  Variables (T: Type) (R: relation T).
  
  Definition Asym (S: relation T) :relation T := [set xy | S xy /\ ~ (S.-1 xy)].
  Definition Rloop (S: relation T) := exists v, forall w,  S (v,w) -> S (w,v).
  
  (* Assumption no infinite chain for (Asym R.+) *)
  Hypothesis A1: (exists (v0:T), (v0 \in setT)).
  (* Hypothesis A2: ~ (iic R). *)
  Hypothesis A3: ~ (iic (Asym R.+)). 
  
  Lemma notloop: forall (S: relation T), ~ (iic (Asym S)) -> (Rloop S).
  Proof.
    move => S; apply contraPP => H1.
    have H2:  total_rel (Asym S)
      by move: H1;rewrite -forallNE => H1 v;move: H1 => /(_ v)/existsNP [w /not_implyP H1];exists w.
    by move: H2 => /DC H2.
  Qed.
  
  Lemma haveA4: Rloop R.+.
  Proof. by apply: notloop. Qed.
  
End  Paper_properties. 

Section wfi_properties. 
  (** * Properties of well founded inductions *)
  Variables (T:Type) (R: relation T).

  (* this is almost immediate in Program.Wf *)
  Lemma ZZ: 
    (forall (P:T->Prop), well_founded_induction R P) -> well_founded (curry R).
  Proof.
    move => H1 x; move: H1 => /(_ (Acc (curry R))) H1.
    apply H1 => [x' H2].
    by move: H2;apply: (@Acc_intro T (curry R)).
  Qed.

  Lemma ZZ2: 
    well_founded (curry R) -> (forall (P:T->Prop), well_founded_induction R P).
  Proof.
    move => H1 P H2 x; move: H1 => /(_ x) H1.
    elim/Acc_ind: H1 => y _ H4.
    by apply H2.
  Qed.

End wfi_properties. 

Section Wfi_Transitive_Closure.
  
  (** Original author: Bruno Barras *)
  Variables (T: Type) (R: relation T).
  
  Lemma Acc_trans_clos : forall x: T, Acc (curry R) x -> Acc (curry R.+) x.
    move => x H0.
    elim: H0 => x0 _ H1.
    apply: Acc_intro.
    move => y H2.
    rewrite -clos_t_decomp_rt_r in H2.
    move : H2 => [/H1 H2 //| [z [/= H2 /H1 H3]]].
    exact: (Acc_inv H3 H2).
  Qed.

  Theorem wf_trans_clos: well_founded (curry R) -> well_founded (curry R.+).
  Proof.
    by rewrite /well_founded_ind => [H1 x]; apply: Acc_trans_clos. 
  Qed.
  
  Lemma Acc_inv_trans : forall (x:T), Acc (curry R) x -> forall (y:T), R.+ (y,x) -> Acc (curry R) y.
  Proof.
    move => x' H1.
    elim/Acc_ind: H1 => x H1 H2 y.
    rewrite -clos_t_decomp_rt_r => [[ H3| [z [/= H4 H5]]]].
    by apply: H1.
    by apply: (H2 z).
  Qed.
  
End Wfi_Transitive_Closure.

Section Inverse_Image.
  (** Author: Bruno Barras *)
  
  Variables (T S: Type) (R : relation S) (f : T -> S).

  Definition inverse_image (V: relation S) := [set xy | V ((f xy.1),(f xy.2))].

  Remark Acc_lemma : forall (y : S),
      Acc (curry R) y -> forall x : T, y = f x -> Acc (curry (inverse_image R)) x.
  Proof.
    move => y' H1.
    elim/Acc_ind: H1 => y H1 H2 x H3.
    apply: Acc_intro => x1 H4. 
    move: H2 H4;rewrite H3 => /(_ (f x1)) H2 /H2 H4.
    by apply: H4.
  Qed.
  
  Lemma Acc_inverse_image : forall (x: T),
      Acc (curry R) (f x) -> Acc (curry (inverse_image R)) x.
  Proof.
    intros; apply (@Acc_lemma (f x)); trivial. 
  Qed.
  
  Theorem wf_inverse_image :
    well_founded (curry R) -> well_founded (curry (inverse_image R)).
  Proof.
    rewrite /well_founded_ind /curry /well_founded.
    move => H1 a.
    by apply Acc_inverse_image. 
  Qed.
  
End Inverse_Image.

Section well_founded_ind. 

  Variables (T:Type) (R: relation T) (a:T).
  
  Lemma wf_not_idc: well_founded (curry R) -> ~(idc R).
  Proof.
    move=> wfR [f hf].
    rewrite /well_founded /curry in wfR. 
    pose proof (measure_wf wfR f).
    apply (Fix (measure_wf wfR f)).
    move=> n h; apply: (h (S n)). 
    rewrite /MR /curry. apply: hf.
    exact 0.
  Qed.
  
  Lemma non_acc_pt : ~(well_founded (curry R)) -> exists a, ~(Acc (curry R) a).
  Proof.  by rewrite -existsNE. Qed.

  (* Context (ha : ~(Acc R a)). *) 

  Definition B:= { x : T | R.* (x,a) /\ ~(Acc (curry R) x) }.

  Definition RB := [set xy : B*B | R ((proj1_sig xy.1), (proj1_sig xy.2))].
  
  Definition P1 (x:T):= (fun y => ~ (R (y, x)) \/ Acc (curry R) y).

  Lemma em_forall (P : T -> Prop ) : (forall a, P a) \/ exists a, ~ (P a).
  Proof.
    have H1: (forall a,  (P a)) \/ ~ (forall a, P(a)) by apply: lem.
    by move: H1 => [H1 | H1]; [left |right; rewrite existsNE].
  Qed.
  
  Lemma right_total_rel_RB: (@right_total_rel B RB).
  Proof.
    rewrite /right_total_rel /RB /mkset /=.
    move=> [x [xa hx]].
    case: (em_forall (fun y => ~ (R (y, x)) \/ Acc (curry R) y)).
    - move=> h0; exfalso; apply hx; constructor=> z accz.
      case: (h0 z)=> // /(_ accz) [].
    - move=> [y0] /not_orP [/contrapT desc hy0].
      unshelve eexists (exist _ y0 _).
      1: split=> //; apply rt_trans with y0. by constructor. 
      apply rt_trans with x. 
      by apply rt_step.
      by [].
      by [].
  Qed.

  Lemma inf_desc_chain : ~(well_founded (curry R)) -> idc R.
  Proof.
    move => H1. 
    pose proof non_acc_pt H1 as [a' ha].
    have H2:  R.* (a',a') /\ ~(Acc (curry R) a') by split;[apply rt_refl |].
    pose proof right_total_rel_RB as H3.
    have H4: total_rel RB.-1 by rewrite /total_rel.
    pose proof DC H4 as [f Hf].
    by exists (fun n => proj1_sig (f n)).
  Qed.
  
  Definition B' := { x : T | R.* (x, a) }.
  Definition RB' :=[ set xy : B'*B'| R ((proj1_sig xy.1), (proj1_sig xy.2))].

  Lemma not_acc (b : B') : right_total_rel R -> ~(Acc (curry RB') b).
  Proof.
    move => eR.
    elim=> -[x hx] h ih; move: (eR x)=> [y hy].
    refine (ih (exist _ y _) hy).
    apply rt_trans with x.
    by apply rt_step.
    by [].
  Qed.
  
  Lemma not_wf : right_total_rel R -> ~(well_founded (curry RB')).
  Proof.
    have a1 : B' by (exists a); by constructor.
    by move=> eR /(_ a1); apply: not_acc.
  Qed.

  Definition Theta (f: nat -> T) (x:T) := 
    fun n => match n with 
          | 0 => x
          | (S m) => f m
          end.
  
  Lemma Tr: forall (k:nat) (f : nat -> T) (x: T),
    (forall n, R (f (S n), f n)) 
    -> (iter R k) (f 0,x) 
    -> exists g: nat -> T, g(0) = x /\ forall n, R (g (S n),g n).
  Proof.
    elim => [f x H1 /Delta_Id H2| n Hr f y H2 H3];first by (exists f).
    move: H3; rewrite -addn1 (iter_compose R n 1) => [[z [/= H3 H4]]].
    move: H4; rewrite Delta_idem_l => H4.
    apply (Hr _ z) in H2; last by [].
    move: H2 => [g [H2 H5]].
    by exists (Theta g y); split; [ | elim => [ | n' _]; rewrite /Theta;[rewrite H2 |]].
  Qed.

  Lemma Tr': forall (f : nat -> T) (x: T),
    (forall n, R (f (S n), f n)) 
    -> R.* (f 0,x) 
    -> exists g: nat -> T, g(0) = x /\ forall n, R (g (S n),g n).
  Proof.
    move => f x Hn.
    rewrite -DuT_eq_Tstar => [[/Delta_Id H1 | H1]].
    by (exists f).
    move: (clos_t_iterk H1) => [k H2].
    apply: (Tr Hn H2).
  Qed.
  
  Lemma reduce_idc_from (b : B') : (idc_from RB' b) -> (idc_from R a).
  Proof.
    move: b=> [? h].
    move=> [g [geq0 hg]].
    (* 
    rewrite /idc_from.
    exists (fun n => proj1_sig (g n)).
    split. 
    rewrite geq0 /=.
    
    move: (h); rewrite clos_rt_rt1n_iff => h'.
    move: {geq0}g (f_equal (@proj1_sig _ _) geq0) hg => /= {h}. 
    induction h'.
    + move=> g geq0 hg; exists (fun n => proj1_sig (g n))=> //.
    + move=> gx geqx hgx.
      unshelve apply: IHh'.
      * case=>[|n]; [| exact (gx n)].
        exists y; by apply: Operators_Properties.clos_rt1n_rt.
      * reflexivity.
      * case=>[|n] /=; last apply: hgx.
        rewrite /RB geqx //=.
  Qed.
   *)
  Admitted.
  
  Lemma dc : forall a0, exists f : nat -> T, f 0 = a0 /\ forall n, R ((f (S n)), (f n)).
  Proof.
    move=> a0.
  Admitted.
  (* 
   mo   ve: (not_wf_idc (B a0) (RB a0) (not_wf a0))=> [g hg].
   apply    : (reduce_idc_from a0 (g 0)); exists g; split=> //.
  Q       ed  .
   *)

  (* 
  Context (not_wf_idc : forall (R : relation T), ~(well_founded_ind R) -> idc R).
  Context (P : Prop).
  Definition RP := [set xy: unit*unit | P].
  Lemma not_wf_RP : ~ ~ P -> ~(well_founded_ind RP).
  Proof.
    move=> nnp wfRP; apply: nnp=> p.
    by elim: (wfRP tt) => x _ /(_ x) H1.
  Qed.
  
  Lemma dne : ~ ~ P -> P.
  Proof.
    move=> /not_wf_RP H1. 
    apply (@not_wf_idc (relation unit)) in H1.
    /not_wf_idc HH.  [? hf].
    exact (hf 0).
  Qed.
   *)

End  well_founded_ind.






