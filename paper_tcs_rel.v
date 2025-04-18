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

From AAC_tactics Require Import AAC.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel  aacset paper_relations. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** * some relations results used in Tcs *)

Section Tcs_Lemma7. 

  (** * Lemma 7 of Tcs *)
  Lemma L14_E38a : (Emw.* `;` Ew.* ) =
                    ('Δ `|` (Δ_(W.^c) `;` Bw) `|` (Bmw `;` Δ_(W.^c)) `|` Kw).
  Proof.
    have L14_E38a1 : Ew.+ = Δ_(W.^c) `;` Bw                            
      by rewrite /Bw -composeA -/Ew r_clos_rt_clos_t.
    have L14_E38a2 : Emw.+ = Bmw `;` Δ_(W.^c)
      by rewrite -inverse_clos_t L14_E38a1 inverse_compose -/Bmw DeltaE_inverse.
    by rewrite L1 !composeDr !composeDl !Delta_idem_r !Delta_idem_l setUA -E9e;
    rewrite -L14_E38a2 -L14_E38a1.
  Qed.

  Lemma L14_E38b : Cw `;` (Emw.* ) `;` (Ew .* ) = Cw `;` ('Δ `|` (Bmw `;` Δ_(W.^c)) `|` Kw).
  Proof.
    have H1: ( Δ_(W) `;` (Δ_(W.^c) `;` Bw)) = 'Δc
      by rewrite -composeA DeltaW_Wc DeltaC_compose_absorbl.
    rewrite composeA L14_E38a {1}Cw_ends composeA !composeDl H1.
    rewrite DeltaC_compose_absorbr.
    rewrite !Delta_idem_r -Cw_ends.
    rewrite -composeA -Cw_ends.
    rewrite -{1}composeA -{1}composeA -{1}composeA -Cw_ends.
    by rewrite DeltaC_union_idemr.
  Qed.

  (* Equation (E23c) *)

  Lemma L14_E38c1 : (Cw `;` (Emw.* ) `;` (Ew.* )) `;` Cw  = Cw `;` ((Δ_(W) `|` Kw `;` Δ_(W)) `;` Cw).
  Proof.
    have H1: Δ_(W.^c) `;` Cw = 'Δc
      by rewrite Cw_starts -composeA DeltaWc_W DeltaC_compose_absorbl.
    have H2: Bmw `;` Δ_(W.^c) `;` Cw = 'Δc
      by rewrite composeA H1 DeltaC_compose_absorbr.
    have H3:  Δ_(W) `;` Cw `|` Kw `;` ( Δ_(W) `;` Cw) = ( Δ_(W) `|` Kw `;`  Δ_(W)) `;` Cw
      by rewrite -[(Kw) `;` (_ `;` _)]composeA -composeDr.
    by rewrite L14_E38b composeA composeDr composeDr H2 DeltaC_union_idemr Delta_idem_l
         {2 3}Cw_starts H3.
  Qed.

  Lemma L14_E38c2 : forall (R: relation T), 
      R = R `;`  Δ_(W) -> (R.+ `;`  Δ_(W) = R.+).
  Proof.
    by move => R H1;rewrite {2}H1 [RHS]Delta_clos_trans_ends -H1. 
  Qed.

  Lemma L14_E38c3 : forall (R: relation T), 
      R =  Δ_(W) `;` R ->  Δ_(W) `;` R.+ = R.+.
  Proof.
    by move => R H1;rewrite {2}H1 [RHS]Delta_clos_trans_starts -H1. 
  Qed.
  
  Lemma L14_E38c4 : forall (R: relation T), 
      R = R `;`  Δ_(W) -> R =  Δ_(W) `;` R -> ( Δ_(W) `|` R.+) `;` ( Δ_(W) `|` R) = ( Δ_(W) `|` R.+).
  Proof. 
    move => R H1 H2.
    rewrite composeDr !composeDl DeltaE_compose_same -H2.
    rewrite L14_E38c2 //. 
    rewrite -setUA [in (R `|` _)]setUA [in (R `|` _)]setUC.
    rewrite -[in (R .+ `|` R `|` R .+ `;` R)]setUA.
    rewrite clos_t_decomp_rt_r. 
    by rewrite setUid.
  Qed.

  Lemma L14_E38c5 : forall (R: relation T), 
      R = R `;`  Δ_(W) -> R =  Δ_(W) `;` R -> ( Δ_(W) `|` R.+) `;` ( Δ_(W) `|` R.+) = ( Δ_(W) `|` R.+).
  Proof.
    move => R H1 H2.
    rewrite composeDr !composeDl DeltaE_compose_same.
    rewrite L14_E38c2 // L14_E38c3 //.
    by rewrite clos_t_decomp_2 -setUA setUid.
  Qed.
  
  Lemma L14_E38c : (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Cw  = Cw. 
  Proof.
    have H1: DKD `;`  Δ_(W) = DKD
      by rewrite /DKD composeA DeltaE_compose_same.
    have H2:  Δ_(W) `;` DKD = DKD
      by rewrite /DKD -composeA -composeA DeltaE_compose_same.
    rewrite L14_E38c1.
    rewrite {1}Cw_ends.
    rewrite composeA. 
    rewrite -{1}[in ( Δ_(W) `;` (( Δ_(W) `|` Kw `;`  Δ_(W)) `;` Cw))]composeA. 
    rewrite [in  Δ_(W) `;` ( Δ_(W) `|` Kw `;`  Δ_(W))]composeDl.
    rewrite DeltaE_compose_same.
    rewrite -[in  Δ_(W) `;` (Kw `;`  Δ_(W))]composeA.
    rewrite /Cw -/DKD. 
    rewrite [in (DKD .+ `|`  Δ_(W))]setUC.
    rewrite -composeA. 
    by rewrite L14_E38c4; first by rewrite L14_E38c5. 
  Qed.
  
  (* Equation (E23d) *)
  
  Lemma L14_E38d : (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Δ_(W.^c)  = Cw `;` (Bmw `|` Kw)  `;` Δ_(W.^c).
  Proof.
    rewrite L14_E38b. 
    rewrite Cw_ends.
    rewrite composeA [in( 'Δ `|` Bmw `;` Δ_(W.^c) `|` Kw) `;` Δ_(W.^c)]composeDr.
    rewrite [in ('Δ `|` Bmw `;` Δ_(W.^c)) `;` Δ_(W.^c)]composeDr.
    rewrite [in  Bmw `;` Δ_(W.^c) `;` Δ_(W.^c)]composeA DeltaE_compose_same.
    rewrite [in LHS]composeA composeDl [in ( Δ_(W) `;` _)]composeDl.
    rewrite Delta_idem_l DeltaW_Wc  DeltaC_union_ideml. 
    rewrite -[in ( Δ_(W) `;` _ `|`  Δ_(W) `;` _)]composeDl.
    rewrite -[in (_ `;` Δ_(W.^c) `|` _ `;` Δ_(W.^c))]composeDr.
    rewrite -[in LHS]composeA -Cw_ends.
    by rewrite -composeA.
  Qed.

  (* Equation (E23e) *)
  Lemma L14_E38e : Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw = Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw.
  Proof.
    have H0 : forall (R: relation T), 
        (Δ_(W.^c) `;` R `;` Cw).-1 = Cw `;` R.-1 `;` Δ_(W.^c)
        by move => R; rewrite inverse_compose  inverse_compose
                       Cw_inverse DeltaE_inverse composeA.
    have H1: inverse (Emw .* ) = (Ew .* )
      by rewrite inverse_star /Emw inverse_inverse.
    have H2 : (Emw.* `;` Ew.* ).-1 = (Emw.* `;` Ew.* )
      by rewrite -H1; apply RRm_inverse. 
    have H3 : (Bw `|` Kw).-1 = (Bmw `|` Kw)
      by rewrite inverse_union Kw_inverse.
    have H4 : (Δ_(W.^c) `;` ((Emw .* ) `;` (Ew .* )) `;` Cw).-1
              =  (Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw).-1
      by rewrite [LHS]H0 [RHS]H0 H2 H3 -[RHS]L14_E38d -composeA. 
    by apply inverse_eq in H4.
  Qed.
  
  (** * C'est maintenant le Lemme 14 *)
  Lemma  L9:
    (Emw.* `;` Ew.* ) = ('Δ `|` (Δ_(W.^c) `;` Bw) `|` (Bmw `;` Δ_(W.^c)) `|` Kw)
    /\ Cw `;` (Emw .* ) `;` (Ew .* ) = Cw `;` ('Δ `|` Bmw `;` Δ_(W.^c) `|` Kw)
    /\ (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Cw  = Cw 
    /\ (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Δ_(W.^c)  = Cw `;` (Bmw `|` Kw)  `;` Δ_(W.^c)
    /\ Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw = Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw.
  Proof.
    pose proof L14_E38a.
    pose proof L14_E38b.
    pose proof L14_E38c.
    pose proof L14_E38d.
    pose proof L14_E38e.
    by [].
  Qed.
  
End Tcs_Lemma7. 
  
