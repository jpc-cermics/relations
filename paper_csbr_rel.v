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
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel erel3 aacset paper_relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** * some relations results used in Csbr *)

Section Csbr.

  (** already in E_incl_Bw *)
  Lemma E9b1 : E `<=` Bw.
  Proof.
    by rewrite -[E]Delta_idem_r; apply: compose_inc; apply: clos_refl_trans_containsD.
  Qed.

  (* Equation (9c) *)
  Lemma E9c : Emw = E.-1 `;` Δ_(W.^c). 
  Proof.
    by rewrite /Emw /Ew inverse_compose DeltaE_inverse.
  Qed.
  
  (* Equation (9d) *)
  Lemma E9d : Bmw = (Emw.* `;` E.-1).
  Proof.
    by rewrite /Bmw /Bw /Emw /Ew inverse_compose inverse_star.
  Qed.

  Section Csbr_Lemma7. 
    (** * Lemma 7 of Csbr *)
    Lemma L7_E25a : (Emw.* `;` Ew.* ) =
                      ('Δ `|` (Δ_(W.^c) `;` Bw) `|` (Bmw `;` Δ_(W.^c)) `|` Kw).
    Proof.
      have L7_E25a1 : Ew.+ = Δ_(W.^c) `;` Bw                            
        by rewrite /Bw -composeA -/Ew r_clos_rt_clos_t.
      have L7_E25a2 : Emw.+ = Bmw `;` Δ_(W.^c)
        by rewrite -inverse_clos_t L7_E25a1 inverse_compose -/Bmw DeltaE_inverse.
      by rewrite L1 !composeDr !composeDl !Delta_idem_r !Delta_idem_l -unionA -E9e;
      rewrite -L7_E25a2 -L7_E25a1.
    Qed.

    Lemma L7_E25b : Cw `;` (Emw.* ) `;` (Ew .* ) = Cw `;` ('Δ `|` (Bmw `;` Δ_(W.^c)) `|` Kw).
    Proof.
      have H1: ( Δ_(W) `;` (Δ_(W.^c) `;` Bw)) = 'Δc
        by rewrite -composeA DeltaW_Wc DeltaC_compose_absorbl.
      rewrite composeA L7_E25a {1}Cw_ends composeA !composeDl H1.
      rewrite DeltaC_compose_absorbr.
      rewrite !Delta_idem_r -Cw_ends.
      rewrite -composeA -Cw_ends.
      rewrite -{1}composeA -{1}composeA -{1}composeA -Cw_ends.
      by rewrite DeltaC_union_idemr.
    Qed.

    (* Equation (E23c) *)

    Lemma L7_E25c1 : (Cw `;` (Emw.* ) `;` (Ew.* )) `;` Cw  = Cw `;` ((Δ_(W) `|` Kw `;` Δ_(W)) `;` Cw).
    Proof.
      have H1: Δ_(W.^c) `;` Cw = 'Δc
        by rewrite Cw_starts -composeA DeltaWc_W DeltaC_compose_absorbl.
      have H2: Bmw `;` Δ_(W.^c) `;` Cw = 'Δc
        by rewrite composeA H1 DeltaC_compose_absorbr.
      have H3:  Δ_(W) `;` Cw `|` Kw `;` ( Δ_(W) `;` Cw) = ( Δ_(W) `|` Kw `;`  Δ_(W)) `;` Cw
        by rewrite -[(Kw) `;` (_ `;` _)]composeA -composeDr.
      by rewrite L7_E25b composeA composeDr composeDr H2 DeltaC_union_idemr Delta_idem_l
           {2 3}Cw_starts H3.
    Qed.

    Lemma L7_E25c2 : forall (R: relation A), 
        R = R `;`  Δ_(W) -> (R.+ `;`  Δ_(W) = R.+).
    Proof.
      by move => R H1;rewrite {2}H1 [RHS]Delta_clos_trans_ends -H1. 
    Qed.

    Lemma L7_E25c3 : forall (R: relation A), 
        R =  Δ_(W) `;` R ->  Δ_(W) `;` R.+ = R.+.
    Proof.
      by move => R H1;rewrite {2}H1 [RHS]Delta_clos_trans_starts -H1. 
    Qed.
    
    Lemma L7_E25c4 : forall (R: relation A), 
        R = R `;`  Δ_(W) -> R =  Δ_(W) `;` R -> ( Δ_(W) `|` R.+) `;` ( Δ_(W) `|` R) = ( Δ_(W) `|` R.+).
    Proof. 
      move => R H1 H2.
      rewrite composeDr !composeDl DeltaE_compose_same -H2.
      rewrite L7_E25c2 //. 
      rewrite unionA -[in (R `|` _)]unionA [in (R `|` _)]unionC.
      rewrite [in (R .+ `|` R `|` R .+ `;` R)]unionA.
      rewrite clos_t_decomp_rt_r. 
      by rewrite union_RR.
    Qed.

    Lemma L7_E25c5 : forall (R: relation A), 
        R = R `;`  Δ_(W) -> R =  Δ_(W) `;` R -> ( Δ_(W) `|` R.+) `;` ( Δ_(W) `|` R.+) = ( Δ_(W) `|` R.+).
    Proof.
      move => R H1 H2.
      rewrite composeDr !composeDl DeltaE_compose_same.
      rewrite L7_E25c2 // L7_E25c3 //.
      by rewrite clos_t_decomp_2 unionA union_RR.
    Qed.

    Lemma L7_E25c : (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Cw  = Cw. 
    Proof.
      have H1: DKD `;`  Δ_(W) = DKD
        by rewrite /DKD composeA DeltaE_compose_same.
      have H2:  Δ_(W) `;` DKD = DKD
        by rewrite /DKD -composeA -composeA DeltaE_compose_same.
      rewrite L7_E25c1.
      rewrite {1}Cw_ends.
      rewrite composeA. 
      rewrite -{1}[in ( Δ_(W) `;` (( Δ_(W) `|` Kw `;`  Δ_(W)) `;` Cw))]composeA. 
      rewrite [in  Δ_(W) `;` ( Δ_(W) `|` Kw `;`  Δ_(W))]composeDl.
      rewrite DeltaE_compose_same.
      rewrite -[in  Δ_(W) `;` (Kw `;`  Δ_(W))]composeA.
      rewrite /Cw -/DKD. 
      rewrite [in (DKD .+ `|`  Δ_(W))]unionC.
      rewrite -composeA. 
      by rewrite L7_E25c4; first by rewrite L7_E25c5. 
    Qed.
  
    (* Equation (E23d) *)
  
    Lemma L7_E25d : (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Δ_(W.^c)  = Cw `;` (Bmw `|` Kw)  `;` Δ_(W.^c).
    Proof.
      rewrite L7_E25b. 
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
    Lemma L7_E25e : Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw = Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw.
    Proof.
      have H0 : forall (R: relation A), 
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
        by rewrite [LHS]H0 [RHS]H0 H2 H3 -[RHS]L7_E25d -composeA. 
      by apply inverse_eq in H4.
    Qed.

    Lemma  L7:
      (Emw.* `;` Ew.* ) = ('Δ `|` (Δ_(W.^c) `;` Bw) `|` (Bmw `;` Δ_(W.^c)) `|` Kw)
      /\ Cw `;` (Emw .* ) `;` (Ew .* ) = Cw `;` ('Δ `|` Bmw `;` Δ_(W.^c) `|` Kw)
      /\ (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Cw  = Cw 
      /\ (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Δ_(W.^c)  = Cw `;` (Bmw `|` Kw)  `;` Δ_(W.^c)
      /\ Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw = Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw.
    Proof.
      pose proof L7_E25a.
      pose proof L7_E25b.
      pose proof L7_E25c.
      pose proof L7_E25d.
      pose proof L7_E25e.
      by [].
    Qed.
    
  End Csbr_Lemma7. 

  Section Csbr_Lemma8.
    (** `;` Lemma 8 of Csbr *)

    Lemma L8_E29a :  Aw_s = 'Δ `|` Aw_sp `|`  Aw_sm.
    Proof.
      rewrite /Aw_s [Bmw `|` Kw]unionC  composeDl.
      rewrite unionA unionA [Bmw `|` (_)]unionC unionA.
      rewrite -[Bw `|` _]unionA -[Bw `|` _]unionA.
      rewrite -[Bw `|` Kw `|` _]unionA.
      rewrite -/Aw_sp. 
      rewrite [Aw_sp `|` (Bw `|` Kw) `;` Cw_s `;` Bmw `|` Bmw]unionA.
      rewrite [ (Bw `|` Kw) `;` Cw_s `;` Bmw `|` Bmw]unionC.
      by rewrite -/Aw_sm unionA.
    Qed.
    
    Lemma L8_E29b :  (Aw_sm `;` Δ_(W.^c) `;` E) `<=`  Aw_sp.
    Proof.
      rewrite /Aw_sm.
      have H: Bmw = 'Δ `;` Bmw by rewrite Delta_idem_l.
      set R1 := (Bw `|` Kw) `;` Cw_s .
      rewrite {1}[Bmw]H -composeDr. 
      set R2 := ('Δ `|` R1) `;` Bmw `;` Δ_( W .^c).
      have H1: (R2 `;` E) `<=` (R2 `;` Bw) by  apply: compose_inc;apply: E9b1.
      suff H2: (R2 `;` Bw) `<=` Aw_sp by apply: subset_trans H1 H2.
      rewrite /R2 composeA composeA.
      rewrite -[(Bmw `;` (_ `;` Bw))]composeA -/Kw composeDr. 
      rewrite Delta_idem_l /R1 /Aw_sp [Bw `|` Kw `|` _]unionA.
      by apply: union_containsr.
    Qed.
    
    Lemma L8_E29c :  (Aw_sp `;` Δ_(W_s) `;` Em) `<=`  Aw_sm.
    Proof.
      have E27c1: E.-1 `<=` Bmw
        by rewrite E9d -{1}[E.-1]Delta_idem_l;apply: composer_inc;
        apply: clos_refl_trans_containsD.
      have E27c2: Δ_(W_s) `<=` Cw_s by rewrite /Cw_s;apply: union_containsr.
      have H1: (Δ_(W_s) `;` E.-1) `<=` (Cw_s `;` E.-1) by apply composer_inc; apply: E27c2.
      have H2: (Cw_s `;` E.-1) `<=` (Cw_s `;` Bmw) by apply compose_inc; apply: E27c1.
      have E27c3: (Δ_(W_s) `;` E.-1) `<=` (Cw_s `;` Bmw) by apply: subset_trans H1 H2.
      have E27c4: ((Bw `|` Kw) `;` Δ_(W_s) `;` E.-1) `<=` ((Bw `|` Kw) `;` (Cw_s) `;` Bmw)
        by rewrite [_ `;` _ `;` E.-1]composeA [_ `;` _ `;` Bmw]composeA;
        apply: compose_inc; apply: E27c3.
      have H3: ((Bw `|` Kw) `;` Cw_s `;` Bmw) `<=`  Aw_sm 
        by rewrite /Aw_sm; apply: union_containsr.
      have H4: ((Bw `|` Kw) `;` Δ_( W_s) `;` Em) `<=` Aw_sm 
        by apply: subset_trans E27c4 H3.
      have E27c5: Cw_s `;` Δ_(W_s) = Cw_s
        by rewrite {1}/Cw_s composeDr -Delta_clos_trans_ends DeltaE_inv -/Cw_s.
      have E27c6: forall (R S: relation A), (S `;` R = R) -> ((R.+ `|` S) `;` R) = (R.+)
          by move => R S H; rewrite composeDr H unionC clos_t_decomp_rt_r.
      have E27c7: Cw_s `;` Kw `;` Δ_(W_s) = (Δ_( W_s) `;` Kw `;` Δ_( W_s)) .+ 
        by rewrite -{1}E27c5 {1}/Cw_s composeA composeA 
           -[Δ_( W_s) `;` (Kw `;` Δ_( W_s))]composeA;
        apply: E27c6;rewrite -composeA -composeA {1}DeltaE_inv.
      have E27c8: (Cw_s `;` Kw `;` Δ_(W_s)) `<=` Cw_s 
        by rewrite E27c7 /Cw_s;apply: union_containsl.
      have H1': (((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s)) `;` E.-1) `<=` (((Bw `|` Kw) `;` Cw_s) `;` E.-1)
        by apply: composer_inc;rewrite composeA composeA;apply: compose_inc;
        rewrite -composeA;apply E27c8.
      have H2': (((Bw `|` Kw) `;` Cw_s) `;` E.-1) `<=` (((Bw `|` Kw) `;` Cw_s) `;` Bmw)
        by apply: compose_inc; apply: E27c1.
      have E27c9: ((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s) `;` E.-1) `<=` ((Bw `|` Kw) `;` Cw_s `;` Bmw)
        by apply: subset_trans H1' H2'.
      have H5: ((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s) `;` Em) `<=` Aw_sm
        by apply:  subset_trans E27c9 H3.
      by rewrite /Aw_sp composeDr composeDr;apply: union_inc_b H4 H5.
    Qed.
    
    Lemma L8: 
      Aw_s = 'Δ `|` Aw_sp `|`  Aw_sm
      /\  ((Aw_sm `;` Δ_(W.^c) `;` E) `<=`  Aw_sp)
      /\  ((Aw_sp `;` Δ_(W_s) `;` Em) `<=`  Aw_sm).
    Proof.
      by split;[apply L8_E29a | split;[apply L8_E29b | apply L8_E29c]].
    Qed.

  End Csbr_Lemma8.

  Section Csbr_Lemma9.
    (** `;` Lemma 9 of Csbr *)
    Lemma L9_E31: forall (R: relation A) (Y: set A),
        (Δ_(Y.^c) `;` R).*#Y = R.*#Y.
    Proof.
      by apply Fset_rt.
    Qed.
    
    Lemma L9_E33: forall (R:relation A) (X: set A), Δ_(R # X) `<=` (R `;` Δ_(X) `;` R.-1).
    Proof.
      rewrite /DeltaE /Fset /mkset.
      move => R X [x y]. 
      move => [[z [H1 H2]] /= <-]. 
      by exists z;split;[exists z |].
    Qed.

    Lemma E32f : ((Ew .* ) `;` Δ_(W_s) `;` (Emw .* )) `<=` ((Ew .* ) `;` Δ_(W) `;` (Emw .* )).
    Proof.
      have E32a: (Fset (Δ_(W.^c) `;` E).* W) = Fset E.* W by apply: L9_E31.
      have E32b: Δ_(Fset Ew.*  W) = Δ_(Fset E.* W) by rewrite /Ew E32a.
      have E32c : Δ_(W_s) `<=` ((Ew .* ) `;` Δ_(W) `;` (Emw .* )) 
        by rewrite /W_s -E32b Emw_1; apply: L9_E33.
      have H1:  (Δ_(W_s) `;` (Emw .* )) `<=` ((Ew .* ) `;` Δ_(W) `;` (Emw .* ) `;` (Emw .* ))
        by apply: composer_inc E32c.
      have E32e :  (Δ_(W_s) `;` (Emw .* )) `<=` ((Ew .* ) `;` Δ_(W) `;` (Emw .* ))
        by rewrite composeA  compose_rt_rt in H1.
      
      rewrite composeA -{2}[Ew.*]compose_rt_rt.
      rewrite [(Ew .* `;` Ew .* `;` _ `;` _)]composeA.
      rewrite [(Ew .* `;` Ew .* `;` _ )]composeA.
      apply: compose_inc.
      by rewrite -[(Ew .* `;` _ )]composeA.
    Qed.

    Lemma E32h : (Ew .* `;` Δ_( W) `;` Emw .* ) `<=` (Ew .* `;` Δ_( W_s) `;` Emw .* ).
    Proof.
      have E32g : Δ_( W) `<=` Δ_( W_s)
        by move => [x y] [H1 H2]; rewrite /W_s /Fset /DeltaE /mkset /=;
                  split;[exists x; split;[ apply: rt_refl |] | ].
      by apply: composer_inc; apply: compose_inc; apply: E32g.
    Qed.

    Lemma E32: ((Ew .* ) `;` Δ_(W) `;` (Emw .* )) = ((Ew .* ) `;` Δ_(W_s) `;` (Emw .* )).
    Proof.
      by rewrite eqEsubset; split;[apply: E32h | apply: E32f].
    Qed.

    Section Key_Lemma_W_s.
      
      Lemma Test5: forall (n: nat) (S R T: relation A) (X: set A),
          (T `;` (iter ( Δ_(X) `;` S `;` R `;` T `;` Δ_(X)) (n.+1))) `;` S =
            ((iter (T `;` Δ_(X) `;` S `;` R) (n.+1)) `;` (T `;` Δ_(X) `;` S)).
      Proof.
        move => n S R T X.
        have Test4: (T `;` (iter ( Δ_(X) `;` S `;` R `;` T `;` Δ_(X)) (n.+1))) = 
                      ((iter (T `;` Δ_(X) `;` S `;` R) (n.+1)) `;` T `;` Δ_(X)).
        elim: n => [| n' H]; 
                  first by rewrite /iter 
                             -!['Δ `;` (_)]composeA Delta_idem_l Delta_idem_l -!composeA.
        rewrite /iter -/iter; rewrite /iter -/iter in H.
        rewrite -composeA H composeA. 
        rewrite -[Δ_( X) `;` (Δ_( X) `;` S `;` R `;` T `;` Δ_( X))]composeA.
        rewrite -[Δ_( X) `;` (Δ_( X) `;` S `;` R `;` T)]composeA.
        rewrite -[Δ_( X) `;` (Δ_( X) `;` S `;` R)]composeA.
        rewrite -[Δ_( X) `;` (Δ_( X) `;` S)]composeA.
        by rewrite DeltaE_inv -!composeA.
        (* *)
        by rewrite Test4 -[_ `;` (T `;` Δ_( X) `;` S)]composeA -[_ `;` (T `;` Δ_( X))]composeA.
      Qed.
      
      Lemma Test6: forall (n: nat) (S R T: relation A) (X Y: set A),
          T `;` Δ_(X) `;` S = T `;` Δ_(Y) `;` S 
          ->  ((T `;` (iter ( Δ_(X) `;` S `;` R `;` T `;` Δ_(X)) (n.+1))) `;` S)
             =
               (T `;` (iter ( Δ_(Y) `;` S `;` R `;` T `;` Δ_(Y)) (n.+1))) `;` S.
      Proof.
        move => n S R T X Y H.
        have H1: ((T `;` (iter ( Δ_(X) `;` S `;` R `;` T `;` Δ_(X)) (n.+1))) `;` S)
                 =
                   ((iter (T `;` Δ_(X) `;` S `;` R) (n.+1)) `;` (T `;` Δ_(X) `;` S)).
        by apply: Test5.
        by rewrite H in H1;rewrite -Test5 in H1.
      Qed.

      Lemma Test7: forall (S R T: relation A) (X Y: set A),
          T `;` Δ_(X) `;` S = T `;` Δ_(Y) `;` S 
          ->  (T `;` ((Δ_(X) `;` S `;` R `;` T `;` Δ_(X)).+) `;` S
              = T `;` (Δ_(Y) `;` S `;` R `;` T `;` Δ_(Y)).+ `;` S ).
      Proof.
        by move => S R T X Y H;apply: clos_trans_eq; move => n; apply: Test6.
      Qed.

    End Key_Lemma_W_s.

    Lemma BwKw_ends : Bw `|` Kw = (Bw `|` Kw) `;` Ew.* .
    Proof.
      by rewrite composeDr -Bw_ends -Kw_ends.
    Qed.
    
    Lemma BmKw_starts : Bmw `|` Kw = (Emw.* `;` (Bmw `|` Kw )).
    Proof.
      by rewrite composeDl -Bmw_starts -Kw_starts.
    Qed.
    
    Lemma L9: Aw = Aw_s. 
    Proof.
      have L9_1: (Ew.* `;` ((Δ_(W) `;` Kw `;` Δ_(W)).+ ) `;` Emw.* )
                 = (Ew.* `;` ((Δ_(W_s) `;` Kw `;` Δ_(W_s)).+ ) `;` Emw.* )
        by rewrite /Cw /DKD /Cw_s Kw_starts_ends -![(Δ_(W) `;` _)]composeA
             -![(Δ_(W_s) `;` _)]composeA; apply Test7; rewrite E32.
      have L9_2: (Ew.* `;` Cw `;` Emw.* = Ew.* `;` Cw_s `;` Emw.* )
        by rewrite /Cw /DKD /Cw_s composeDl composeDr
             [in RHS]composeDl [in RHS]composeDr E32 L9_1.
      rewrite /Aw /Aw_s /Dw BmKw_starts BwKw_ends.
      rewrite [(Bw `|` Kw) `;` Ew.* `;` _]composeA.
      rewrite -[(Ew.* `;` _)]composeA.
      rewrite -[(Ew.* `;` Cw `;`  _)]composeA. 
      rewrite L9_2.
      rewrite -[in X in 'Δ `|` Bw `|` Bmw `|` Kw `|` X]composeA.
      rewrite -[in X in 'Δ `|` Bw `|` Bmw `|` Kw `|` X]composeA.
      rewrite [in X in 'Δ `|` Bw `|` Bmw `|` Kw `|` X]composeA.
      by rewrite -[(Bw `|` Kw) `;` (Ew.* `;` Cw_s)]composeA.
    Qed.

  End Csbr_Lemma9.

End Csbr. 
  
