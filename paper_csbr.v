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

From AAC_tactics Require Import AAC.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  seq1 rel  aacset paper_relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** ****************************************************************
 * Conditional Separation as a Binary Relation 
 *   Jean-Philippe Chancelier, Michel De Lara, Benjamin Heymann 
 ******************************************************************)

(** * some relations results used in Csbr *)

Section Csbr.
  
  Section Appendix_D_L16. 

    Lemma D_L16_E42a :  Aw_s = 'Δ `|` Aw_sp `|`  Aw_sm.
    Proof.
      rewrite /Aw_s [Bmw `|` Kw]setUC  composeDl.
      rewrite -setUA -setUA [Bmw `|` (_)]setUC -setUA.
      rewrite [Bw `|` _]setUA [Bw `|` _]setUA.
      rewrite [Bw `|` Kw `|` _]setUA.
      rewrite -/Aw_sp. 
      rewrite -[Aw_sp `|` (Bw `|` Kw) `;` Cw_s `;` Bmw `|` Bmw]setUA.
      rewrite [ (Bw `|` Kw) `;` Cw_s `;` Bmw `|` Bmw]setUC.
      by rewrite -/Aw_sm -setUA.
    Qed.
    
    Lemma D_L16_E42b :  (Aw_sm `;` Δ_(W.^c) `;` E) `<=`  Aw_sp.
    Proof.
      rewrite /Aw_sm.
      have H: Bmw = 'Δ `;` Bmw by rewrite Delta_idem_l.
      set R1 := (Bw `|` Kw) `;` Cw_s .
      rewrite {1}[Bmw]H -composeDr. 
      set R2 := ('Δ `|` R1) `;` Bmw `;` Δ_( W .^c).
      have H1: (R2 `;` E) `<=` (R2 `;` Bw) by  apply: composeSl;apply: E9b1.
      suff H2: (R2 `;` Bw) `<=` Aw_sp by apply: subset_trans H1 H2.
      rewrite /R2 composeA composeA.
      rewrite -[(Bmw `;` (_ `;` Bw))]composeA -/Kw composeDr. 
      rewrite Delta_idem_l /R1 /Aw_sp -[Bw `|` Kw `|` _]setUA.
      by apply: subsetUr.
    Qed.
    
    Lemma D_L16_E42c :  (Aw_sp `;` Δ_(W_s) `;` Em) `<=`  Aw_sm.
    Proof.
      have E21c1: E^-1 `<=` Bmw
        by rewrite E9d -{1}[E^-1]Delta_idem_l;apply: composeSr;
        apply: RTclos_containsD.
      have E21c2: Δ_(W_s) `<=` Cw_s by rewrite /Cw_s;apply: subsetUr.
      have H1: (Δ_(W_s) `;` E^-1) `<=` (Cw_s `;` E^-1) by apply composeSr; apply: E21c2.
      have H2: (Cw_s `;` E^-1) `<=` (Cw_s `;` Bmw) by apply composeSl; apply: E21c1.
      have E21c3: (Δ_(W_s) `;` E^-1) `<=` (Cw_s `;` Bmw) by apply: subset_trans H1 H2.
      have E21c4: ((Bw `|` Kw) `;` Δ_(W_s) `;` E^-1) `<=` ((Bw `|` Kw) `;` (Cw_s) `;` Bmw)
        by rewrite [_ `;` _ `;` E^-1]composeA [_ `;` _ `;` Bmw]composeA;
        apply: composeSl; apply: E21c3.
      have H3: ((Bw `|` Kw) `;` Cw_s `;` Bmw) `<=`  Aw_sm 
        by rewrite /Aw_sm; apply: subsetUr.
      have H4: ((Bw `|` Kw) `;` Δ_( W_s) `;` Em) `<=` Aw_sm 
        by apply: subset_trans E21c4 H3.
      have E21c5: Cw_s `;` Δ_(W_s) = Cw_s
        by rewrite {1}/Cw_s composeDr -Delta_clos_trans_ends DsetK -/Cw_s.
      have E21c6: forall (R S: relation T), (S `;` R = R) -> ((R.+ `|` S) `;` R) = (R.+)
          by move => R S H; rewrite composeDr H setUC clos_t_decomp_rt_r.
      have E21c7: Cw_s `;` Kw `;` Δ_(W_s) = (Δ_( W_s) `;` Kw `;` Δ_( W_s)) .+ 
        by rewrite -{1}E21c5 {1}/Cw_s composeA composeA 
           -[Δ_( W_s) `;` (Kw `;` Δ_( W_s))]composeA;
        apply: E21c6;rewrite -composeA -composeA {1}DsetK.
      have E21c8: (Cw_s `;` Kw `;` Δ_(W_s)) `<=` Cw_s 
        by rewrite E21c7 /Cw_s;apply: subsetUl.
      have H1': (((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s)) `;` E^-1) `<=` (((Bw `|` Kw) `;` Cw_s) `;` E^-1)
        by apply: composeSr;rewrite composeA composeA;apply: composeSl;
        rewrite -composeA;apply E21c8.
      have H2': (((Bw `|` Kw) `;` Cw_s) `;` E^-1) `<=` (((Bw `|` Kw) `;` Cw_s) `;` Bmw)
        by apply: composeSl; apply: E21c1.
      have E21c9: ((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s) `;` E^-1) `<=` ((Bw `|` Kw) `;` Cw_s `;` Bmw)
        by apply: subset_trans H1' H2'.
      have H5: ((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s) `;` Em) `<=` Aw_sm
        by apply:  subset_trans E21c9 H3.
      by rewrite /Aw_sp composeDr composeDr;apply: union_inc_b H4 H5.
    Qed.
    
  End Appendix_D_L16. 
    
  Section Appendix_B_L7.
    
    Lemma B_L7_E25: forall (R: relation T) (Y: set T),
          (Δ_(Y.^c) `;` R).*#Y = R.*#Y. 
    Proof.
      by move => R Y;rewrite Fset_rt.
    Qed.
    
    Lemma B_L7_E27: forall (R:relation T) (X: set T), Δ_(R # X) `<=` (R `;` Δ_(X) `;` R^-1).
    Proof.
      rewrite /Delta /Fset /mkset.
      move => R X [x y]. 
      move => [[z [H1 H2]] /= <-]. 
      by exists z;split;[exists z |].
    Qed.
    
    Lemma B_L7_E28: ((Ew .* ) `;` Δ_(W) `;` (Emw .* )) = ((Ew .* ) `;` Δ_(W_s) `;` (Emw .* )).
    Proof.
      have B_L7_E28a: (Fset (Δ_(W.^c) `;` E).* W) = Fset E.* W by apply: B_L7_E25.
      have B_L7_E28b: Δ_(Fset Ew.*  W) = Δ_(Fset E.* W) by rewrite /Ew B_L7_E28a.
      have B_L7_E28c : Δ_(W_s) `<=` ((Ew .* ) `;` Δ_(W) `;` (Emw .* )) 
        by rewrite /W_s -B_L7_E28b Emw_1; apply: B_L7_E27.
      have H1:  (Δ_(W_s) `;` (Emw .* )) `<=` ((Ew .* ) `;` Δ_(W) `;` (Emw .* ) `;` (Emw .* ))
        by apply: composeSr B_L7_E28c.
      have B_L7_E28e :  (Δ_(W_s) `;` (Emw .* )) `<=` ((Ew .* ) `;` Δ_(W) `;` (Emw .* ))
        by rewrite composeA  compose_rt_rt in H1.
      have B_L7_E28f : ((Ew .* ) `;` Δ_(W_s) `;` (Emw .* )) `<=` ((Ew .* ) `;` Δ_(W) `;` (Emw .* ))
        by rewrite composeA -{2}[Ew.*]compose_rt_rt [(Ew .* `;` Ew .* `;` _ `;` _)]composeA
                               [(Ew .* `;` Ew .* `;` _ )]composeA; apply: composeSl;
        rewrite -[(Ew .* `;` _ )]composeA.
      have B_L7_E28g : Δ_( W) `<=` Δ_( W_s)
        by move => [x y] [H'1 H'2]; rewrite /W_s /Fset /Delta /mkset /=;
                  split;[exists x; split;[ apply: RTclosR |] | ].
      have B_L7_E28h : (Ew .* `;` Δ_( W) `;` Emw .* ) `<=` (Ew .* `;` Δ_( W_s) `;` Emw .* )
        by apply: composeSr; apply: composeSl; apply: B_L7_E28g.
      
      by rewrite eqEsubset; split;[apply: B_L7_E28h | apply: B_L7_E28f].
    Qed.
    
    Lemma B_L7: Aw = Aw_s. 
    Proof.
      have B_L7_1: (Ew.* `;` ((Δ_(W) `;` Kw `;` Δ_(W)).+ ) `;` Emw.* )
                 = (Ew.* `;` ((Δ_(W_s) `;` Kw `;` Δ_(W_s)).+ ) `;` Emw.* )
        by rewrite /Cw /DKD /Cw_s Kw_starts_ends -![(Δ_(W) `;` _)]composeA
             -![(Δ_(W_s) `;` _)]composeA; apply Ws_L3; rewrite B_L7_E28.
      have B_L7_2: (Ew.* `;` Cw `;` Emw.* = Ew.* `;` Cw_s `;` Emw.* )
        by rewrite /Cw /DKD /Cw_s composeDl composeDr
             [in RHS]composeDl [in RHS]composeDr B_L7_E28 B_L7_1.
      rewrite /Aw /Aw_s /Dw BmKw_starts BwKw_ends.
      rewrite [(Bw `|` Kw) `;` Ew.* `;` _]composeA.
      rewrite -[(Ew.* `;` _)]composeA.
      rewrite -[(Ew.* `;` Cw `;`  _)]composeA. 
      rewrite B_L7_2.
      rewrite -[in X in 'Δ `|` Bw `|` Bmw `|` Kw `|` X]composeA.
      rewrite -[in X in 'Δ `|` Bw `|` Bmw `|` Kw `|` X]composeA.
      rewrite [in X in 'Δ `|` Bw `|` Bmw `|` Kw `|` X]composeA.
      by rewrite -[(Bw `|` Kw) `;` (Ew.* `;` Cw_s)]composeA.
    Qed.

  End Appendix_B_L7.

End Csbr. 

(* begin snippet dsepnota:: no-out *)  
Notation "( x [⊥d] y | W )" := (D_separated W E x y).
(* end snippet dsepnota *)

(** * some Lemmas for the paths part *)

Section Bw_implies_active_path.
  
  (** * csbr: Lemma 10 *)
  Lemma C_L10: forall (x y: T),
      Bw (x,y) -> (exists (p: seq T),
                   Active_path W E (Lifto (x::(rcons p y)) P) x y
                   /\ p [\in] (Ew.+)#_(y)).
  Proof.
    rewrite /Bw -DuT_eq_Tstar /mkset .
    move => x y [x1 [/= H1 [/DeltaP <- | H2]]];first by (exists [::]).
    pose proof (clos_t_to_paths_l H2) as [p [H3 [H4 H5]]].
    exists (x1::p);split. 
    apply Deployment_to_Active_path.
    split. by []. 
    rewrite /R_o allL_c H4 andbT. by apply mem_set.
    by [].
  Qed.
  
  (** simplified version for right composition *)
  Lemma C_L10_1: forall (x y: T),
      Bw (x,y) -> exists (p : seq (T*T*O)) (y': T),
        Active_path W E (rcons p (y',y,P)) x y /\ Oedge E (y',y,P).
  Proof.
    move => x y H1.
    pose proof C_L10 H1 as [p [H2 _]].
    rewrite -rcons_cons Lifto_rcc in H2.
    pose proof Active_path_rc_hto H2 as [_ [_ [H5 _]]].
    by exists (Lifto (x :: p) P), (last x p).
  Qed.
  
  Lemma C_L10_2: forall (x y: T),
      (Bw (x, y)) /\ W.^c x -> (exists (p: seq T),
                                Active_path W E (Lifto (x::(rcons p y)) P) x y
                                /\ (x::p) [\in] (Ew.+)#_(y)).
  Proof.
    move => x y [H1 H3]. 
    move: (H1) => [x1 [H1' H2]].
    pose proof C_L10 H1 as [p [H4 H5]].
    have H6: Ew.+ (x, y) by rewrite -r_clos_rt_clos_t;exists x1;split;[exists x;split | ].
    by exists p;rewrite allset_cons;split;[ | split;[exists y|]].
  Qed.

End Bw_implies_active_path.

Section Bmw_implies_active_path.

  (** * Lemma 11 *)
  Lemma C_L11: forall (x y: T),
      Bmw (x, y) -> (exists (p: seq T), Active_path W E (Lifto (x::(rcons p y)) N) x y
                               /\ p [\in] (Ew.+)#_(x)).
  Proof.
    rewrite /Bmw /inverse /Bw -DuT_eq_Tstar.
    move => x y [x1 [/= H1 [/DeltaP <- | H2]]];first by (exists [::]).
    pose proof (clos_t_to_paths_l H2) as [p [H3 [H4 H5]]].  
    apply allL_rev in H4.
    move: H3 => /allset_cons [H3 H3'].
    exists (rcons (rev p) x1); split.
    apply Deployment_to_Active_path.
    split. 
    by rewrite allset_rcons -allset_rev.
    by rewrite /R_o allL_rev rev_rcons revK inverseK allL_c;
    apply/andP; split;[apply mem_set| rewrite allL_rev].
    by rewrite allset_rev rev_rcons revK.
  Qed.
  
  (** simplified version for composition *)
  Lemma C_L11_1: forall (x y: T),
      Bmw (x, y) -> exists (p : seq (T*T*O)) (x': T),
        Active_path W E ((x,x',N)::p) x y /\ Oedge E (x,x',N).
  Proof.
    move => x y H1.
    pose proof C_L11 H1 as [p [H2 _]].
    rewrite Lifto_crc in H2.
    pose proof Active_path_c_hto H2 as [_ [_ [H5 _]]].
    by exists (Lifto (rcons p y) N), (head y p).
  Qed.
  
  Lemma C_L11_2: forall (x y: T),
      Bmw (x, y) /\ W.^c y -> 
      (exists (p: seq T), Active_path W E (Lifto (x::(rcons p y)) N) x y
                     /\ (rcons p y) [\in] (Ew.+)#_(x)).
  Proof.
    move => x y [H1 H3]. 
    move: (H1) => [x1 [H1' H2]].
    pose proof C_L11 H1 as [p [H4 H5]].
    have H6: Ew.+ (y, x) by rewrite -r_clos_rt_clos_t;exists x1;split;[exists y;split | ].
    by exists p;rewrite allset_rcons; split;[ | split;[|exists x]].
  Qed.
  
End Bmw_implies_active_path.

Section Kw_implies_active_path.

  (** * Lemma 12 *)  
  Lemma C_L12: forall (x y: T),
      Kw (x, y) -> (exists (p q: seq T),exists t,
                      Active_path W E 
                        ((Lifto (x::(rcons p t)) N)++(Lifto (t::(rcons q y)) P )) x y
                      /\ (rcons p t) [\in] (Ew.+)#_(x)
                      /\ (t::q) [\in] (Ew.+)#_(y)).
  Proof.
    move => x y [z [ [t [H2 [/= H3 <-]]] /= H4]]. 
    pose proof (C_L11_2 (conj H2 H3)) as [p [H5 H6]].
    pose proof (C_L10_2 (conj H4 H3)) as [q [H7 H8]].
    pose proof (Lifto_rcc p N x t) as H9.
    pose proof (Lifto_crc q P t y) as H10.
    have H13: Active_path W E (rcons (Lifto (x :: p) N) (last x p, t, N))
                x t by rewrite -H9.
    have H14: Active_path W E ((t, head y q, P):: Lifto (rcons q y) P) 
                t y by rewrite -H10.
    pose proof Active_path_rc_hto H13 as [_ [_ [H15 _]]].
    pose proof Active_path_c_hto H14 as [_ [_ [H16 _]]].
    exists p,q,t;split; last by [].
    apply Active_path_cat' with t;split; last by [].
    by exists (Lifto (x :: p) N),(Lifto (rcons q y) P),(last x p, t, N),(t, head y q, P). 
  Qed.
  
  Lemma C_L12_1: forall (x y: T),
      Kw (x,y) ->  exists (p : seq (T*T*O)) (x' y': T),
        Active_path W E ((x,x',N)::(rcons p (y',y,P))) x y
        /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof.
    move => x y H1.
    pose proof C_L12 H1 as [p [q [t [H2 _]]]].
    pose proof @Lift_o_start_end T p q x y t as [x' [y' [r H3]]].
    rewrite H3 in H2. clear H3.
    pose proof Active_path_crc_a H2 as H3. 
    move: H3; rewrite ActiveOe_iff => [[[H3 _] [_ [H4 _]]]].
    by exists r, x', y'.
  Qed.

End Kw_implies_active_path.

Section Cw_s_implies_active_path.
  (* we do not use Cw_s but use the fact that 
   * Cw_s := (DKD_s.+) + Δ_(W_s) 
   * and we consider (DKD_s.+) and  Δ_(W_s) separately
   *)
  (** * Lemma 13 *)

  Lemma C_L13_I1: forall (x y: T),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s))
      in R (x, y)
         -> exists (p q: seq (T*T*O)), exists (x' y': T),
          Active_path W E q x y
          /\ q = (x,x',N)::(rcons p (y',y,P)) /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof. 
    move => x y' R [z [[xx1 [[H1 /= <-] H2]] [H3 /= <-]]].
    pose proof C_L12 H2 as [p1 [q1 [t1 [H6 [H7 H8]]]]].
    pose proof (Lift_o_start_end p1 q1 x z t1) as [x1 [z1 [r1 H12]]].
    rewrite H12 in H6.
    pose proof Active_path_crc_a H6 as H14. 
    move: H14; rewrite ActiveOe_iff => [[[H14' _] [_ [H14 _]]]].
    by exists r1, ((x, x1, N) :: rcons r1 (z1, z, P)), x1, z1.
  Qed.
  
  Lemma C_L13_In: forall (n: nat) (x y: T),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s))^(n.+1) 
      in R (x, y)
         -> exists (p q: seq (T*T*O)), exists (x' y': T),
          Active_path W E q x y
          /\ q = (x,x',N)::(rcons p (y',y,P)) /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof. 
    elim. 
    - by rewrite iter1_id; apply C_L13_I1.
    - move => n Hn x y.
      rewrite -addn1 iter_compose.
      move => R [z [H1 H5]].
      move: H1 => /Hn [r1 [p [x1 [z1 [H1 [H2 [H3 H4]]]]]]].
      rewrite iter1_id in H5.
      have H5': W_s z by move: H5 => [z' [[z'' [[H'1 _] _]] _]].
      move: H5 => /C_L13_I1 [r2 [q [z2 [y2 [H5 [H6 [H7 H8]]]]]]].
      exists ((rcons r1 (z1,z,P)) ++ (z,z2,N)::r2),(p ++ q), x1, y2.
      split. 
      by apply Active_path_cat' with z;
      split;[exists ((x, x1, N) :: r1), (rcons r2 (y2, y, P)), (z1, z, P), (z, z2, N) | ].
      by split;[rewrite H2 H6 !rcons_cat rcons_cons | split].
  Qed.
  
  Lemma C_L13: forall (x y: T),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s)).+
      in R (x, y)
         -> exists (p q: seq (T*T*O)), exists (x' y': T),
          Active_path W E q x y
          /\ q = (x,x',N)::(rcons p (y',y,P)) /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof.
    move => x y H1 H2.
    pose proof clos_t_iterk H2 as [n H3].
    by apply C_L13_In with n.
  Qed.

  (* XXX a mettre ailleurs *)
  Lemma C_L13_2: forall (x y: T),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s)).+
      in R (x, y) ->  W_s x /\ W_s y.
  Proof.
    move => x y H1;rewrite /H1 => H2.
    move: (H2);rewrite Delta_clos_trans_ends => [[y' [_ [H3 /= <-]]]].
    by move: H2;rewrite composeA Delta_clos_trans_starts => [[z' [[H2 _] _]]].
  Qed.
  
End Cw_s_implies_active_path.

Section Dw_path.

  (** * Lemma 14 *)
  Lemma C_L14_1: forall (x y: T),
      let R:=(Bw `|` Kw) in R (x, y) -> exists (p : seq (T*T*O)) (y': T),
          Active_path W E (rcons p (y',y,P)) x y /\ Oedge E (y',y,P).
  Proof.
    move => x y H1 [H2 | H2].
    by apply C_L10_1.
    pose proof C_L12_1 H2 as [p [x' [y' [H3 [_ H5]]]]].
    exists ((x,x',N)::p), y'.
    by rewrite rcons_cons.
  Qed.

  Lemma C_L14_2: forall (x y: T),
      let R:=(Bmw `|` Kw) in R (x,y) -> exists (p : seq (T*T*O)) (x': T),
          Active_path W E ((x,x',N)::p) x y /\ Oedge E (x,x',N).
  Proof.
    move => x y H1 [H2 | H2].
    by apply C_L11_1.
    pose proof C_L12_1 H2 as [p [x' [y' [H3 [H4 _]]]]].
    by exists (rcons p (y',y,P)), x'.
  Qed.
  
  Lemma C_L14: forall (x y: T),
      let R:= ((Bw `|` Kw)`;`Cw_s`;`(Bmw `|` Kw))
      in R (x, y)
         -> exists (p : seq (T*T*O)), Active_path W E p x y.
  Proof.
    move => x y H2; rewrite /H2 => [[z [[t [H3 H4]] H5]]].
    move: H4;rewrite /Cw_s; move => [H4 | H4].
    + rewrite /DKD_s in H4.
      pose proof C_L14_1 H3 as [p1 [y' [H6 Ho1]]].
      pose proof C_L13 H4 as [p2 [p3 [t' [z' [H7 [H8 [Ho2 Ho3]]]]]]].
      pose proof C_L14_2 H5 as [p4 [z'' [H9 Ho4]]].
      pose proof C_L13_2 H4 as [H10 H11].
      have H12: ActiveOe' W E ((y', t, P), (t, t', N)) by [].
      have H13: ActiveOe' W E ((z', z, P),(z, z'', N)) by [].
      have H14: Active_path W E
                  (rcons p1 (y', t, P) ++ (t, t', N)::(rcons p2 (z', z, P)))
                  x z
        by apply Active_path_cat with t;rewrite -H8.
      exists ((rcons p1 (y', t, P) ++ (t, t', N) :: rcons p2 (z', z, P)) ++ ((z, z'', N) :: p4)).
      rewrite -rcons_cons -rcons_cat.
      apply Active_path_cat with z.
      rewrite rcons_cat rcons_cons.
      by [].
    + move: H4 => [H1 /= H4];rewrite -H4 in H5;clear H4.
      pose proof C_L14_1 H3 as [p1 [y' [H6 Ho1]]].
      pose proof C_L14_2 H5 as [p4 [t' [H9 Ho4]]].
      have H12: ActiveOe' W E ((y', t, P), (t, t', N)) by [].
      exists ((rcons p1 (y', t, P))++ ((t, t', N) :: p4)).
      by apply Active_path_cat with t.
  Qed.

End Dw_path.

Section Aw_s_implies_active_path.

  Proposition C_P8: forall (x y: T), Aw_s (x, y) -> ~ ( x [⊥d] y | W ).
  Proof.
    move => x y H1.
    have H3: exists (p : seq (T*T*O)), Active_path W E p x y.
    move: H1 => [[[[/DeltaP -> | H2] | H2] | H2] | H2].
    (* explore the five cases *)
    by (exists [::]).
    by pose proof C_L10 H2 as [p [H3 H4]];(exists (Lifto (x :: rcons p y) P)).
    by pose proof C_L11 H2 as [p [H3 H4]];(exists (Lifto (x :: rcons p y) N)).
    by pose proof C_L12 H2 as  [p [t [H3 [H4 [H5 H6]]]]];
      (exists (Lifto (x :: rcons p H3) N ++ Lifto (H3 :: rcons t y) P)).
    by pose proof C_L14 H2.
    by [].
  Qed.
  
End Aw_s_implies_active_path.

Section Active_path_implies_Aw_s.
  
  (** * From active paths to Active relation *)
  
  Lemma D_L17_1: forall (o1 o2:O) (x y t: T), 
      Active_path W E [::(x,t,o1);(t,y,o2)] x y
      -> ( ((let R:= E^-1 `;` Δ_(W.^c) `;` E in R (x, y))
            \/ (let R:= E `;` Δ_(W.^c) `;` E in R (x, y)))
           /\ o2 = P) 
         \/ 
           ( ((let R:= E `;` Δ_(W_s) `;` E^-1 in R (x, y))
              \/ (let R:= E^-1 `;` Δ_(W.^c) `;` E^-1 in R (x, y)))
             /\ o2 = N).
  Proof.
    move => o1 o2 x y t. 
    elim: o2 => [|] [H1 [H2 H3]].
    - rewrite ActiveOe_iff in H3.
      elim: o1 H1 H3 => [|] _ /= /allL0' [/= H5 [H6 [_ H8]]].  
      by left;split;[right; exists t;split;[exists t| ] | ].
      by left;split;[left; exists t;split;[exists t| ] | ].
    - rewrite ActiveOe_iff in H3.
      elim: o1 H1 H3 => [|] _ /= /allL0' [/= H5 [H6 [_ H8]]]. 
      by right;split;[left; exists t;split;[exists t| ] | ].
      by right;split;[right; exists t;split;[exists t| ] | ].
  Qed.
  
  Lemma D_L17: forall (o1 o2:O) (x y t: T), 
      Active_path W E [::(x,t,o1);(t,y,o2)] x y
      -> ( Aw_sp (x, y) /\ o2 = P) \/ ( Aw_sm (x, y) /\ o2 = N).
  Proof.
    move => o1 o2 x y t H1.
    pose proof D_L17_1 H1 as [[H2 H3 ] |[H2 H3]].
    by left;move: H2 => [H2 | H2];[split;[apply Awsp_L1|] |split;[apply Awsp_L2|]].
    by right;move: H2 => [H2 | H2];[split;[apply Awsm_L1|] |split;[apply Awsm_L2|]].
  Qed.
  
  Lemma D_L18: forall (n: nat) (p : seq (T*T*O)) (x y: T), 
      size (p) = n.+2 
      -> Active_path W E p x y
      -> exists (q: seq (T*T*O)) (o: O) (y': T),
          p = rcons q (y',y,o) /\ (( Aw_sp (x, y) /\ o = P) \/ ( Aw_sm (x, y) /\ o = N)).
  Proof.
    elim. 
    - move => p x y H1 H2.
      have H3: (1 < size p) by rewrite H1.
      rewrite seq_rcrc0 in H1;move: H1 => [[[u v] o1] [[[z t] o2] H4]].
      rewrite H4 in H2.
      pose proof Active_path_cc_ht H2 as [H5 H6].
      rewrite /last /= in H5 H6.
      rewrite H5 H6.
      pose proof Active_path_cc_a H2 as H7. 
      move: H7; rewrite ActiveOe_iff => [[H7 [H8 [H9 H10]]]].
      rewrite /ChrelO /mkset /fst /snd in H9.
      rewrite H9 H5 H6 in H2 *.
      exists [:: (u, v, o1)],o2,z.
      split; first by [].
      pose proof D_L17 H2 as [H11 | H11].
      by left.
      by right.
    - move => n Hr p x y H1 H2.
      have H3: 1 < size p by rewrite H1. 
      pose proof seq_rcrc H3 as [q [[[u v] o1] [[[z t] o2] H4]]].
      rewrite H4 in H2.
      pose proof Active_path_rcrc_ht H2 as [H5 H6].
      rewrite H5 H6 in H2.
      rewrite Active_path_rcrc in H2.
      move: H2 => [H2 H7].
      pose proof H1 as H8.
      rewrite H4 size_rcons in H8.
      move: H8 => /eqP H8. 
      have H9: size (rcons q (u,v,o1)) == n.+2 by [].
      move: H9 => /eqP H9.
      have H10: exists (r : seq (T*T*O)) (o : O) (y' : T),
          (rcons q (u,v,o1)) = rcons r (y',v , o) 
          /\ (Aw_sp ((head (u,v,o1) q).1.1, v) /\ o = P 
              \/ Aw_sm ((head (u,v,o1) q).1.1, v) /\ o = N)
          by apply Hr.
      clear Hr.
      rewrite -H5 in H2 H10 *;clear H5.
      rewrite /= in H6;rewrite H6; clear H6 y.
      move: H10 => [r [o [y' [H11 [[H12 H13] | [H12 H13]]]]]].
      
      + move: H11 => /rcons_inj [_ _ H14];rewrite H13 in H14;clear H13.
        exists (rcons q (u, v, o1)),o2, v.
        rewrite ActiveOe_iff in H7.
        move: H7 => [/= H15 [H16 [/ChrelO_eq H17  H18]]].
        rewrite H17 in H4 *.
        split. 
        by [].
        rewrite H14 in H2 H18 H15 *.
        rewrite H17 in H15 H2 H18 H12 *.
        clear H8 H9 r H4 H17 H2 H14 y' o H1 H3 q.
        elim: o2 H16 H18 => [ H1 H2 | H1 H2].
        ++ have H3: (Aw_sp `;` Δ_(W.^c) `;` E) (x, t) by (exists z);split;[exists z | ].
           by rewrite composeA in H3;left;split;[apply AwspE |].
        ++ have H3: (Aw_sp `;` Δ_(W_s) `;` E^-1) (x, t) by (exists z);split;[exists z | ].
           by right;split;[apply D_L16_E42c|].
      + move: H11 => /rcons_inj [_ _ H14];rewrite H13 in H14;clear H13.
        exists (rcons q (u, v, o1)),o2, v.
        rewrite ActiveOe_iff in H7.
        move: H7 => [/= H15 [H16 [/ChrelO_eq H17  H18]]].
        rewrite H17 in H4 *.
        split. 
        by [].
        rewrite H14 in H2 H18 H15 *.
        rewrite H17 in H15 H2 H18 H12 *.
        clear H8 H9 r H4 H17 H2 H14 y' o H1 H3 q.
        elim: o2 H16 H18 => [ H1 H2 | H1 H2].
        ++ have H3: (Aw_sm `;` Δ_(W.^c) `;` E) (x, t) by (exists z);split;[exists z | ].
           by left;split;[apply D_L16_E42b |].
        ++ have H3: (Aw_sm `;` Δ_(W.^c) `;` E^-1) (x, t) by (exists z);split;[exists z | ].
           by right;split;[apply AwsmDE |].
  Qed.
  
  Proposition D_P15:forall (x y: T), ~ ( x [⊥d] y | W ) -> Aw_s (x, y).
  Proof.
    move => x y H1; apply contrapT in H1.
    move: H1 => [p H1].
    elim: p H1 => [ H1 | [[x1 y1] o1] p _ ];
                 (* p = [::]*)first by rewrite D_L16_E42a;left;left;rewrite DeltaP.
    elim: p => [[H1 [H2 H3]] | [[x2 y2] o2]  p _ H1].
    (* p = [::(x',y',o)] *)
    rewrite /= in H1 H2;rewrite -H1 -H2;clear H1 H2.
    by case: o1 H3 => [ ? | ?];[ apply E_inc_Aw_s | apply Einv_inc_Aw_s].
    (* general case *)
    pose q:= [:: (x1, y1, o1), (x2, y2, o2) & p].
    rewrite -/q in H1.
    have H2: size q = (size p).+2 by rewrite /q.
    rewrite D_L16_E42a.
    pose proof D_L18 H2 H1 as [q' [o' [y' [_ [[H4 _] | [H4 _]]]]]].
    by left;right.
    by right.
  Qed.
  
End Active_path_implies_Aw_s.

Section Main_Result.

  Theorem Th5_s: forall (x y: T), ( x [⊥d] y | W ) <-> ~ Aw_s (x,y).
  Proof.
    move => x y; split.
    by apply contraPP => /contrapT H1; apply C_P8.
    by apply contraPP => /D_P15 H1;rewrite notP.
  Qed.

  (** * This is the main result of the paper csbr *)

  (* begin snippet theoremfive:: no-out *)  
  Theorem Th5: forall (x y: T), ( x [⊥d] y | W ) <-> ~ Aw (x,y).
  (* end snippet theoremfive *)  
  Proof.
    move => x y; rewrite B_L7. apply Th5_s.
  Qed.
  
End Main_Result. 
