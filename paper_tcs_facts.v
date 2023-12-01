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
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  ssrel rel erel3 aacset paper_relations paper_csbr_rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Tcs.
  (** * proofs for the paper Topological conditional separation *)
  
  (* starting by closure properties *) 

  Lemma Singl_iff': forall (x y:A), (x \in [set y])%classic <-> x = y.
  Proof.
    move => x y. rewrite in_setE.
    split. 
    by [].
    by move => ->.
  Qed.
  
  Lemma Clos_Ew: forall (x y:A),  y \in Clos_(x | E,W) <-> Ew.* (y, x).
  Proof.
    move => x' y'.
    split. 
    rewrite in_setE.
    move =>  [z [H1 /Singl_iff <-]].
    by [].
    by move => H1;rewrite in_setE;exists x';split;[ | rewrite in_setE].
  Qed.

  (* Closure intersect as a relation *) 
  Definition Closure_intersect := 
    [set xy | Clos_(xy.1 | E,W) `&` Clos_(xy.2 | E,W) <> set0 ]%classic.

  Lemma Clos_Intersect : forall (x y:A), 
      (Clos_(x | E,W) `&` Clos_(y | E,W) != set0)%classic <-> 
        (let R:= Emw.* * Ew.* in R (x, y)).
  Proof.
    move => w1' w2'; split.
    - rewrite -notempty_exists.
      move => [z H1]. rewrite in_setE in H1.
      move: H1 => [H1 H2].
      move: H1 => [w1 [H1 /Singl_iff <-]]. 
      move: H2 => [w2 [H2 /Singl_iff <-]]. 
      by (exists z; split;[rewrite Emw_1 |]). 
    - rewrite -notempty_exists.
      move => [z /= [H1 H2]]. rewrite Emw_1 /inverse /mkset /= in H1.
      by (exists z);rewrite in_setE;split;rewrite -in_setE Clos_Ew. 
  Qed.
  
  (* Closure intersect as a relation, Closure_intersect, is equal to (Emw.* * Ew.* ) *) 
  Lemma Clos_Intersect_eq: Closure_intersect = (Emw.* * Ew.* ).
  Proof.
    apply classic_relation;split => [x y H1 | x y H1].
    by rewrite /Closure_intersect Clos_Intersect in H1.
    by rewrite /Closure_intersect Clos_Intersect.
  Qed.
  
  (* Closure intersect on W as a relation (removing reflexivity) *) 
  Definition Closure_intersectW := 
    fun (w1 w2:A) => w1∈ W /\ w2 ∈ W /\ w1 <> w2 /\ 
                    Clos_(w1 | E,W) ∩ Clos_(w2 | E,W)<> '∅.

  Lemma Kw_W : Δ_(W)*('Δ + Δ_(W.^c)* Bw + Bmw*Δ_(W.^c) + Kw )*Δ_(W)
               = Δ_(W) + Δ_(W) * Kw * Δ_(W).
  Proof.
    rewrite composeDl composeDl composeDl composeDr composeDr composeDr.
    have -> : Δ_(W) * 'Δ * Δ_(W) = Δ_(W)
      by rewrite  Delta_idem_r DeltaE_inv.
    have -> : Δ_(W) * (Δ_(W.^c) * Bw)* Δ_(W) = 'Δc
      by rewrite -composeA DeltaW_Wc !DeltaC_compose_absorbl.
    have -> : Δ_(W) * (Bmw * Δ_(W.^c)) * Δ_(W) = 'Δc
      by rewrite composeA [(Bmw * Δ_(W.^c) * Δ_(W))]composeA DeltaWc_W
           !DeltaC_compose_absorbr.
    by rewrite !DeltaC_union_idemr.
  Qed.
  
  Lemma Kw_W': Δ_(W) * (Emw.* * Ew.* ) * Δ_(W) =Δ_(W) + Δ_(W) * Kw * Δ_(W).
  Proof.
    by rewrite L7_E23a Kw_W.
  Qed.
  
  Lemma ClosW_Intersect : forall (w1 w2:A),
      w1 ∈ W /\ w2 ∈ W /\ w1 <> w2 ->
      Clos_(w1 | E,W) ∩ Clos_(w2 | E,W)<> '∅ <-> 
        (let R:= Δ_(W) * Kw * Δ_(W) in R w1 w2).
  Proof.
    move => w1' w2' [H1 [H2 H3]]; split => H4.
    - have H5: (Emw.* * Ew.* ) w1' w2' by rewrite -Clos_Intersect_eq.
      have H6: (Δ_(W)* (Emw.* * Ew.* )* Δ_(W)) w1' w2' by apply R_restrict.
      have H7: (Δ_(W) + Δ_(W) * Kw * Δ_(W))  w1' w2' by rewrite -Kw_W'.
      by move: H7 => [[z H7] | H7] //.
    - have H5:  (Δ_(W) + (Δ_(W) * Kw * Δ_(W)))  w1' w2'
        by apply union_containsr.
      have H6: (Δ_(W)* (Emw.* * Ew.* )* Δ_(W)) w1' w2' by rewrite Kw_W'.
      have H7: (Emw.* * Ew.* ) w1' w2' by apply R_restrict in H6.
      by rewrite -Clos_Intersect_eq in H7.
  Qed.
  
  Lemma Clos_Intersect_W_inc: Closure_intersectW ⊂ Δ_(W) * Kw * Δ_(W).
  Proof.
    move => x y [H1 [H2 [H3 H4]]].
    by apply ClosW_Intersect. 
  Qed.
  
  Lemma Clos_Intersect_W_t_eq: (Closure_intersectW).+ ⊂ Cw. 
  Proof.
    have H1: (Closure_intersectW).+ ⊂ (Δ_(W) * Kw * Δ_(W)).+ 
      by apply clos_t_inc; apply Clos_Intersect_W_inc.
    have H2: (Δ_(W) * Kw * Δ_(W)).+ ⊂ Cw by apply union_containsl.
    by apply inclusion_transitive with (Δ_(W) * Kw * Δ_(W)).+ .
  Qed.

  Lemma TOBEUSED: forall (X Y: Ensemble A),
      (Included _ Y W) /\ (Y ∩ (CBK X) = '∅)
      -> ~(exists z, z∈ Clos(Y | E,W) /\ z∈ Clos(CBK X | E,W)).
  Proof.
    move => X Y [H1 H2] [z [/Clos_to_singleton H3 /Clos_to_singleton H4]].
    move: H3 H4 => [w1 [H3 H'3]] [w2 [H4 H'4]].
    have H5: w1 ∈ W by apply H1 in H3.
    have H6: w2 ∈ W by rewrite /CBK in H4;
      move: H4 => [x [[u [H6 _]] _]]; rewrite Cw_starts in H6;move: H6 => [v [[H6 _] _]].
    have H7: w1 <> w2
      by move => H8; (have H9: Y ∩ (CBK X) <> '∅ by apply notempty_exists;
                      exists w1; split;[ | by rewrite H8]).
    have H8: (Δ_(W) * Kw * Δ_(W)) w1 w2
      by apply ClosW_Intersect;[ |rewrite -notempty_exists;exists z;split].
    (* on doit montrer qu'alors w1 est aussi dans (CBK X) *)
    have H9: Cw w1 w2  by left; rewrite /DKD;apply t_step.
    move: H4 => [x [H10 H11]].
    have H12: (Cw *(Bmw + Kw)) w1 x by rewrite -Cw_transitive composeA; exists w2.
    have H13: w1 ∈ (CBK X) by rewrite /CBK;exists x.
    have H14:  Y ∩ (CBK X) <> '∅ by rewrite -notempty_exists; exists w1; split.
    by [].
  Qed.
  
  Section Lemma_12.

    Lemma L12_a: (Cw * Emw.* * Ew.* * (( 'Δ +  Cw*(Bmw + Kw)) * Δ_(W.^c))) =
                   Cw * (Bmw + Kw) * Δ_(W.^c).
    Proof.
      rewrite {1}composeDr {1}composeDl Delta_idem_l L7_E23d.
      aac_rewrite L7_E23c.
      by aac_reflexivity. 
    Qed.
    
    Lemma L12_b: (Δ_(W.^c) * ( 'Δ + (Bw + Kw)*Cw ) * Emw.* * Ew.* * Cw) =
                   (Δ_(W.^c) * (Bw + Kw) *Cw).
    Proof.
      have H: (Δ_(W.^c) * Emw.* * Ew.* * Cw) = (Δ_(W.^c ) * (Emw.* * Ew.* ) * Cw)
        by aac_normalise.
      rewrite {1}composeDl Delta_idem_r {1}composeDr {1}composeDr {1}composeDr H L7_E23e.
      have H1: (Δ_(W.^c) * ((Bw + Kw) * Cw) * Emw.* * Ew.* * Cw) =
                 (Δ_(W.^c) * (Bw + Kw) * (Cw * Emw.* * Ew.* * Cw))
        by aac_normalise.
      by rewrite H1 L7_E23c union_RR.
    Qed.

    Lemma L12: (Δ_(W.^c) *('Δ + (Bw + Kw)*Cw) * Emw.* * Ew.* * Cw * Emw.* * Ew.* *
                  ( 'Δ +  Cw*(Bmw + Kw)) * Δ_(W.^c)) =
                 Δ_(W.^c) * (Bw + Kw) * Cw * (Bmw + Kw) * Δ_(W.^c).
    Proof.
      rewrite L12_b.
      have H1: (Δ_(W.^c) * (Bw + Kw) * Cw * Emw.* * Ew.* * 
                  ('Δ + Cw * (Bmw + Kw)) * Δ_(W.^c)) = 
                 (Δ_(W.^c) * (Bw + Kw) * 
                    ( Cw * Emw.* * Ew.* * (('Δ + Cw * (Bmw + Kw)) * Δ_(W.^c))))
        by aac_reflexivity.
      rewrite H1 L12_a.
      by aac_reflexivity.
    Qed.

  End Lemma_12.

  Section Lemma_13.
    
    Lemma L13_a : (Δ_(W.^c) * Emw.* * Ew.* * Δ_(W.^c))
                  = (Δ_(W.^c) * ('Δ + Bw + Bmw + Kw) * Δ_(W.^c)).
    Proof.
      have H1: (Δ_(W.^c) * Emw.* * Ew.* * Δ_(W.^c)) =
                 (Δ_(W.^c) * ( Emw.* * Ew.* ) * Δ_(W.^c))
        by aac_reflexivity.
      have H2:  (Δ_(W.^c) * (Bmw * Δ_(W.^c)) * Δ_(W.^c))
                = (Δ_(W.^c) * Bmw * (Δ_(W.^c) * Δ_(W.^c)))
        by aac_reflexivity.
      rewrite H1 L7_E23a composeDl composeDl composeDl Delta_idem_r.
      rewrite -[Δ_(W.^c) * (Δ_(W.^c) * Bw)]composeA DeltaE_inv.
      rewrite composeDr composeDr composeDr  DeltaE_inv.
      rewrite H2  DeltaE_inv.
      rewrite [in RHS]composeDl [in RHS]composeDl [in RHS]composeDl Delta_idem_r.
      rewrite [in RHS]composeDr [in RHS]composeDr [in RHS]composeDr DeltaE_inv.
      by [].
    Qed.
    
    Lemma L13_b:  (Δ_(W.^c) * ((Bw + Kw) * Cw) * Emw.* * Ew.* * Δ_(W.^c))
                  = (Δ_(W.^c) * (Bw + Kw) * Cw * (Bmw + Kw) * Δ_(W.^c)).
    Proof.
      have H1 : (Δ_(W.^c) * ((Bw + Kw) * Cw) * Emw.* * Ew.* * Δ_(W.^c) )
                = (Δ_(W.^c) * (Bw + Kw) * (Cw * Emw.* * Ew.* * Δ_(W.^c)) )
        by aac_reflexivity.
      rewrite H1 L7_E23d.
      by aac_reflexivity.
    Qed.
    
    Lemma L13_c: (Δ_(W.^c) * Emw.* * Ew.* * (Cw * (Bmw + Kw)) * Δ_(W.^c))
                 = (Δ_(W.^c) * (Bw + Kw) * Cw * (Bmw + Kw) * Δ_(W.^c)).
    Proof.
      have H1: (Δ_(W.^c) * Emw.* * Ew.* * (Cw * (Bmw + Kw)) * Δ_(W.^c))
               = ((Δ_(W.^c) * (Emw.* * Ew.* ) * Cw) * (Bmw + Kw) * Δ_(W.^c))
        by aac_reflexivity.
      by rewrite H1 L7_E23e.
    Qed.
    
    Lemma L13_d: (Δ_(W.^c) * ((Bw + Kw) * Cw) * Emw.* * Ew.* * (Cw * (Bmw + Kw))
                                                               * Δ_(W.^c))
                 =Δ_(W.^c) * (Bw + Kw) * Cw * (Bmw + Kw) * Δ_(W.^c).
    Proof.
      have H1:  (Δ_(W.^c) * ((Bw + Kw) * Cw) * Emw.* * Ew.* * (Cw * (Bmw + Kw))
                                                              * Δ_(W.^c)) =
                  (Δ_(W.^c) * (Bw + Kw) * ((Cw * Emw.* * Ew.* ) * Cw) * 
                     (Bmw + Kw) * Δ_(W.^c)) 
        by aac_reflexivity.
      by rewrite H1 L7_E23c.
    Qed.
    
    Lemma L13: (Δ_(W.^c)* Smw *  Emw.* * Ew.* * Sw * Δ_(W.^c))
               = Δ_(W.^c)* Aw *  Δ_(W.^c).
      rewrite /Smw /Sw composeDl composeDl !composeDr !Delta_idem_r.
      rewrite -[(Bw * Cw + Kw * Cw)]composeDr.
      rewrite -[(DKD.+ * (Bmw + Kw) + Δ_(W) * (Bmw + Kw))]composeDr -/Cw.
      (* now we have 4 terms as in the math proof *)
      rewrite L13_d L13_b L13_c L13_a union_RR unionA union_RR.
      rewrite -composeDr. 
      have H1: (Δ_(W.^c) * ('Δ + Bw + Bmw + Kw) +
                  Δ_(W.^c) * (Bw + Kw) * Cw * (Bmw + Kw))
               = (Δ_(W.^c) * ('Δ + Bw + Bmw + Kw) +
                    Δ_(W.^c) * ((Bw + Kw) * Cw * (Bmw + Kw)))
        by aac_normalise.
      rewrite H1 -composeDl /Aw /Dw.
      by aac_reflexivity.
    Qed.

  End Lemma_13.
  
  Section Theorem_5.
    (** * t-separation is equivalent to d-separation on W.^c *)

    Definition d_separated (x y:A) := ~ (Aw x y).
    
    Definition t_separated (x y:A) :=
      Clos( Sw#_(x) | E, W) ∩ Clos( Sw#_(y) | E, W) = '∅.
    
    (* Definition not_t_separated (x y:A) :=
        (exists z, z ∈ Clos( Sw#_(x) | E, W) /\ z ∈ Clos( Sw#_(y) | E, W)). *)
    
    Lemma T_not_t_separated : forall (x y:A),
        x ∈ W.^c -> y ∈ W.^c ->
        (Clos( Sw#_(x) | E, W) ∩ Clos( Sw#_(y) | E, W) <> '∅ <-> Aw x y).
    Proof. 
      move => x y Hx Hy.
      split.
      - rewrite -notempty_exists.
        move=> [_ [z H1]] H2.
        rewrite Fset_comp in H1.
        rewrite Fset_comp in H2.
        have H3: ((Ew.* * Sw).-1 * (Ew.* * Sw)) x y
          by apply Fset_intersect; exists z; by split.
        have H4: (Δ_(W.^c) * ((Ew.* * Sw).-1 * (Ew.* * Sw))  * Δ_(W.^c)) x y
          by apply R_restrict.
        have H5: (Δ_(W.^c) * Aw * Δ_(W.^c)) = 
                   (Δ_(W.^c) * ((Ew.* * Sw).-1 * (Ew.* * Sw)) * Δ_(W.^c))
          by rewrite -L13 inverse_compose Sw_inverse Emw_1;aac_reflexivity.
        have H6: (Δ_(W.^c) * Aw * Δ_(W.^c)) x y
          by rewrite H5.
        by apply R_restrict in H6.
      - move => H1.
        have H2: (Δ_(W.^c) * Aw * Δ_(W.^c)) x y by apply R_restrict.
        have H3: (Δ_(W.^c) * Aw * Δ_(W.^c)) = 
                   (Δ_(W.^c) * ((Ew.* * Sw).-1 * (Ew.* * Sw)) * Δ_(W.^c))
          by rewrite -L13 inverse_compose Sw_inverse Emw_1;aac_reflexivity.
        have H4: (Δ_(W.^c) * ((Ew.* * Sw).-1 * (Ew.* * Sw))  * Δ_(W.^c)) x y
          by rewrite H3 in H2.
        apply R_restrict in H4; last by split.
        move: H4 => [z [H4 H5]].
        have H6: (Ew.* * Sw) z x by [].
        move: H6 => [t [H6 H'6]].
        move: H5 => [u [H5 H'5]].
        rewrite -notempty_exists.
        exists z;split; first by (exists t; split; [ | exists x; split;[ |apply In_singleton]]).
        by (exists u; split; [ | exists y;split;[ |apply In_singleton]]).
    Qed.
    
    (* Theorem 5 *)
    Theorem T5: forall (x y:A), x ∈ W.^c -> y ∈ W.^c -> (t_separated x y <-> d_separated x y).
    Proof.
      move => x y Hx Hy.
      by rewrite /t_separated -empty_iff T_not_t_separated.
    Qed.

  End Theorem_5.
  
  Section Lemma_7.
    
    Local Lemma L7_1: forall (x y:A), 
        x ∈ W.^c -> Bw x y -> Clos_( x | E,W) ∩ Clos_(y | E,W) <> '∅.
    Proof. 
      move => x y H1 H2.
      have H3: (Δ_(W.^c) * Bw) x y by apply R_restrict_l.
      have H5: Ew.+ x y by move: H3;rewrite /Bw -composeA -/Ew r_clos_rt_clos_t.
      have H7: x ∈ Clos_(y | E,W) by apply Clos_Ew; apply clos_t_clos_rt.
      have H8: x ∈ Clos_(x | E,W) by apply Clos_x_x.
      by rewrite -notempty_exists; exists x; split.
    Qed.

    Local Lemma L7_2: forall (x y:A), 
        y ∈ W.^c -> Bmw x y -> Clos_( x | E,W) ∩ Clos_(y | E,W) <> '∅.
    Proof. 
      rewrite /Bmw. move => x y H1 H2.
      have H3: Clos_( y | E,W) ∩ Clos_(x | E,W) <> '∅ by apply L7_1.
      (* intersection commutative *)
      rewrite -notempty_exists in H3. move: H3 => [z' [z H5] H6].
      by rewrite -notempty_exists;exists z.
    Qed.
    
    Local Lemma L7_3: forall (x y:A), 
        Kw x y -> Clos_( x | E,W) ∩ Clos_(y | E,W) <> '∅.
    Proof. 
      rewrite E9e; move => x y [z [H1 H2]];rewrite -notempty_exists;exists z;split.
      - exists x;split; last by constructor.
        by rewrite /Emw -inverse_clos_t /inverse in H1;
        rewrite -DuT_eq_Tstar; right.
      - by exists y;split => [ |//]; rewrite -DuT_eq_Tstar; right.
    Qed.
    
    Local Lemma L7_4: forall (x y:A), 
        x ∈ W.^c -> y ∈ W.^c -> 
        (let R:= 'Δ + Bw + Bmw + Kw in R x y) ->
        Clos_( x | E,W) ∩ Clos_(y | E,W) <> '∅.
    Proof.
      move => x y Hx Hy [[[[_ H1]| H2] | H3] | H4]. 
      - rewrite -notempty_exists;exists x; split;
          first by (exists x; split; [rewrite -DuT_eq_Tstar; left | constructor]).
        by (exists x;split;[rewrite -DuT_eq_Tstar;left | rewrite H1; constructor]).
      - by apply: L7_1.
      - by apply: L7_2.
      - by apply: L7_3.
    Qed.
    
    Lemma L7_5: forall (x y:A), 
        x ∈ W.^c -> y ∈ W.^c ->
        Clos_( x | E,W) ∩ Clos_(y | E,W) = '∅ ->
        Aw x y ->
        (let R:= (Bw + Kw) * Cw *(Bmw + Kw) in R x y).
    Proof.
      rewrite /Aw. 
      move => x y Hx Hy H1 [H2 | H2].
      by have H3: Clos_( x | E,W) ∩ Clos_(y | E,W) <> '∅ by apply L7_4.
      by rewrite /Dw -composeA in H2.    
    Qed.
    
    Lemma L7_6l : forall (x y :A), Cw x y -> x ∈ W.
    Proof.
      by rewrite Cw_starts; move => x y [w_x [[H1 H'1] _]]. 
    Qed.

    Lemma L7_6r : forall (x y :A), Cw x y -> y ∈ W.
    Proof.
      by rewrite Cw_ends; move => x y [w_x [_ [H1 <-]]].  
    Qed.
    
    Lemma L7_7:  forall (x w:A), 
        x ∈ W.^c -> 
        (let R:= (Bw + Kw) in R x w) ->
        Clos_( x | E,W) ∩ Clos_(w | E,W) <> '∅.
    Proof.
      by move => x w Hx [H1 | H1];[apply L7_1 | apply L7_3].
    Qed.
    
    Lemma L7_8:  forall (y w:A), 
        y ∈ W.^c -> 
        (let R:= (Bmw + Kw) in R w y) ->
        Clos_( y | E,W) ∩ Clos_(w | E,W) <> '∅.
    Proof.
      rewrite /Bmw -Kw_inverse -inverse_union.
      by move => y w H1 H2; have H3: (Bw + Kw) y w by [];apply: L7_7.
    Qed. 
    
    Lemma L7_final: forall (x y:A), 
        x ∈ W.^c -> y ∈ W.^c -> Clos_(x |E,W) ∩ Clos_(y|E,W) = '∅ -> Aw x y -> 
        exists w_x, exists w_y, w_x ∈ W/\ w_y ∈ W /\ Cw w_x w_y 
                                /\ (Clos_(x| E,W) ∩  Clos_(w_x| E,W) <> '∅)
                                /\ (Clos_(y| E,W) ∩  Clos_(w_y| E,W) <> '∅).
    Proof.
      move => x y Hx Hy H1 H2.
      have [w_y [[w_x [H3 H4]] H5]]:
        (let R:= (Bw + Kw) * Cw *(Bmw + Kw) in R x y) by apply L7_5.
      exists w_x; exists w_y.
      split; first by apply: L7_6l H4.
      split; first by apply: L7_6r H4.
      split; first by [].
      split; first by apply L7_7.
      by apply L7_8.
    Qed.

  End Lemma_7.
  
  Section Lemma_8_part1.

    Lemma L8_part1_a : forall (w1 w2:A), 
        w1 ∈ W -> w2 ∈ W -> w1 <> w2 ->
        Clos_(w1 | E,W) ∩ Clos_(w2 | E,W)<>'∅ ->
        Cw w1 w2.
    Proof.
      move => w1 w2 H1 H2 H3 H4.
      have H5 : (Δ_(W) * Kw * Δ_(W)) w1 w2 by apply ClosW_Intersect.
      by rewrite /Cw /DKD; left;rewrite -clos_t_decomp_rt_r; left.
    Qed.
    
    Lemma L8_part1 : forall (W' W'': Ensemble A),
        Included _ W' W /\ Included _ W'' W /\ (forall (w' w'':A), w' ∈ W' /\ w'' ∈ W'' -> ~(Cw w' w''))
        -> Clos(W' | E,W) ∩ Clos(W''| E,W) = '∅. 
    Proof.
      move => W' W'' [H1 [H2 H3]].
      rewrite empty_notexists.
      move => [u [z /Clos_to_singleton H10 /Clos_to_singleton H11]].
      move: H10 H11 => [w1 [H10 H'10]] [w2 [H11 H'11]].
      have H12: Clos_(w1| E,W) ∩ Clos_(w2 |E,W)<>'∅
        by rewrite -notempty_exists;exists z.
      have H6: w1 ∈ W by apply H1 in H10.
      have H7: w2 ∈ W by apply H2 in H11.
      have H8: ~ Cw w1 w2 by apply H3.
      have H9:  w1 <> w2 by move => H9; have H9': Cw w1 w2 by rewrite H9;apply Cw_reflexive_W.
      have H13: Clos_(w1 | E,W) ∩ Clos_(w2 | E,W) = '∅
        by rewrite empty_notexists;
        elim: (classic (exists z, z ∈ (Clos_(w1 | E,W) ∩ Clos_(w2 | E,W))));
        [ move => H4 H5;have H14:Cw w1 w2 by apply L8_part1_a | move => H4 H5].
      by [].
    Qed.

  End Lemma_8_part1.

  Section Lemma8_part2.
    
    Local Lemma clos_t_sep_n : forall (n: nat) (W' W'': Ensemble A) (w' w'':A) (R: relation A),
        (Included _ W' W) /\ (W''= Setminus _ W W') /\ 
          w' ∈ W' /\ w'' ∈ W'' /\ (iter (Δ_(W) * R *Δ_(W))  n.+1) w' w''
        -> let Rw := (Δ_(W) * R *Δ_(W)) in
           (exists (x' y': A), x'∈ W' /\ y' ∈ W'' /\ Rw x' y').
    Proof.
      move => n X Y x y R.
      elim: n x y => [x y [H1 [H2 H3]] | n H0 y y' ].
      by (exists x; exists y; rewrite /iter Delta_idem_l in H3).
      rewrite /iter -/iter.
      move => [H2 [H3 [H4 [H5 [z [H6  H7]]]]]].
      elim: (classic (z ∈ X)) => Hz. by (exists z; exists y').
      (* need to prove that z \in Y *)
      have H8: z ∈ W. by move: H7 => [u [[v [[H7 _] _]] _]].
      have H9: z ∈ Y. by rewrite H3; apply Setminus_intro.
      have H10: let Rw:=(Δ_(W) * R *Δ_(W))in exists x' y' : A, x' ∈ X /\ y' ∈ Y /\ Rw x' y'.
      by apply H0 with y z.
      move: H10 => [x2 [y2 [H11 [H12 H13]]]].
      by exists x2; exists y2.
    Qed.

    Lemma clos_t_sep : forall (W' W'': Ensemble A) (w' w'':A) (R: relation A),
        (Included _ W' W) /\ (W''= Setminus _ W W') /\ 
          w' ∈ W' /\ w'' ∈ W'' /\ (Δ_(W) * R *Δ_(W)).+ w' w''
        -> let Rw := (Δ_(W) * R *Δ_(W)) in
           (exists (x' y': A), x'∈ W' /\ y' ∈ W'' /\ Rw x' y').
    Proof.
      move => W' W'' w' w'' R [H1 [H2 [H3 [H4 H5]]]].
      apply clos_t_iterk in H5.
      move: H5 => [n' H5].
      by apply clos_t_sep_n with n' w' w''.
    Qed.

    Lemma L8_a: forall (W' W'': Ensemble A) (w' w'':A),
        (Included _ W' W) /\ (W''= Setminus _ W W') /\ w' ∈ W' /\ w'' ∈ W''
        /\ Cw w' w''
        -> let Rw := (Δ_(W) * Kw *Δ_(W)) in
           (exists (x' y': A), x'∈ W' /\ y' ∈ W'' /\ Rw x' y').
    Proof.
      move => W' W'' w' w'' [H1 [H2 [H3 [H4 H5]]]].
      have H8:  W' ∩ W'' = '∅  by apply W_part with W.
      have H6: w' <> w''
        by move => H6; rewrite -H6 in H4;
                   (have H7: W' ∩ W'' <> '∅ by apply notempty_exists;exists w'; split).
      have H7:  (Δ_(W) * Kw *Δ_(W)).+ w' w'' by move: H5 => [H5 | [ x H5]].
      by apply clos_t_sep with w' w''.
    Qed.

    Lemma L8_b: forall (W' W'': Ensemble A) (w' w'':A),
        (Included _ W' W) /\ (W''= Setminus _ W W') /\ w' ∈ W' /\ w'' ∈ W''
        /\ Cw w' w''
        -> (exists (w1' w1'':A), w1' ∈ W' /\ w1'' ∈ W'' /\
                                   Clos_( w1' | E,W) ∩ Clos_(w1'' | E,W) <> '∅).
    Proof.
      move => W' W'' w' w'' H1.
      have [x' [y' [H2 [H3 H4]]]]:
        let Rw := (Δ_(W) * Kw *Δ_(W)) in (exists (x' y': A), x'∈ W' /\ y' ∈ W'' /\ Rw x' y')
          by apply L8_a with w' w''.
      apply ClosW_Intersect in H4. rewrite -notempty_exists in H4.
      move: H4 => [z H4].
      by exists x'; exists y';rewrite -notempty_exists;split;[| split;[ | exists z]].
                move: H1 => [H'1 [H'2 [H'3 [H'4 H'5]]]].
                split; first by apply H'1 in H2.
                split; first by rewrite H'2 in H3;move: H3 => [H3 _].
                move => H5.
                have H6: W' ∩ W'' <> '∅ by rewrite -notempty_exists;exists x';split;[|rewrite H5].
                have H7: W' ∩ W'' = '∅ by apply W_part with W.
                by [].
    Qed.

    Lemma L8_part2: forall (W' W'': Ensemble A),
        (Included _ W' W) /\ (W''= Setminus _ W W') /\ Clos(W' | E,W) ∩ Clos(W'' | E,W)='∅
        -> ~ (exists (w' w'': A), w' ∈ W' /\ w'' ∈ W'' /\ Cw w' w'').
    Proof.
      move => W' W'' [H1 [H2 H3]] [w' [w'' [H4 [H5 H6]]]].
      have H7:  (exists (w1' w1'': A), w1' ∈ W' /\ w1'' ∈ W'' /\
                                         Clos_( w1' | E,W) ∩ Clos_(w1'' | E,W)<>'∅)
        by apply L8_b with w' w''.
      move: H7 => [w1 [w2 [H7 [H8 H9]]]].
      have [_ [z H10 H11]]: exists z, z∈  (Clos_( w1 | E,W) ∩ Clos_( w2 | E,W))
          by rewrite notempty_exists.
      have H12:  Clos(W'|E,W) ∩ Clos(W''|E,W) <> '∅
        by rewrite -notempty_exists;exists z;split;rewrite Clos_to_singleton;[exists w1 | exists w2].
      by [].
    Qed.

  End Lemma8_part2.
  
  Section Proposition_6.

    Lemma P6_1_first_contra': forall (Γ Λ: Ensemble A) (W' W'': Ensemble A),
        (W' = (Cw*(Bmw + Kw))#Λ) /\ (W''= (Cw*(Bmw + Kw))#Γ ) /\
          (Included _ Γ W.^c) /\ (Included _ Λ W.^c) /\ (Γ ∩ Λ = '∅)
        -> ( Clos(Λ ∪ W'| E,W) ∩ Clos(Γ ∪ W''| E,W) <> '∅)
        -> ~ (forall (λ γ: A), λ ∈ Λ /\ γ ∈ Γ -> t_separated λ γ).
    Proof.
      move => Γ Λ W' W'' [H1 [H2 [H3 [H4 H5]]]] -/notempty_exists [z [t H6 H7]].
      rewrite Clos_to_singleton in H6; move: H6 => [λ [H6 H6'']].
      rewrite Clos_to_singleton in H7; move: H7 => [γ [H7 H7']].
      apply Union_inv in H6; apply Union_inv in H7.
      have H8: λ ∈ Sw#Λ
        by move: H6 => [H6 | H6];rewrite /Sw -Fset_union_rel Fset_D;
                       [ left | right;rewrite -H1].
      have H9: γ ∈ Sw#Γ
        by move: H7 => [H7 | H7];rewrite /Sw -Fset_union_rel Fset_D;
                       [ left | right;rewrite -H2].
      move: H8 => /Fset_union_set H8; move: H8 => [x [H8 H10]].
      move: H9 => /Fset_union_set H9; move: H9 => [y [H9 H11]].
      have H12: Clos( Sw#_(x) | E, W) ∩ Clos( Sw#_(y) | E, W) <> '∅
        by rewrite -notempty_exists; exists t; apply Intersection_intro;
        rewrite Clos_to_singleton;[exists λ | exists γ].
      by move => H; have H13: t_separated x y by apply H.
    Qed.
    
    (* Une autre façon équivalente de voir ce qu'est (Cw*(Bmw + Kw))#X *)
    Lemma TClos :  forall (w : A) (X : Ensemble A),
        Included _ X W.^c ->
        ( w ∈ (Cw*(Bmw + Kw))#X
          <-> (exists w', Cw w w' /\ (exists z, z ∈ Clos_(w'|E,W) /\ z ∈ Clos(X|E,W)))).
    Proof.
      move => w X H1;rewrite (Fset_restrict _ H1) -L7_E23d -Fset_restrict=> [|//].
      rewrite composeA; split.
      - move => [x [[x' [H2 [z [H3 H'3]]]] H4] ].
        exists x'; split => [// |].
        by (exists z; split;[ exists x'; split;
                                     [rewrite Emw_1 in H3 | apply In_singleton] | exists x; split]).
      - move => [w' [H2 [z [[w'' [H3 H'3]] [x [H4 H'4]]]]]].
        exists x; split; last by [].
        exists w';split; first by[].
        by exists z;split;[apply Singleton_inv in H'3; rewrite H'3 Emw_1 | ].
    Qed.
    
    Lemma L11: forall (Θ: Ensemble A) (W': Ensemble A),
        (W' ∩ (Cw*(Bmw + Kw))#Θ = '∅) 
        -> Included _ W' W
        -> Included _ Θ  W.^c
        -> ( Clos(W'| E,W) ∩ Clos(Θ ∪ (Cw*(Bmw + Kw))#Θ| E,W)= '∅).
    Proof.
      move => Θ W' H0 H0' H0''.
      - (* first part *) have H1:  Clos(W'| E,W) ∩ Clos(Θ| E,W)= '∅.
        rewrite empty_notexists.
        move => [_ [t H2 H3]].
        rewrite Clos_to_singleton in H2.
        move: H2 => [y [H2 H4]].
        have H5: y ∈ (Cw*(Bmw + Kw))#Θ
          by rewrite TClos;[exists y;split;
                                   [apply Cw_reflexive_W;apply H0' in H2|exists t]|].
        have H6: y ∈ ( W' ∩ (Cw * (Bmw + Kw))#Θ) by split.
        have H7: W' ∩ (Cw * (Bmw + Kw))#Θ <> '∅ by rewrite -notempty_exists;exists y.
        by [].
      - (* second part *) 
        have H'1:  Clos(W'| E,W) ∩ Clos( (Cw*(Bmw + Kw))#Θ| E,W)= '∅.
        rewrite empty_notexists.
        move => [_ [t H2 H3]].
        rewrite Clos_to_singleton in H2.
        rewrite Clos_to_singleton in H3.
        move: H2 H3 => [w [H2 H4]] [θ [H3 H5]].
        have H6: θ <> w
          by move => H6;(have H7: W' ∩ (Cw * (Bmw + Kw))#Θ <> '∅
                          by rewrite -notempty_exists;exists θ;split;[rewrite H6 |]).
        have H8: Cw w θ
          by apply L8_part1_a;[ apply H0' in H2 | apply CBK_W in H3
                              | move => H7;symmetry in H7
                              |rewrite -notempty_exists;(exists t)].
        have H9: w ∈ (Cw*(Cw * (Bmw + Kw)))#Θ
          by rewrite -Fset_comp; exists θ; split.
        have H10: w ∈ (Cw * (Bmw + Kw))#Θ
          by rewrite - Cw_transitive composeA.
        have H11:  W' ∩ (Cw * (Bmw + Kw))#Θ <> '∅
          by rewrite -notempty_exists; exists w; split.
        by [].
      - (* combine *)
        by rewrite Clos_union Distributivity H1 H'1 Union_idempotent.
    Qed.

    Lemma P6_1_second: forall (Γ Λ: Ensemble A) (W' W'' Wt: Ensemble A),
        (W' = (Cw*(Bmw + Kw))#Γ) /\ (W''= (Cw*(Bmw + Kw))#Λ )
        /\ (Wt = Setminus _ W (W'∪ W''))
        /\ (Included _ Γ W.^c) /\ (Included _ Λ W.^c) /\ (Γ ∩ Λ = '∅)
        /\ Clos(Λ ∪ W''|E,W) ∩ Clos(Γ ∪ W'|E,W) = '∅
        -> ( Clos(Γ ∪ (W' ∪ Wt) | E,W) ∩ Clos(Λ ∪ W''| E,W) = '∅).
    Proof.
      move => Γ Λ W' W'' Wt [H1 [H2 [H3 [H4 [H5 [H6 H'6]]]]]].
      have H7: (W'∪ W'') ∩ Wt = '∅.  apply W_part with W.
      split.
      by move => x [x' H8| x' H8];
                 [rewrite H1 in H8;apply CBK_W in H8| rewrite H2 in H8;apply CBK_W in H8].
      by [].
      
      have [H8 H9]: (Wt ∩ W' = '∅) /\ (Wt ∩ W'' = '∅)
        by rewrite Intersection_commutative Distributivity Union_empty in H7.
      
      have H10: Clos(Wt | E,W) ∩ Clos(Λ ∪ W''| E,W) = '∅.
      rewrite H2; apply L11.
      by rewrite -H2.
      by rewrite H3; apply In_Setminus.
      by [].
      rewrite -Union_associative Clos_union.
      rewrite -Intersection_commutative.
      rewrite Distributivity.
      rewrite Intersection_commutative in H10.
      rewrite H10 Empty_set_zero_right.
      by [].
    Qed.
    
    (* second part using Lemma 7 and Lemma 8 *)
    Lemma P6_2: forall (W' W'': Ensemble A) (Γ Λ: Ensemble A),
        (Included _ W' W) /\ (W''= Setminus _ W W') /\
          (Included _ Γ W.^c) /\ (Included _ Λ W.^c) /\
          (Γ ∩ Λ = '∅) /\ ( Clos(Λ ∪ W'| E,W) ∩ Clos(Γ ∪ W''| E,W) = '∅)
        -> (forall (λ γ: A), λ ∈ Λ /\ γ ∈ Γ -> t_separated λ γ).
    Proof.
      move => W' W'' Γ Λ [H1 [H2 [H3 [H4 [H5 H6]]]]]  λ γ [H7 H8].
      have H9: λ ∈ W.^c by apply H4 in H7.
      have H10: γ ∈ W.^c by apply H3 in H8.
      rewrite (T5 H9 H10).
      move => H11.
      have H12: Included _ Clos_(γ | E,W) Clos(Γ ∪ W''| E,W) by apply Clos_s_inc.
      have H13: Included _ Clos_(λ | E,W) Clos(Λ ∪ W'| E,W) by apply Clos_s_inc.
      have H14: Included _ Clos_(λ | E,W) ∩ Clos_(γ | E,W)
                  Clos(Λ ∪ W'| E,W) ∩ Clos(Γ ∪ W''| E,W)
        by move => x [t H'1 H'2]; apply H13 in H'1;apply H12 in H'2;split.
      have H15: Included _ Clos_(λ|E,W) ∩ Clos_(γ|E,W) '∅
        by rewrite H6 in H14.
      have H17: Clos_(λ|E,W) ∩ Clos_(γ|E,W) = '∅
        by apply Extensionality_Ensembles;split;[apply H15|].
      clear H12 H13 H14 H15.
      have [w_x [w_y [H12 [H13 [H14 [H15 H16]]]]]]:
        exists w_x, exists w_y, w_x ∈ W/\ w_y ∈ W /\ Cw w_x w_y 
                                /\ (Clos_(λ| E,W) ∩ Clos_(w_x| E,W) <> '∅)
                                /\ (Clos_(γ| E,W) ∩ Clos_(w_y| E,W) <> '∅).
      by apply L7_final.
      have H18: Included _ Clos(W''| E,W) Clos(Γ ∪ W''| E,W) by apply Clos_inc_r.
      have H19: Included _ Clos(W' | E,W) Clos(Λ ∪ W'| E,W) by apply Clos_inc_r.
      have H20: Included _ Clos(W'| E,W) ∩ Clos(W''| E,W) 
                  Clos(Λ ∪ W'| E,W) ∩ Clos(Γ ∪ W''| E,W)
        by move => x [v H'1 H'2];apply H19 in H'1;apply H18 in H'2;split.
      have H21: Included _ Clos(W'| E,W) ∩ Clos(W''| E,W) '∅
        by rewrite H6 in H20.        
      have H22: Clos(W'| E,W) ∩ Clos(W''| E,W) = '∅
        by apply Extensionality_Ensembles;split;[apply H21|]. 
      clear H18 H19 H20 H21.
      have H18: ~ (exists (w' w'': A), w' ∈ W' /\ w'' ∈ W'' /\ Cw w' w'')
        by apply L8_part2.
      move: H15 => /notempty_exists [t' [t H15 H'15]].
      move: H16 => /notempty_exists [u' [u H16 H'16]].
      elim: (classic (w_x ∈ W')) => H19;
                                    elim: (classic (w_y ∈ W')) => H20.
      - have H21: u ∈ Clos(Λ ∪ W' | E,W)
          by rewrite Clos_to_singleton; exists w_y; split;[right|].
        have H23: u ∈ Clos(Γ ∪ W'' | E,W)
          by rewrite Clos_to_singleton; exists γ;split;[left|].
        have H24: Clos(Λ ∪ W'|E,W) ∩ Clos(Γ ∪ W''|E,W) <> '∅
          by rewrite -notempty_exists; exists u.
        by [].
      - have H21: w_y ∈ W'' by rewrite H2;apply Setminus_intro. 
        have H23: (exists w' w'' : A, w' ∈ W' /\ w'' ∈ W'' /\ Cw w' w'')
          by (exists w_x;exists w_y).
        by [].
      - have H21: w_x ∈ W'' by rewrite H2;apply Setminus_intro. 
        have H23: (exists w' w'' : A, w' ∈ W' /\ w'' ∈ W'' /\ Cw w' w'')
          by (exists w_y;exists w_x; split;[ |split;[ |apply Cw_sym]]).
        by [].
      - have H21: t ∈ Clos(Λ ∪ W' | E,W)
          by rewrite Clos_to_singleton; exists λ; split;[left|].
        have H23: w_x ∈ W'' by rewrite H2;apply Setminus_intro. 
        have H24: t ∈ Clos(Γ ∪ W'' | E,W)
          by rewrite Clos_to_singleton; exists w_x;split;[right|].
        have H25: Clos(Λ ∪ W'|E,W) ∩ Clos(Γ ∪ W''|E,W) <> '∅
          by rewrite -notempty_exists; exists t.
        by [].
    Qed.
    
  End Proposition_6.
  
End Tcs.











