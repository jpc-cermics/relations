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

From RL Require Import  ssrel rel erel3 aacset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Parameter (A: Type) (W: set A) (E: relation A).

Section Papers_relations.

  (** * The relations used in the two papers  *)

  Definition Em := E.-1.
  Definition Ew := Δ_(W.^c) * E.
  Definition Bw := E * Ew.* .
  Definition Emw := Ew.-1. 
  Definition Bmw := Bw.-1.
  Definition Kw := (Bmw * Δ_(W.^c) * Bw).
  
  Definition DKD := ( Δ_(W) * Kw *  Δ_(W)).
  Definition Cw := ((DKD).+) `|`   Δ_(W).
  Definition Dw := (Bw `|` Kw) * (Cw * (Bmw `|` Kw)).
  Definition Aw := 'Δ `|` Bw `|` Bmw `|` Kw `|` Dw.
  
  Definition W_s := Fset E.* W.
  Definition DKD_s := ( Δ_(W_s) * Kw *  Δ_(W_s)).
  Definition Cw_s := (DKD_s.+) `|` Δ_(W_s).
  Definition Aw_s :=  'Δ `|` Bw `|` Bmw `|` Kw `|` (Bw `|` Kw)*Cw_s *(Bmw `|` Kw).
  Definition Aw_sp := Bw `|` Kw `|` ((Bw `|` Kw) * Cw_s * Kw).
  Definition Aw_sm := Bmw `|` ((Bw `|` Kw)* Cw_s * Bmw).

  Definition Sw :=  'Δ `|` Cw * (Bmw `|` Kw).
  Definition Smw := 'Δ `|` (Bw `|` Kw)*Cw.

  Definition CBK (X: set A) := (Cw *(Bmw `|` Kw))# X.

End Papers_relations.


Section Ew_facts.

  (** * Properties of Ew *) 

  Lemma Ew_t_starts: Δ_(W.^c) * Ew.+ = Ew.+ .
  Proof.
    by rewrite {1}/Ew  Delta_clos_trans_starts
       -composeA DeltaE_inv -Delta_clos_trans_starts -/Ew.
  Qed.

  Lemma Emw_1 : Emw.* = Ew.* .-1.
  Proof.
    by rewrite /Emw inverse_star.
  Qed.
  
End Ew_facts.
    
Section Bw_facts.
  (** * Properties of Bw *) 
  Lemma Bw_ends : Bw = Bw * Ew.*.
  Proof.
    by rewrite {2}/Bw composeA compose_rt_rt -/Bw.
  Qed.
      
  Lemma Bw_ends1 : Bw * Ew `<=` Bw.
  Proof.
    rewrite /Bw composeA clos_rt_r_clos_t.
    by apply compose_inc; apply clos_t_clos_rt.
  Qed.

  Lemma Bmw_starts : Bmw = (Emw.* * Bmw).
  Proof.
    by rewrite {2}/Bmw inverse_compose [Ew .*.-1]inverse_star -composeA compose_rt_rt
       -inverse_star -inverse_compose.
  Qed.

  Lemma E_incl_Bw : E `<=` Bw.
  Proof.
    by rewrite -[E]Delta_idem_r; apply: compose_inc; apply: clos_refl_trans_containsD.
  Qed.

  Lemma I3_1: E *Δ_(W.^c)* E `<=` Bw.
  Proof.
    rewrite /Bw /Ew.
    have H1: Δ_(W.^c) * E `<=` (Δ_(W.^c) * E).* .
    apply subset_trans with (Δ_(W.^c) * E).+ .
    apply iter1_inc_clos_trans.
    apply clos_t_clos_rt.
    rewrite composeA.
    by apply compose_inc.
  Qed.
      
End Bw_facts. 

Section Bmw_facts.

  Lemma Einv_inc_Bmw: E.-1 `<=` Bmw.
  Proof.
    have H1: Bmw = (Emw.* * E.-1)
      by rewrite /Bmw /Bw /Emw /Ew inverse_compose inverse_star.
    by rewrite H1 -{1}[E.-1]Delta_idem_l;apply: composer_inc;
    apply: clos_refl_trans_containsD.
  Qed.
  
End Bmw_facts.

Section Kw_facts.
  (** * Properties of Bw *) 
  Lemma Kw_ends : Kw = Kw * Ew.*.
  Proof.
    by rewrite {2}/Kw composeA -Bw_ends.
  Qed.

  Lemma Kw_ends1 : Kw * Ew `<=` Kw.
  Proof.
    pose proof Bw_ends1 as H1.
    have H2: (Bmw * Δ_(W.^c)) * (Bw * Ew) `<=` (Bmw * Δ_(W.^c)) * Bw
      by apply compose_inc.
    by rewrite /Kw composeA.
  Qed.
  
  Lemma Kw_starts : Kw = (Emw.* * Kw).
  Proof.
    by rewrite {2}/Kw -composeA -composeA -Bmw_starts.
  Qed.

  Lemma Kw_starts_ends: Kw = (Emw.* * Kw * Ew.* ).
  Proof.
    by rewrite -Kw_starts -Kw_ends.
  Qed.
  
  Lemma E9e : Kw = ((Emw).+ * Ew.+).
  Proof.
    have H1: (Δ_(W.^c) * (E * Ew .* )) = Ew.+ by rewrite -composeA -/Ew r_clos_rt_clos_t.
    have H2: Ew.-1 = E.-1 * Δ_(W.^c) by rewrite  inverse_compose DeltaE_inverse.
    have H3: E .-1 * (Δ_(W.^c) * Ew .+) = Ew.-1 * Ew .+  by rewrite -composeA H2.
    by rewrite /Kw /Bmw /Bw /Ew
       -{2}DeltaE_inv -/Ew composeA composeA
          H1 inverse_compose composeA H3 -composeA
       -inverse_compose  r_clos_rt_clos_t inverse_clos_t -/Emw.
  Qed.
  
  Lemma Kw_inverse: Kw.-1 = Kw.
  Proof.
    by rewrite E9e  -inverse_clos_t inverse_compose inverse_inverse.
  Qed.
  
  Lemma Kw_sym : @symmetric A Kw.
  Proof.
    by apply inverse_sym, Kw_inverse.
  Qed.
  
  Lemma Dx_Kw_Dx_sym: forall (X: set A), @symmetric A (Δ_(X) * (Kw * Δ_(X))).
  Proof.
    move => X x y [z [H1 [z' [H2 H3]]]].
    apply DeltaE_sym in H3;apply DeltaE_sym in H1;apply Kw_sym in H2.
    by exists z';split; [ | exists z; split].
  Qed.
  
End Kw_facts.

Section CwCw_s_facts.
  (** * Properties of Cw *)   

  Definition D (X: set A) := Δ_(X) * Kw *  Δ_(X).
  Definition C (X: set A) :=  (D X).+ `|` Δ_(X).

  Lemma Dsym (X: set A): symmetric ( Δ_(X) * (Kw *  Δ_(X))).+ .
  Proof.
   by apply clos_t_sym, Dx_Kw_Dx_sym.
  Qed.
  
  Lemma C_sym (X: set A) : symmetric (C X).
  Proof.
    have H1: symmetric (D X).+ by rewrite /D composeA; apply Dsym.
    move => x y [ H2| [/= H3 H4]].
    by left; apply: H1.
    by right; split;[ rewrite /fst -H4 |].
  Qed.
  
  (* could be derived from below as Cw is a transitive closure *)
  Lemma C_transitive (X: set A) : (C X) * (C X) = (C X).
  Proof.
    rewrite {1 2}/C composeDr composeDl composeDl DeltaE_compose_same.
    have -> : ((D X).+ * Δ_(X) =(D X).+)
      by rewrite {1}/D -Delta_clos_trans_ends -/D.
    have -> : ( Δ_(X) * (D X).+ ) = (D X).+
      by rewrite {1}/D composeA -Delta_clos_trans_starts -composeA -/D.
    have H1: ((D X).+ * (D X).+ `|` (D X).+ `|` ((D X).+ `|` Δ_(X)))
             = ((D X).+ * (D X).+ `|` ((D X).+ `|` (D X).+) `|` Δ_(X))
      by aac_reflexivity.
    rewrite H1 union_RR.
    have H2: forall (T: relation A), ( T.+ * T.+ `<=` T.+)
        by move => T [x y] [z [/= H3 H4]];apply t_trans with z.
    have H3: ((D X).+ * (D X).+ `|` (D X).+ = (D X).+)
      by rewrite unionC; apply union_inc_eq.
    by rewrite H3.
  Qed.
  
  (* Equivalence relation on W *)
  Lemma C_reflexive_W (X: set A): forall w, w \in X -> (C X) (w, w).
  Proof.
    by move => w';rewrite /C /D; right.
  Qed.
  
  Lemma C_as_clos_t (X: set A): (C X) =  (Δ_(X) `|`  Δ_(X) * Kw *  Δ_(X)).+.
  Proof.
    rewrite predeqE => [[x' y']].
    split => [ [H1 | H2] | ].
    - rewrite /D /clos_t /= in H1.
      elim: H1 => [x y H3 | x y z _ H2 _ H4].
      by apply t_step; right.
      by apply t_trans with y.
    - by apply t_step; left.
    - rewrite /clos_t /=. 
      elim => [x y [H1 | H2] | x y z _ H2 _ H4 ].
      by right.
      by left; apply t_step.
      pose proof (C_transitive X) as <-.
      by exists y; split.
  Qed.
  
  (* XXXX utile ? *)
  Lemma C_n (X: set A) : forall (w w':A),
      w <> w' -> ((C X) (w, w') <->  exists n, (iter (Δ_(X) * Kw * Δ_(X)) n.+1) (w, w')).
  Proof.
    rewrite /C /D; move => w w' H1; split => [[H3| [w1 H3] // ] | [n H3]].
    by apply: clos_t_iterk.
    have H4: (iter (Δ_(X) * Kw * Δ_(X)) (n.+1)) `<=` (Δ_(X) * Kw * Δ_(X)).+
      by apply iterk_inc_clos_trans.
    apply H4 in H3.
    by left.
  Qed.
  
  Lemma C_inverse (X: set A) : (C X).-1 = (C X).
  Proof.
    by apply inverse_sym, C_sym.
  Qed.
  
  Lemma C_ends (X: set A): (C X) = (C X) *  Δ_(X).
  Proof.
    by rewrite composeDr  DeltaE_inv -Delta_clos_trans_ends.
  Qed.

  Lemma C_starts (X: set A): (C X) =  Δ_(X) * (C X).
  Proof.
    have H2: inverse ( Δ_(X) * (C X)) = (C X) *  Δ_(X)
      by rewrite inverse_compose C_inverse DeltaE_inverse.
    have H4:  Δ_(X) * (C X) = ( Δ_(X) *(C X)).-1 .-1 by rewrite inverse_inverse.
    rewrite -{1}C_inverse H4 H2;apply inverse_eq, C_ends.
  Qed.
  
End CwCw_s_facts.

Section Cw_facts.
  (** * Properties of Cw *) 
  Lemma Cw_sym : @symmetric A Cw.
  Proof.
    apply C_sym.
  Qed.

  (* could be derived from below as Cw is a transitive closure *)
  Lemma Cw_transitive : Cw * Cw = Cw.
  Proof.
    apply C_transitive. 
  Qed.
  
  (* Equivalence relation on W *)
  Lemma Cw_reflexive_W: forall w, w \in W -> Cw (w, w).
  Proof.
    apply C_reflexive_W.
  Qed.
  
  Lemma Cw_as_clos_t: Cw =  (Δ_(W) `|`  Δ_(W) * Kw *  Δ_(W)).+.
  Proof.
    apply C_as_clos_t.
  Qed.
  
  (* XXXX utile ? *)
  Lemma Cw_n : forall (w w':A),
      w <> w' -> (Cw (w, w') <->  exists n, (iter (Δ_(W) * Kw * Δ_(W)) n.+1) (w, w')).
  Proof.
    apply C_n.
  Qed.
  
  Lemma Cw_inverse : Cw.-1 = Cw.
  Proof.
    apply C_inverse.
  Qed.
  
  Lemma Cw_ends : Cw = Cw *  Δ_(W).
  Proof.
    apply C_ends. 
  Qed.

  Lemma Cw_starts : Cw =  Δ_(W) * Cw.
  Proof.
    apply C_starts.
  Qed.
  
  Lemma Cw_Ewrt_Cw : (Cw * Ew.* * Cw) = Cw.
  Proof.
    rewrite -DuT_eq_Tstar -Ew_t_starts composeDl Delta_idem_r.
    rewrite {2}Cw_ends.
    have H1: Cw * Δ_(W) * (Δ_(W.^c) * Ew.+) =  Cw * (Δ_(W) * Δ_(W.^c)) * Ew.+
      by aac_reflexivity.
    rewrite H1 DeltaW_Wc DeltaC_compose_absorbr DeltaC_compose_absorbl.
    by rewrite DeltaC_union_idemr Cw_transitive.
  Qed.

  Lemma Fset_CW : forall (X: set A), Cw#(Clos( Cw#X | E,W))= Cw#X.
  Proof.
    by move => X; rewrite Fset_comp Fset_comp -/Ew Cw_Ewrt_Cw.
  Qed.
  
End Cw_facts.

Section Cw_s_facts.
    
  Lemma Cw_s_sym : @symmetric A Cw_s.
  Proof.
    apply C_sym. 
  Qed.

  (* could be derived from below as Cw_s is a transitive closure *)
  Lemma Cw_s_transitive : Cw_s * Cw_s = Cw_s.
  Proof.
    apply C_transitive.
  Qed.
  
  (* Equivalence relation on W *)
  Lemma Cw_s_reflexive_W: forall w, w \in W_s -> Cw_s (w, w).
  Proof.
    apply C_reflexive_W. 
  Qed.

  Lemma Cw_s_as_clos_t: Cw_s =  (Δ_(W_s) `|`  Δ_(W_s) * Kw *  Δ_(W_s)).+.
  Proof.
    apply C_as_clos_t. 
  Qed.
  
  (* XXXX utile ? *)
  Lemma Cw_s_n : forall (w w':A),
      w <> w' -> (Cw_s (w, w') <->  exists n, (iter (Δ_(W_s) * Kw * Δ_(W_s)) n.+1) (w, w')).
  Proof.
    apply C_n. 
  Qed.
  
  Lemma Cw_s_inverse : Cw_s.-1 = Cw_s.
  Proof.
    apply C_inverse. 
  Qed.
  
  Lemma Cw_s_ends : Cw_s = Cw_s *  Δ_(W_s).
  Proof.
    apply C_ends. 
  Qed.
  
  Lemma Cw_s_starts : Cw_s =  Δ_(W_s) * Cw_s.
  Proof.
    apply C_starts.
  Qed.
  
End Cw_s_facts.

Section Sw_facts.
  (** * Properties of Sw *)       

  Lemma Sw_inverse : Sw.-1 = Smw.
  Proof.
    rewrite /Sw inverse_union inverse_compose Cw_inverse inverse_union.
    by rewrite Kw_inverse /Bmw inverse_inverse DeltaE_inverse -/Smw.
  Qed.
  
End Sw_facts.

Section CBK_facts.
  (** * Properties of CBK *) 

  Lemma CBK_Clos: forall (X: set A), Cw#(Clos(CBK X | E,W ))= CBK X.
  Proof.
    by move => X; rewrite /CBK -Fset_comp Fset_CW.
  Qed.

  Lemma CBK_W: forall (X: set A), (CBK X) `<=` W.
  Proof.
    move => X x.
    rewrite /CBK Cw_starts -Fset_comp -Fset_comp Fset_DE. 
    by move => [H1 _]. 
  Qed.
  
End CBK_facts.

Section Aw_facts.
  (** * Properties of Aw *) 
  Lemma E_inc_Aw: E `<=` Aw.
  Proof.
    have H1: Aw = Bw `|` ('Δ `|` Bmw `|` Kw `|` Dw) by rewrite /Aw;aac_reflexivity.
    have H2: Bw `<=` Aw by rewrite H1;apply union_containsl.
    pose proof E_incl_Bw as H3.
    by apply subset_trans with Bw.
  Qed.

  Lemma Einv_inc_Aw: E.-1 `<=` Aw.
  Proof.
    have H1: Aw = Bmw `|` ('Δ `|` Bw `|` Kw `|` Dw) by rewrite /Aw;aac_reflexivity.
    have H2: Bmw `<=` Aw by rewrite H1;apply union_containsl.
    pose proof Einv_inc_Bmw as H3.
    by apply subset_trans with Bmw.
  Qed.

End  Aw_facts.

Section Aw_sp_facts.
  (** * Properties of Aw_sp *) 

  Lemma I1: E.-1 *Δ_(W.^c)* E `<=` Aw_sp.
  Proof.
    have H1: E.-1 *Δ_(W.^c)* E `<=`  Kw.
    pose proof E_incl_Bw as H1.
    rewrite /Kw /Bw /Bmw.
    have H2: E.-1 `<=` Bw.-1. by apply inverse_inc;rewrite /Bw.
    have H3: E.-1 * Δ_(W.^c) * E `<=` E.-1 * Δ_(W.^c) * Bw
      by apply compose_inc.
    have H4: E.-1 * Δ_(W.^c) * Bw `<=` Bmw * Δ_(W.^c) * Bw
      by apply composer_inc; apply composer_inc.
    by apply subset_trans with (E.-1 * Δ_(W.^c) * Bw).
    have H2: Kw `<=` Aw_sp.
    rewrite /Aw_sp.
    rewrite unionA unionC unionA.
    by apply union_containsl.
    by apply subset_trans with Kw.
  Qed.
  
  Lemma I3: E *Δ_(W.^c)* E `<=` Aw_sp.
  Proof.
    have H1: E *Δ_(W.^c)* E `<=` Bw by apply I3_1.
    have H2: Bw `<=` Aw_sp 
      by rewrite /Aw_sp unionA;apply union_containsl.
    
    by apply subset_trans with Bw.

  Qed.

End Aw_sp_facts.

Section Aw_sm_facts.
  (** * Properties of Aw_sm *) 

  
  Lemma I6: E *Δ_(W_s)* E.-1 `<=` Aw_sm.
  Proof.
    pose proof E_incl_Bw as H1.
    pose proof inverse_inc H1 as H2.
    have H3: E * Δ_(W_s) * E.-1 `<=` E * Δ_(W_s) * Bmw
      by apply compose_inc.
    have H4: E * Δ_(W_s) * Bmw `<=` Bw * Δ_(W_s) * Bmw
      by apply composer_inc; apply composer_inc.
    have H5: E *Δ_(W_s)* E.-1 `<=` Bw*Δ_(W_s)*Bmw
      by apply subset_trans with (E * Δ_(W_s) * Bmw).
    have H'1: Δ_(W_s) `<=` Cw_s by apply union_containsr.
    have H'2: Δ_(W_s) * Bmw `<=` Cw_s * Bmw by apply composer_inc.
    have H'3: Bw * Δ_(W_s) * Bmw `<=` Bw * Cw_s * Bmw
      by rewrite composeA composeA; apply compose_inc.
    have H'4: Bw * Cw_s * Bmw `<=` (Bw `|` Kw) * Cw_s * Bmw
      by apply composer_inc;apply composer_inc;apply union_containsl.
    have H'5: Bw * Δ_(W_s) * Bmw `<=` (Bw `|` Kw) * Cw_s * Bmw
      by apply subset_trans with (Bw * Cw_s * Bmw).
    have H'6: (Bw `|` Kw) * Cw_s * Bmw `<=` Bmw `|` (Bw `|` Kw) * Cw_s * Bmw
      by apply union_containsr.
    have H'7: Bw*Δ_(W_s)*Bmw `<=` Aw_sm
      by rewrite /Aw_sm;apply subset_trans with ((Bw `|` Kw) * Cw_s * Bmw).
    by apply subset_trans with (Bw*Δ_(W_s)*Bmw).
  Qed.

  Lemma I8: E.-1 *Δ_(W.^c)* E.-1 `<=` Aw_sm.
  Proof.
    have H1: E.-1 *Δ_(W.^c)* E.-1 `<=` Bmw.
    rewrite composeA -DeltaE_inverse 
            -[Δ_(W.^c).-1 * E.-1]inverse_compose -inverse_compose.
    by apply inverse_inc; apply I3_1.
    have H2: Bmw `<=` Aw_sm by apply union_containsl.
    by apply  subset_trans with Bmw.
  Qed.

End Aw_sm_facts.

