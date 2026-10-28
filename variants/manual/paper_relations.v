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

(** * without relation algebra tactices to solve goals *)
From AAC_tactics Require Import AAC.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import rel aacset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Parameter (T: Type) (W: set T) (E: relation T).

Section Papers_relations.

  (** * The relations used in the two papers  *)

  (* begin snippet Aw:: no-out *)  
  Definition Em := E^-1.
  Definition Ew := Δ_(W.^c) `;` E.
  Definition Bw := E `;` Ew.* .
  Definition Emw := Ew^-1. 
  Definition Bmw := Bw^-1.
  Definition Kw := (Bmw `;` Δ_(W.^c) `;` Bw).
  
  Definition DKD := ( Δ_(W) `;` Kw `;`  Δ_(W)).
  Definition Cw := ((DKD).+) `|` Δ_(W).
  Definition Dw := (Bw `|` Kw) `;` (Cw `;` (Bmw `|` Kw)).
  Definition Aw := 'Δ `|` Bw `|` Bmw `|` Kw `|` Dw.
  (* end snippet Aw *)  
  
  Definition W_s := fset E.* W.
  Definition DKD_s := ( Δ_(W_s) `;` Kw `;`  Δ_(W_s)).
  Definition Cw_s := (DKD_s.+) `|` Δ_(W_s).
  Definition Aw_s :=  'Δ `|` Bw `|` Bmw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` (Bmw `|` Kw).
  Definition Aw_sp := Bw `|` Kw `|` ((Bw `|` Kw) `;` Cw_s `;` Kw).
  Definition Aw_sm := Bmw `|` ((Bw `|` Kw) `;` Cw_s `;` Bmw).

  Definition Sw :=  'Δ `|` (Cw `;` (Bmw `|` Kw)).
  Definition Smw := 'Δ `|` ((Bw `|` Kw) `;` Cw).

  Definition CBK (X: set T) := (Cw `;` (Bmw `|` Kw))# X.

  Definition D (X: set T) := Δ_(X) `;` Kw `;`  Δ_(X).
  Definition C (X: set T) :=  (D X).+ `|` Δ_(X).

End Papers_relations.

Section Ew_facts.
  (** * Properties of Ew *) 

  Lemma Ew_t_starts: Δ_(W.^c) `;` Ew.+ = Ew.+ .
  Proof.
    by rewrite {1}/Ew  tclos_deltal
       -compA deltaK -tclos_deltal -/Ew.
  Qed.
  
  Lemma Emw_1 : Emw.* = Ew.* ^-1.
  Proof.
    by rewrite /Emw rtclosV.
  Qed.
  
End Ew_facts.
    
Section Bw_facts.
  (** * Properties of Bw *) 
  Lemma Bw_ends : Bw = Bw `;` Ew.*.
  Proof.
    by rewrite {2}/Bw compA rtclosK -/Bw.
  Qed.
      
  Lemma Bw_ends1 : Bw `;` Ew `<=` Bw.
  Proof.
    rewrite /Bw compA rtclos_compE.
    by apply compS; apply tclos_rtclosS.
  Qed.

  Lemma Bmw_starts : Bmw = (Emw.* `;` Bmw).
  Proof.
    by rewrite {2}/Bmw compV [Ew .*^-1]rtclosV -compA rtclosK
       -rtclosV -compV.
  Qed.

  Lemma E_incl_Bw : E `<=` Bw.
  Proof.
    by rewrite -[E]compx1; apply: compS; apply: delta_rtclosS.
  Qed.

  Lemma EDwE_in_Bw: E `;` Δ_(W.^c) `;` E `<=` Bw.
  Proof.
    rewrite /Bw /Ew.
    have H1: Δ_(W.^c) `;` E `<=` (Δ_(W.^c) `;` E).* .
    apply subset_trans with (Δ_(W.^c) `;` E).+ .
    apply tcl_sub.
    apply tclos_rtclosS.
    rewrite compA.
    by apply compS.
  Qed.
      
End Bw_facts. 

Section Bmw_facts.
  (** * Properties of Bmw *) 
  Lemma Einv_inc_Bmw: E^-1 `<=` Bmw.
  Proof.
    have H1: Bmw = (Emw.* `;` E^-1)
      by rewrite /Bmw /Bw /Emw /Ew compV rtclosV.
    by rewrite H1 -{1}[E^-1]comp1x;apply: compSl;
    apply: delta_rtclosS.
  Qed.
  
End Bmw_facts.

Section Kw_facts.
  (** * Properties of Kw *) 
  Lemma Kw_ends : Kw = Kw `;` Ew.*.
  Proof.
    by rewrite {2}/Kw compA -Bw_ends.
  Qed.

  Lemma Kw_ends1 : Kw `;` Ew `<=` Kw.
  Proof.
    pose proof Bw_ends1 as H1.
    have H2: (Bmw `;` Δ_(W.^c)) `;` (Bw `;` Ew) `<=` (Bmw `;` Δ_(W.^c)) `;` Bw
      by apply compS.
    by rewrite /Kw compA.
  Qed.
  
  Lemma Kw_starts : Kw = (Emw.* `;` Kw).
  Proof.
    by rewrite {2}/Kw -compA -compA -Bmw_starts.
  Qed.

  Lemma Kw_starts_ends: Kw = (Emw.* `;` Kw `;` Ew.* ).
  Proof.
    by rewrite -Kw_starts -Kw_ends.
  Qed.
  
  Lemma E9e : Kw = ((Emw).+ `;` Ew.+).
  Proof.
    have H1: (Δ_(W.^c) `;` (E `;` Ew .* )) = Ew.+ by rewrite -compA -/Ew comp_rtclosE.
    have H2: Ew^-1 = E^-1 `;` Δ_(W.^c) by rewrite  compV deltaV.
    have H3: E ^-1 `;` (Δ_(W.^c) `;` Ew .+) = Ew^-1 `;` Ew .+  by rewrite -compA H2.
    by rewrite /Kw /Bmw /Bw /Ew
       -{2}deltaK -/Ew compA compA
          H1 compV compA H3 -compA
       -compV  comp_rtclosE tclosV -/Emw.
  Qed.
  
  Lemma Kw_inverse: Kw^-1 = Kw.
  Proof.
    by rewrite E9e  -tclosV compV inverseK.
  Qed.
  
  Lemma Kw_sym : @symmetric T Kw.
  Proof.
    by apply invP, Kw_inverse.
  Qed.
  
  Lemma Dx_Kw_Dx_sym: forall (X: set T), @symmetric T (Δ_(X) `;` (Kw `;` Δ_(X))).
  Proof.
    move => X x y [z [H1 [z' [H2 H3]]]].
    apply delta_sym in H3;apply delta_sym in H1;apply Kw_sym in H2.
    by exists z';split; [ | exists z; split].
  Qed.
  
End Kw_facts.

Section DKD_facts.
  (** * Properties of DKD *)
  
  Lemma DKDsubCw: DKD `<=` Cw.
  Proof.
    have H1: DKD.+  `<=` Cw by apply: subsetUl.
    have H2: DKD `<=`  DKD.+ by rewrite -tclosUr; apply: subsetUl.
    by apply: subset_trans H2 H1.
  Qed.

End  DKD_facts.

Section CwCw_s_facts.
  (** * Properties of Cw and Cws *)   

  Lemma Dsym (X: set T): symmetric ( Δ_(X) `;` (Kw `;`  Δ_(X))).+ .
  Proof.
   by apply tclos_sym, Dx_Kw_Dx_sym.
  Qed.
  
  Lemma C_sym (X: set T) : symmetric (C X).
  Proof.
    have H1: symmetric (D X).+ by rewrite /D compA; apply Dsym.
    move => x y [ H2| [/= H3 H4]].
    by left; apply: H1.
    by right; split;[ rewrite /fst -H4 |].
  Qed.
  
  (* could be derived from below as Cw is a transitive closure *)
  Lemma C_transitive (X: set T) : (C X) `;` (C X) = (C X).
  Proof.
    rewrite {1 2}/C compUl compUr compUr deltaK.
    have -> : ((D X).+ `;` Δ_(X) =(D X).+)
      by rewrite {1}/D -tclos_deltar -/D.
    have -> : ( Δ_(X) `;` (D X).+ ) = (D X).+
      by rewrite {1}/D compA -tclos_deltal -compA -/D.
    have H1: ((D X).+ `;` (D X).+ `|` (D X).+ `|` ((D X).+ `|` Δ_(X)))
             = ((D X).+ `;` (D X).+ `|` ((D X).+ `|` (D X).+) `|` Δ_(X))
      by aac_reflexivity.
    rewrite H1 setUid.
    have H2: forall (T: relation T), ( T.+ `;` T.+ `<=` T.+)
        by move => T [x y] [z [/= H3 H4]];apply tclos_trans with z.
    have H3: ((D X).+ `;` (D X).+ `|` (D X).+ = (D X).+)
      by rewrite setUC; apply setUidPl.
    by rewrite H3.
  Qed.
  
  (* Equivalence relation on W *)
  Lemma C_reflexive_W (X: set T): forall w, X w -> (C X) (w, w).
  Proof.
    by move => w';rewrite /C /D;right.
  Qed.
  
  (* 
  Lemma C_as_Tclos (X: set T): (C X) =  (Δ_(X) `|` (Δ_(X) `;` Kw `;`  Δ_(X))).+.
  Proof.
    have H3: (Δ_(X)`;`Kw`;`Δ_(X)) `<=`(Δ_(X) `|` Δ_(X)`;`Kw`;`Δ_(X))  by apply: subsetUr.
    rewrite /C /D.
    rewrite predeqE => [[x' y']].
    split => [[[n H1 H2] | H2] | ];first by (exists n);[| apply: (iter_include H3)].
    by apply: tcl_sub; left.
    move => [n /= H1 H2 ].
  *)

  Lemma C_n (X: set T) : forall (w w': T),
      w <> w' -> ((C X) (w, w') <->  exists n, (Δ_(X) `;` Kw `;` Δ_(X))^(n.+1) (w, w')).
  Proof.
    rewrite /C /D; move => w w' H1; split => [[H3| [w1 H3] // ] | [n H3]].
    by apply: tclos_iterP.
    have H4: (Δ_(X) `;` Kw `;` Δ_(X))^(n.+1) `<=` (Δ_(X) `;` Kw `;` Δ_(X)).+
      by apply iterS_tclos.
    apply H4 in H3.
    by left.
  Qed.
  
  Lemma C_inverse (X: set T) : (C X)^-1 = (C X).
  Proof.
    by apply invP, C_sym.
  Qed.
  
  Lemma C_ends (X: set T): (C X) = (C X) `;`  Δ_(X).
  Proof.
    by rewrite compUl  deltaK -tclos_deltar.
  Qed.

  Lemma C_starts (X: set T): (C X) =  Δ_(X) `;` (C X).
  Proof.
    have H2: inverse ( Δ_(X) `;` (C X)) = (C X) `;`  Δ_(X)
      by rewrite compV C_inverse deltaV.
    have H4:  Δ_(X) `;` (C X) = ( Δ_(X) `;` (C X))^-1 ^-1 by rewrite inverseK.
    by rewrite -{1}C_inverse H4 H2 -invE -[RHS]C_ends.
  Qed.
  
End CwCw_s_facts.

Section Cw_facts.
  (** * Properties of Cw *) 
  Lemma Cw_sym : @symmetric T Cw.
  Proof.
    apply C_sym.
  Qed.

  (* could be derived from below as Cw is a transitive closure *)
  Lemma Cw_transitive : Cw `;` Cw = Cw.
  Proof.
    apply C_transitive. 
  Qed.
  
  (* Equivalence relation on W *)
  Lemma Cw_reflexive_W: forall w, W w -> Cw (w, w).
  Proof.
    apply C_reflexive_W.
  Qed.
  (* 
  Lemma Cw_as_clos_t: Cw =  (Δ_(W) `|` (Δ_(W) `;` Kw `;`  Δ_(W))).+.
  Proof.
    apply C_as_clos_t.
  Qed.
  *)
  Lemma Cw_n : forall (w w': T),
      w <> w' -> (Cw (w, w') <->  exists n, (Δ_(W) `;` Kw `;` Δ_(W))^(n.+1) (w, w')).
  Proof.
    apply C_n.
  Qed.
  
  Lemma Cw_inverse : Cw^-1 = Cw.
  Proof.
    apply C_inverse.
  Qed.
  
  Lemma Cw_ends : Cw = Cw `;`  Δ_(W).
  Proof.
    apply C_ends. 
  Qed.

  Lemma Cw_starts : Cw =  Δ_(W) `;` Cw.
  Proof.
    apply C_starts.
  Qed.
  
  Lemma Cw_Ewrt_Cw : (Cw `;` Ew.* `;` Cw) = Cw.
  Proof.
    rewrite rtclosE -Ew_t_starts compUr compx1.
    rewrite {2}Cw_ends.
    have H1: Cw `;` Δ_(W) `;` (Δ_(W.^c) `;` Ew.+) =  Cw `;` (Δ_(W) `;` Δ_(W.^c)) `;` Ew.+
      by aac_reflexivity.
    rewrite H1 deltaCr compx0 comp0x.
    by rewrite deltaCU0 Cw_transitive.
  Qed.

  Lemma Fset_CW : forall (X: set T), Cw#(Clos( Cw#X | E,W))= Cw#X.
  Proof.
    by move => X; rewrite fset_comp fset_comp -/Ew Cw_Ewrt_Cw.
  Qed.
  
End Cw_facts.

Section Cw_s_facts.
  (** * Properties of Cw_s *) 
  Lemma Cw_s_sym : @symmetric T Cw_s.
  Proof.
    apply C_sym. 
  Qed.

  (* could be derived from below as Cw_s is a transitive closure *)
  Lemma Cw_s_transitive : Cw_s `;` Cw_s = Cw_s.
  Proof.
    apply C_transitive.
  Qed.
  
  (* Equivalence relation on W *)
  Lemma Cw_s_reflexive_W: forall w, W_s w -> Cw_s (w, w).
  Proof.
    apply C_reflexive_W. 
  Qed.

  (*
  Lemma Cw_s_as_clos_t: Cw_s =  (Δ_(W_s) `|` (Δ_(W_s) `;` Kw `;`  Δ_(W_s))).+.
  Proof.
    apply C_as_clos_t. 
  Qed.
  *)

  Lemma Cw_s_n : forall (w w': T),
      w <> w' -> (Cw_s (w, w') <->  exists n, (Δ_(W_s) `;` Kw `;` Δ_(W_s))^(n.+1) (w, w')).
  Proof.
    apply C_n. 
  Qed.
  
  Lemma Cw_s_inverse : Cw_s^-1 = Cw_s.
  Proof.
    apply C_inverse. 
  Qed.
  
  Lemma Cw_s_ends : Cw_s = Cw_s `;`  Δ_(W_s).
  Proof.
    apply C_ends. 
  Qed.
  
  Lemma Cw_s_starts : Cw_s =  Δ_(W_s) `;` Cw_s.
  Proof.
    apply C_starts.
  Qed.
  
End Cw_s_facts.

Section Sw_facts.
  (** * Properties of Sw *)       

  Lemma Sw_inverse : Sw^-1 = Smw.
  Proof.
    rewrite /Sw invU compV Cw_inverse invU.
    by rewrite Kw_inverse /Bmw inverseK deltaV -/Smw.
  Qed.
  
End Sw_facts.

Section CBK_facts.
  (** * Properties of CBK *) 

  Lemma CBK_Clos: forall (X: set T), Cw#(Clos(CBK X | E,W ))= CBK X.
  Proof.
    by move => X; rewrite /CBK -fset_comp Fset_CW.
  Qed.

  Lemma CBK_W: forall (X: set T), (CBK X) `<=` W.
  Proof.
    move => X x.
    rewrite /CBK Cw_starts -fset_comp -fset_comp fset_deltaE. 
    by move => [H1 _]. 
  Qed.
  
End CBK_facts.

Section Aw_facts.
  (** * Properties of Aw *) 
  Lemma E_inc_Aw: E `<=` Aw.
  Proof.
    have H1: Aw = Bw `|` ('Δ `|` Bmw `|` Kw `|` Dw) by rewrite /Aw;aac_reflexivity.
    have H2: Bw `<=` Aw by rewrite H1;apply subsetUl.
    pose proof E_incl_Bw as H3.
    by apply subset_trans with Bw.
  Qed.

  Lemma Einv_inc_Aw: E^-1 `<=` Aw.
  Proof.
    have H1: Aw = Bmw `|` ('Δ `|` Bw `|` Kw `|` Dw) by rewrite /Aw;aac_reflexivity.
    have H2: Bmw `<=` Aw by rewrite H1;apply subsetUl.
    pose proof Einv_inc_Bmw as H3.
    by apply subset_trans with Bmw.
  Qed.

End  Aw_facts.

Section Aw_s_facts.
  (** * Properties of Aw *) 
  Lemma E_inc_Aw_s: E `<=` Aw_s.
  Proof.
    have H1: Aw_s = Bw `|` ( 'Δ `|` Bmw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` (Bmw `|` Kw))
      by rewrite /Aw_s;aac_reflexivity.     
    have H2: Bw `<=` Aw_s by rewrite H1;apply subsetUl.
    pose proof E_incl_Bw as H3.
    by apply subset_trans with Bw.
  Qed.

  Lemma Einv_inc_Aw_s: E^-1 `<=` Aw_s.
  Proof.
    have H1: Aw_s = Bmw `|` ( 'Δ `|` Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` (Bmw `|` Kw))
      by rewrite /Aw_s;aac_reflexivity.
    have H2: Bmw `<=` Aw_s by rewrite H1;apply subsetUl.
    pose proof Einv_inc_Bmw as H3.
    by apply subset_trans with Bmw.
  Qed.
  
End Aw_s_facts.

Section Aw_sp_facts.
  (** * Properties of Aw_sp *) 
  
  Lemma Awsp_L1: E^-1 `;` Δ_(W.^c) `;` E `<=` Aw_sp.
  Proof.
    pose proof E_incl_Bw as H1.
    have H2: E^-1 `<=` Bw^-1 by apply inverseS;rewrite /Bw.
    have H3: E^-1 `;` Δ_(W.^c) `;` E `<=` E^-1 `;` Δ_(W.^c) `;` Bw
      by apply compS.
    have H4: E^-1 `;` Δ_(W.^c) `;` Bw `<=` Bmw `;` Δ_(W.^c) `;` Bw
      by apply compSl; apply compSl.
    have H5: E^-1 `;` Δ_(W.^c) `;` E `<=`  Kw
      by apply subset_trans with (E^-1 `;` Δ_(W.^c) `;` Bw).
    have H6: Kw `<=` Aw_sp
      by rewrite /Aw_sp; rewrite -setUA setUC -setUA.
    
    by apply subset_trans with Kw.
  Qed.
  
  Lemma Awsp_L2: E `;` Δ_(W.^c) `;` E `<=` Aw_sp.
  Proof.
    have H1: E `;` Δ_(W.^c) `;` E `<=` Bw by apply EDwE_in_Bw.
    have H2: Bw `<=` Aw_sp 
      by rewrite /Aw_sp -setUA;apply subsetUl.
    
    by apply subset_trans with Bw.

  Qed.
  
End Aw_sp_facts.

Section Aw_sm_facts.
  (** * Properties of Aw_sm *) 
  
  Lemma Awsm_L1: E `;` Δ_(W_s) `;` E^-1 `<=` Aw_sm.
  Proof.
    pose proof E_incl_Bw as H1.
    pose proof inverseS H1 as H2.
    have H3: E `;` Δ_(W_s) `;` E^-1 `<=` E `;` Δ_(W_s) `;` Bmw
      by apply compS.
    have H4: E `;` Δ_(W_s) `;` Bmw `<=` Bw `;` Δ_(W_s) `;` Bmw
      by apply compSl; apply compSl.
    have H5: E `;` Δ_(W_s) `;` E^-1 `<=` Bw `;` Δ_(W_s) `;` Bmw
      by apply subset_trans with (E `;` Δ_(W_s) `;` Bmw).
    have H'1: Δ_(W_s) `<=` Cw_s by apply subsetUr.
    have H'2: Δ_(W_s) `;` Bmw `<=` Cw_s `;` Bmw by apply compSl.
    have H'3: Bw `;` Δ_(W_s) `;` Bmw `<=` Bw `;` Cw_s `;` Bmw
      by rewrite compA compA; apply compS.
    have H'4: Bw `;` Cw_s `;` Bmw `<=` (Bw `|` Kw) `;` Cw_s `;` Bmw
      by apply compSl;apply compSl;apply subsetUl.
    have H'5: Bw `;` Δ_(W_s) `;` Bmw `<=` (Bw `|` Kw) `;` Cw_s `;` Bmw
      by apply subset_trans with (Bw `;` Cw_s `;` Bmw).
    have H'6: (Bw `|` Kw) `;` Cw_s `;` Bmw `<=` Bmw `|` ((Bw `|` Kw) `;` Cw_s `;` Bmw)
      by apply subsetUr.
    have H'7: Bw `;` Δ_(W_s) `;` Bmw `<=` Aw_sm
      by rewrite /Aw_sm;apply subset_trans with ((Bw `|` Kw) `;` Cw_s `;` Bmw).
    by apply subset_trans with (Bw `;` Δ_(W_s) `;` Bmw).
  Qed.

  Lemma Awsm_L2: E^-1 `;` Δ_(W.^c) `;` E^-1 `<=` Aw_sm.
  Proof.
    have H1: E^-1 `;` Δ_(W.^c) `;` E^-1 `<=` Bmw.
    rewrite compA -deltaV
            -[Δ_(W.^c)^-1 `;` E^-1]compV -compV.
    by apply inverseS; apply EDwE_in_Bw.
    have H2: Bmw `<=` Aw_sm by apply subsetUl.
    by apply  subset_trans with Bmw.
  Qed.

End Aw_sm_facts.

(** already in E_incl_Bw *)
Lemma E9b1 : E `<=` Bw.
Proof.
  by rewrite -[E]compx1; apply: compS; apply: delta_rtclosS.
Qed.

(* Equation (9c) *)
Lemma E9c : Emw = E^-1 `;` Δ_(W.^c). 
Proof.
  by rewrite /Emw /Ew compV deltaV.
Qed.
  
(* Equation (9d) *)
Lemma E9d : Bmw = (Emw.* `;` E^-1).
Proof.
  by rewrite /Bmw /Bw /Emw /Ew compV rtclosV.
Qed.

Section Aw_sp_sm_facts.
  (** * Properties of Aw_sp *)   
  Lemma AwspE: (Aw_sp `;` Ew `<=` Aw_sp).
  Proof.
    pose proof Bw_ends1 as H1.
    pose proof Kw_ends1 as H2.
    have H3: (Bw `;` Ew `|` Kw `;` Ew `<=` Bw `;` Ew `|` Kw)
      by apply setUS.
    have H4: (Bw `;` Ew `|` Kw `<=` Bw `|` Kw)
      by apply setSU.
    have H5: (Bw `;` Ew `|` Kw `;` Ew `<=` Bw `|` Kw)
      by apply subset_trans with (Bw `;` Ew `|` Kw).
    have H6: (Bw `;` Ew `|` Kw `;` Ew 
                `|` (Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew `<=` Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew)
      by apply setSU.
    have H7: ((Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew `<=` (Bw `|` Kw) `;` Cw_s `;` Kw)
      by rewrite compA; apply compS.
    have H8: (Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew `<=` Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` Kw).
    by apply setUS.
    
    rewrite /Aw_sp. 
    rewrite compUl [((Bw `|` Kw) `;` Ew)]compUl.
    by apply subset_trans with (Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew).
  Qed.
  (** * Properties of Aw_sm *)   
  Lemma AwsmDE: (Aw_sm `;` Δ_(W.^c) `;` E^-1 `<=` Aw_sm).
  Proof.
    have H1: (Bmw `;` Δ_(W.^c) `;` E^-1 `<=` Bmw).
    rewrite /Bmw /Bw /Ew.
    rewrite -deltaV compV rtclosV compV.
    rewrite deltaV deltaV.
    pose R:= E^-1 `;` Δ_(W.^c). 
    rewrite -/R [R.* `;` E^-1 `;` Δ_(W.^c)]compA -/R. 
    rewrite rtclos_compE.
    apply compSl.
    apply tclos_rtclosS.
    
    pose R:= Δ_(W.^c) `;` E^-1.
    rewrite compA -/R.
    rewrite compA -/R in H1.
    rewrite /Aw_sm.
    pose S:= ((Bw `|` Kw) `;` Cw_s).
    rewrite -/S.
    rewrite compUl.
    have H2: (Bmw `;` R `|` S `;` Bmw `;` R `<=` Bmw `|` S `;` Bmw `;` R)
      by apply setSU. 
    have H3: (Bmw `|` S `;` Bmw `;` R `<=` Bmw `|` S `;` Bmw)
      by apply setUS; rewrite compA; apply compS.
    by apply subset_trans with (Bmw `|` S `;` Bmw `;` R).
  Qed.

End Aw_sp_sm_facts.

Section Key_Lemma_W_s.
  
  Lemma Ws_L1: forall (n: nat) (S R V: relation T) (X: set T),
      (V `;` ( Δ_(X) `;` S `;` R `;` V `;` Δ_(X))^(n.+1) `;` S =
         (V `;` Δ_(X) `;` S `;` R)^(n.+1) `;` (V `;` Δ_(X) `;` S)).
  Proof.
    move => n S R V X.
    have Ws_L4: (V `;` (Δ_(X) `;` S `;` R `;` V `;` Δ_(X))^(n.+1) = 
                  (V `;` Δ_(X) `;` S `;` R)^(n.+1) `;` V `;` Δ_(X)).
    elim: n => [| n' H]; 
              first by rewrite /iter 
                         -!['Δ `;` (_)]compA comp1x comp1x -!compA.
    rewrite /iter -/iter; rewrite /iter -/iter in H.
    rewrite -compA H compA. 
    rewrite -[Δ_( X) `;` (Δ_( X) `;` S `;` R `;` V `;` Δ_( X))]compA.
    rewrite -[Δ_( X) `;` (Δ_( X) `;` S `;` R `;` V)]compA.
    rewrite -[Δ_( X) `;` (Δ_( X) `;` S `;` R)]compA.
    rewrite -[Δ_( X) `;` (Δ_( X) `;` S)]compA.
    by rewrite deltaK -!compA.
    (* *)
    by rewrite Ws_L4 -[_ `;` (V `;` Δ_( X) `;` S)]compA -[_ `;` (V `;` Δ_( X))]compA.
  Qed.
  
  Lemma Ws_L2: forall (n: nat) (S R V: relation T) (X Y: set T),
      V `;` Δ_(X) `;` S = V `;` Δ_(Y) `;` S 
      -> (V `;` (Δ_(X) `;` S `;` R `;` V `;` Δ_(X))^(n.+1) `;` S)
        = (V `;` (Δ_(Y) `;` S `;` R `;` V `;` Δ_(Y))^(n.+1)) `;` S.
  Proof.
    move => n S R V X Y H.
    have H1: (V `;` (Δ_(X) `;` S `;` R `;` V `;` Δ_(X))^(n.+1)) `;` S
             = (V `;` Δ_(X) `;` S `;` R)^(n.+1) `;` (V `;` Δ_(X) `;` S).
    by apply: Ws_L1.
    by rewrite H in H1;rewrite -Ws_L1 in H1.
  Qed.

  Lemma Ws_L3: forall (S R V: relation T) (X Y: set T),
      V `;` Δ_(X) `;` S = V `;` Δ_(Y) `;` S 
      ->  (V `;` ((Δ_(X) `;` S `;` R `;` V `;` Δ_(X)).+) `;` S
          = V `;` (Δ_(Y) `;` S `;` R `;` V `;` Δ_(Y)).+ `;` S ).
  Proof.
    by move => S R V X Y H;apply: tclos_iterE; move => n; apply: Ws_L2.
  Qed.

End Key_Lemma_W_s.

Lemma BwKw_ends : Bw `|` Kw = (Bw `|` Kw) `;` Ew.* .
Proof.
  by rewrite compUl -Bw_ends -Kw_ends.
Qed.

Lemma BmKw_starts : Bmw `|` Kw = (Emw.* `;` (Bmw `|` Kw )).
Proof.
  by rewrite compUr -Bmw_starts -Kw_starts.
Qed.


  Section Tcs_Lemma14. 
    (** * Lemma 14 of Tcs *)
    Lemma L14_E38a : (Emw.* `;` Ew.* ) =
                       ('Δ `|` (Δ_(W.^c) `;` Bw) `|` (Bmw `;` Δ_(W.^c)) `|` Kw).
    Proof.
      have L14_E38a1 : Ew.+ = Δ_(W.^c) `;` Bw                            
        by rewrite /Bw -compA -/Ew comp_rtclosE.
      have L14_E38a2 : Emw.+ = Bmw `;` Δ_(W.^c)
        by rewrite -tclosV L14_E38a1 compV -/Bmw deltaV.
      by rewrite rtclos_compE1 !compUl !compUr !compx1 !comp1x setUA -E9e;
      rewrite -L14_E38a2 -L14_E38a1.
    Qed.

    Lemma L14_E38b : Cw `;` (Emw.* ) `;` (Ew .* ) = Cw `;` ('Δ `|` (Bmw `;` Δ_(W.^c)) `|` Kw).
    Proof.
      have H1: ( Δ_(W) `;` (Δ_(W.^c) `;` Bw)) = 'Δc
        by rewrite -compA deltaCr comp0x.
      rewrite compA L14_E38a {1}Cw_ends compA !compUr H1.
      rewrite compx0.
      rewrite !compx1 -Cw_ends.
      rewrite -compA -Cw_ends.
      rewrite -{1}compA -{1}compA -{1}compA -Cw_ends.
      by rewrite deltaCU0.
    Qed.

    (** * Equation (E38c) *)
    Local Lemma L14_E38c1 : (Cw `;` (Emw.* ) `;` (Ew.* )) `;` Cw  = Cw `;` ((Δ_(W) `|` Kw `;` Δ_(W)) `;` Cw).
    Proof.
      have H1: Δ_(W.^c) `;` Cw = 'Δc
        by rewrite Cw_starts -compA deltaCl comp0x.
      have H2: Bmw `;` Δ_(W.^c) `;` Cw = 'Δc
        by rewrite compA H1 compx0.
      have H3:  Δ_(W) `;` Cw `|` Kw `;` ( Δ_(W) `;` Cw) = ( Δ_(W) `|` Kw `;`  Δ_(W)) `;` Cw
        by rewrite -[(Kw) `;` (_ `;` _)]compA -compUl.
      by rewrite L14_E38b compA compUl compUl H2 deltaCU0 comp1x
           {2 3}Cw_starts H3.
    Qed.
    
    Local Lemma L14_E38c2 : forall (R: relation T), 
        R = R `;`  Δ_(W) -> (R.+ `;`  Δ_(W) = R.+).
    Proof.
      by move => R H1;rewrite {2}H1 [RHS]tclos_deltar -H1. 
    Qed.

    Local Lemma L14_E38c3 : forall (R: relation T), 
        R =  Δ_(W) `;` R ->  Δ_(W) `;` R.+ = R.+.
    Proof.
      by move => R H1;rewrite {2}H1 [RHS]tclos_deltal -H1. 
    Qed.
    
    Local Lemma L14_E38c4 : forall (R: relation T), 
        R = R `;`  Δ_(W) -> R =  Δ_(W) `;` R -> ( Δ_(W) `|` R.+) `;` ( Δ_(W) `|` R) = ( Δ_(W) `|` R.+).
    Proof. 
      move => R H1 H2.
      rewrite compUl !compUr deltaK -H2.
      rewrite L14_E38c2 //. 
      rewrite -setUA [in (R `|` _)]setUA [in (R `|` _)]setUC.
      rewrite -[in (R .+ `|` R `|` R .+ `;` R)]setUA.
      rewrite tclosUr. 
      by rewrite setUid.
    Qed.

    Local Lemma L14_E38c5 : forall (R: relation T), 
        R = R `;`  Δ_(W) -> R =  Δ_(W) `;` R -> ( Δ_(W) `|` R.+) `;` ( Δ_(W) `|` R.+) = ( Δ_(W) `|` R.+).
    Proof.
      move => R H1 H2.
      rewrite compUl !compUr deltaK.
      rewrite L14_E38c2 // L14_E38c3 //.
      by rewrite tclosU_comp -setUA setUid.
    Qed.
    
    (** * Equation (E38c) *)
    Lemma L14_E38c : (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Cw  = Cw. 
    Proof.
      have H1: DKD `;`  Δ_(W) = DKD
        by rewrite /DKD compA deltaK.
      have H2:  Δ_(W) `;` DKD = DKD
        by rewrite /DKD -compA -compA deltaK.
      rewrite L14_E38c1.
      rewrite {1}Cw_ends.
      rewrite compA. 
      rewrite -{1}[in ( Δ_(W) `;` (( Δ_(W) `|` Kw `;`  Δ_(W)) `;` Cw))]compA. 
      rewrite [in  Δ_(W) `;` ( Δ_(W) `|` Kw `;`  Δ_(W))]compUr.
      rewrite deltaK.
      rewrite -[in  Δ_(W) `;` (Kw `;`  Δ_(W))]compA.
      rewrite /Cw -/DKD. 
      rewrite [in (DKD .+ `|`  Δ_(W))]setUC.
      rewrite -compA. 
      by rewrite L14_E38c4; first by rewrite L14_E38c5. 
    Qed.
    
    (** * Equation (E38d) *)
    Lemma L14_E38d : (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Δ_(W.^c)  = Cw `;` (Bmw `|` Kw)  `;` Δ_(W.^c).
    Proof.
      rewrite L14_E38b. 
      rewrite Cw_ends.
      rewrite compA [in( 'Δ `|` Bmw `;` Δ_(W.^c) `|` Kw) `;` Δ_(W.^c)]compUl.
      rewrite [in ('Δ `|` Bmw `;` Δ_(W.^c)) `;` Δ_(W.^c)]compUl.
      rewrite [in  Bmw `;` Δ_(W.^c) `;` Δ_(W.^c)]compA deltaK.
      rewrite [in LHS]compA compUr [in ( Δ_(W) `;` _)]compUr.
      rewrite comp1x deltaCr  deltaC0U. 
      rewrite -[in ( Δ_(W) `;` _ `|`  Δ_(W) `;` _)]compUr.
      rewrite -[in (_ `;` Δ_(W.^c) `|` _ `;` Δ_(W.^c))]compUl.
      rewrite -[in LHS]compA -Cw_ends.
      by rewrite -compA.
    Qed.

    (** * Equation (E38e) *)
    Lemma L14_E38e : Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw = Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw.
    Proof.
      have H0 : forall (R: relation T), 
          (Δ_(W.^c) `;` R `;` Cw)^-1 = Cw `;` R^-1 `;` Δ_(W.^c)
          by move => R; rewrite compV  compV
                         Cw_inverse deltaV compA.
      have H1: inverse (Emw .* ) = (Ew .* )
        by rewrite rtclosV /Emw inverseK.
      have H2 : (Emw.* `;` Ew.* )^-1 = (Emw.* `;` Ew.* )
        by rewrite -H1; apply comp_invVV. 
      have H3 : (Bw `|` Kw)^-1 = (Bmw `|` Kw)
        by rewrite invU Kw_inverse.
      have H4 : (Δ_(W.^c) `;` ((Emw .* ) `;` (Ew .* )) `;` Cw)^-1
                =  (Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw)^-1
        by rewrite [LHS]H0 [RHS]H0 H2 H3 -[RHS]L14_E38d -compA. 
      by apply invE in H4.
    Qed.
    
    (** * Lemma 14 *)
    Lemma  L14:
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
    
  End Tcs_Lemma14. 

  Section Lemma_15.
    Lemma L15_a : (Δ_(W.^c) `;` Emw.* `;` Ew.* `;` Δ_(W.^c))
                  = (Δ_(W.^c) `;` ('Δ `|` Bw `|` Bmw `|` Kw) `;` Δ_(W.^c)).
    Proof.
      have H1: (Δ_(W.^c) `;` Emw.* `;` Ew.* `;` Δ_(W.^c)) =
                 (Δ_(W.^c) `;` ( Emw.* `;` Ew.* ) `;` Δ_(W.^c))
        by aac_reflexivity.
      have H2:  (Δ_(W.^c) `;` (Bmw `;` Δ_(W.^c)) `;` Δ_(W.^c))
                = (Δ_(W.^c) `;` Bmw `;` (Δ_(W.^c) `;` Δ_(W.^c)))
        by aac_reflexivity.
      rewrite H1 L14_E38a compUr compUr compUr compx1.
      rewrite -[Δ_(W.^c) `;` (Δ_(W.^c) `;` Bw)]compA deltaK.
      rewrite compUl compUl compUl  deltaK.
      rewrite H2  deltaK.
      rewrite [in RHS]compUr [in RHS]compUr [in RHS]compUr compx1.
      rewrite [in RHS]compUl [in RHS]compUl [in RHS]compUl deltaK.
      by [].
    Qed.
    
    Lemma L15_b:  (Δ_(W.^c) `;` ((Bw `|` Kw) `;` Cw) `;` Emw.* `;` Ew.* `;` Δ_(W.^c))
                  = (Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw) `;` Δ_(W.^c)).
    Proof.
      have H1 : (Δ_(W.^c) `;` ((Bw `|` Kw) `;` Cw) `;` Emw.* `;` Ew.* `;` Δ_(W.^c) )
                = (Δ_(W.^c) `;` (Bw `|` Kw) `;` (Cw `;` Emw.* `;` Ew.* `;` Δ_(W.^c)) )
        by aac_reflexivity.
      rewrite H1 L14_E38d.
      by aac_reflexivity.
    Qed.
    
    Lemma L15_c: (Δ_(W.^c) `;` Emw.* `;` Ew.* `;` (Cw `;` (Bmw `|` Kw)) `;` Δ_(W.^c))
                 = (Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw) `;` Δ_(W.^c)).
    Proof.
      have H1: (Δ_(W.^c) `;` Emw.* `;` Ew.* `;` (Cw `;` (Bmw `|` Kw)) `;` Δ_(W.^c))
               = ((Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw) `;` (Bmw `|` Kw) `;` Δ_(W.^c))
        by aac_reflexivity.
      by rewrite H1 L14_E38e.
    Qed.
    
    Lemma L15_d: (Δ_(W.^c) `;` ((Bw `|` Kw) `;` Cw) `;` Emw.* `;` Ew.* `;` (Cw `;` (Bmw `|` Kw))
                                                               `;` Δ_(W.^c))
                 =Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw) `;` Δ_(W.^c).
    Proof.
      have H1:  (Δ_(W.^c) `;` ((Bw `|` Kw) `;` Cw) `;` Emw.* `;` Ew.* `;` (Cw `;` (Bmw `|` Kw))
                                                              `;` Δ_(W.^c)) =
                  (Δ_(W.^c) `;` (Bw `|` Kw) `;` ((Cw `;` Emw.* `;` Ew.* ) `;` Cw) `;` 
                     (Bmw `|` Kw) `;` Δ_(W.^c)) 
        by aac_reflexivity.
      by rewrite H1 L14_E38c.
    Qed.
    (** * Lemma 15 Equation (39) *) 
    Lemma L15: (Δ_(W.^c) `;` Smw `;`  Emw.* `;` Ew.* `;` Sw `;` Δ_(W.^c))
               = Δ_(W.^c) `;` Aw `;`  Δ_(W.^c).
    Proof.
      rewrite /Smw /Sw compUr compUr !compUl !compx1.
      rewrite -[(Bw `;` Cw `|` Kw `;` Cw)]compUl.
      rewrite -[(DKD.+ `;` (Bmw `|` Kw) `|` Δ_(W) `;` (Bmw `|` Kw))]compUl -/Cw.
      (* now we have 4 terms as in the math proof *)
      rewrite L15_d L15_b L15_c L15_a setUid -setUA setUid.
      rewrite -compUl. 
      have H1: (Δ_(W.^c) `;` ('Δ `|` Bw `|` Bmw `|` Kw) `|`
                  Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw))
               = (Δ_(W.^c) `;` ('Δ `|` Bw `|` Bmw `|` Kw)  `|`
                    Δ_(W.^c) `;` ((Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw)))
        by aac_normalise.
      rewrite H1 -compUr /Aw /Dw.
      by aac_reflexivity.
    Qed.

  End Lemma_15.

  Section Appendix_D_L16. 

    Lemma D_L16_E42a :  Aw_s = 'Δ `|` Aw_sp `|`  Aw_sm.
    Proof.
      rewrite /Aw_s [Bmw `|` Kw]setUC  compUr.
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
      have H: Bmw = 'Δ `;` Bmw by rewrite comp1x.
      set R1 := (Bw `|` Kw) `;` Cw_s .
      rewrite {1}[Bmw]H -compUl. 
      set R2 := ('Δ `|` R1) `;` Bmw `;` Δ_( W .^c).
      have H1: (R2 `;` E) `<=` (R2 `;` Bw) by  apply: compS;apply: E9b1.
      suff H2: (R2 `;` Bw) `<=` Aw_sp by apply: subset_trans H1 H2.
      rewrite /R2 compA compA.
      rewrite -[(Bmw `;` (_ `;` Bw))]compA -/Kw compUl. 
      rewrite comp1x /R1 /Aw_sp -[Bw `|` Kw `|` _]setUA.
      by apply: subsetUr.
    Qed.
    
    Lemma D_L16_E42c :  (Aw_sp `;` Δ_(W_s) `;` Em) `<=`  Aw_sm.
    Proof.
      have E21c1: E^-1 `<=` Bmw
        by rewrite E9d -{1}[E^-1]comp1x;apply: compSl;
        apply: delta_rtclosS.
      have E21c2: Δ_(W_s) `<=` Cw_s by rewrite /Cw_s;apply: subsetUr.
      have H1: (Δ_(W_s) `;` E^-1) `<=` (Cw_s `;` E^-1) by apply compSl; apply: E21c2.
      have H2: (Cw_s `;` E^-1) `<=` (Cw_s `;` Bmw) by apply compS; apply: E21c1.
      have E21c3: (Δ_(W_s) `;` E^-1) `<=` (Cw_s `;` Bmw) by apply: subset_trans H1 H2.
      have E21c4: ((Bw `|` Kw) `;` Δ_(W_s) `;` E^-1) `<=` ((Bw `|` Kw) `;` (Cw_s) `;` Bmw)
        by rewrite [_ `;` _ `;` E^-1]compA [_ `;` _ `;` Bmw]compA;
        apply: compS; apply: E21c3.
      have H3: ((Bw `|` Kw) `;` Cw_s `;` Bmw) `<=`  Aw_sm 
        by rewrite /Aw_sm; apply: subsetUr.
      have H4: ((Bw `|` Kw) `;` Δ_( W_s) `;` Em) `<=` Aw_sm 
        by apply: subset_trans E21c4 H3.
      have E21c5: Cw_s `;` Δ_(W_s) = Cw_s
        by rewrite {1}/Cw_s compUl -tclos_deltar deltaK -/Cw_s.
      have E21c6: forall (R S: relation T), (S `;` R = R) -> ((R.+ `|` S) `;` R) = (R.+)
          by move => R S H; rewrite compUl H setUC tclosUr.
      have E21c7: Cw_s `;` Kw `;` Δ_(W_s) = (Δ_( W_s) `;` Kw `;` Δ_( W_s)) .+ 
        by rewrite -{1}E21c5 {1}/Cw_s compA compA 
           -[Δ_( W_s) `;` (Kw `;` Δ_( W_s))]compA;
        apply: E21c6;rewrite -compA -compA {1}deltaK.
      have E21c8: (Cw_s `;` Kw `;` Δ_(W_s)) `<=` Cw_s 
        by rewrite E21c7 /Cw_s;apply: subsetUl.
      have H1': (((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s)) `;` E^-1) `<=` (((Bw `|` Kw) `;` Cw_s) `;` E^-1)
        by apply: compSl;rewrite compA compA;apply: compS;
        rewrite -compA;apply E21c8.
      have H2': (((Bw `|` Kw) `;` Cw_s) `;` E^-1) `<=` (((Bw `|` Kw) `;` Cw_s) `;` Bmw)
        by apply: compS; apply: E21c1.
      have E21c9: ((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s) `;` E^-1) `<=` ((Bw `|` Kw) `;` Cw_s `;` Bmw)
        by apply: subset_trans H1' H2'.
      have H5: ((Bw `|` Kw) `;` Cw_s `;` Kw `;` Δ_(W_s) `;` Em) `<=` Aw_sm
        by apply:  subset_trans E21c9 H3.
      by rewrite /Aw_sp compUl compUl subUset;split.
    Qed.
    
  End Appendix_D_L16. 
