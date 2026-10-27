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

(** * using relation algebra tactices to solve goals *)
From AAC_tactics Require Import AAC.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import rel aacset.

(* ---- instrumentation ra_probe (genere par probe/ra_probe.py) ---- *)
(* "x ^+" (itr, RelationAlgebra) masque "x ^+ n" (natexp, mathcomp) *)
Set Warnings "-notation-incompatible-prefix".
From RL Require Import rel_ra.
Set Warnings "notation-incompatible-prefix".
Local Open Scope classical_set_scope.

Ltac ra_unfold := idtac.

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

Ltac ra_unfold ::= cbv beta delta [Em Ew Bw Emw Bmw Kw DKD Cw Dw Aw W_s DKD_s Cw_s Aw_s Aw_sp Aw_sm Sw Smw CBK D C].

(** from paper_tcs_facts *)

Tactic Notation "ra_probe" string(s) :=
  first
  [ assert_succeeds (solve [timeout 20 rka]);                  idtac "RAP" s "ka"
  | assert_succeeds (solve [timeout 20 rkat]);                 idtac "RAP" s "kat"
  | assert_succeeds (solve [timeout 20 rka_cnv]);              idtac "RAP" s "ka_cnv"
  | assert_succeeds (solve [timeout 20 rkat_cnv]);             idtac "RAP" s "kat_cnv"
  | assert_succeeds (solve [timeout 20 rlattice]);             idtac "RAP" s "lattice"
  | assert_succeeds (solve [timeout 40 rhkat]);                idtac "RAP" s "hkat"
  | assert_succeeds (solve [ra_unfold; timeout 20 rka]);       idtac "RAP" s "U+ka"
  | assert_succeeds (solve [ra_unfold; timeout 20 rkat]);      idtac "RAP" s "U+kat"
  | assert_succeeds (solve [ra_unfold; timeout 20 rka_cnv]);   idtac "RAP" s "U+ka_cnv"
  | assert_succeeds (solve [ra_unfold; timeout 20 rkat_cnv]);  idtac "RAP" s "U+kat_cnv"
  | assert_succeeds (solve [ra_unfold; timeout 40 rhkat]);     idtac "RAP" s "U+hkat"
  | idtac "RAP" s "-" ].
(* ---- fin instrumentation ---- *)

Lemma  L14_E1: (Emw.* `;` Ew.* ) = ('Δ `|` (Δ_(W.^c) `;` Bw) `|` (Bmw `;` Δ_(W.^c)) `|` Kw).
Proof. by ra_unfold;rkat_cnv. Qed.

Lemma  L14_E2:  Cw `;` (Emw .* ) `;` (Ew .* ) = Cw `;` ('Δ `|` Bmw `;` Δ_(W.^c) `|` Kw).
Proof. by ra_unfold;rkat_cnv. Qed.

Lemma  L14_E3:  (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Cw  = Cw .
Proof. by ra_unfold;rkat_cnv. Qed.

Lemma  L14_E4:  (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Δ_(W.^c)  = Cw `;` (Bmw `|` Kw)  `;` Δ_(W.^c).
Proof. by ra_unfold;rkat_cnv. Qed.

Lemma  L14_E5:  Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw = Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw.
Proof. by ra_unfold;rkat_cnv. Qed.


Section Ew_facts.
  (** * Properties of Ew *) 

  Lemma Ew_t_starts: Δ_(W.^c) `;` Ew.+ = Ew.+ .
  Proof. (* ok with: by ra_unfold;rkat. Qed. *)
    by rewrite {1}/Ew  tclos_deltal
       -compA deltaK -tclos_deltal -/Ew.
  Qed.
  
  Lemma Emw_1 : Emw.* = Ew.* ^-1.
  Proof. (* ok with:  by rka_cnv. Qed. *)
  by rewrite /Emw rtclosV.
  Qed.

End Ew_facts.
    
Section Bw_facts.
  (** * Properties of Bw *) 
  Lemma Bw_ends : Bw = Bw `;` Ew.*.
  Proof. (* ok with: by ra_unfold;rka. Qed. *)
    by rewrite {2}/Bw compA rtclosK -/Bw. 
  Qed.
  
  Lemma Bw_ends1 : Bw `;` Ew `<=` Bw.
  Proof. (* ok with: by ra_unfold;rka. Qed. *)
    rewrite /Bw compA rtclos_compE.
    by apply compS; apply tclos_rtclosS.
  Qed.
  
  Lemma Bmw_starts : Bmw = (Emw.* `;` Bmw).
  Proof. (* ok with: by ra_unfold;rka_cnv. Qed. *)
    by rewrite {2}/Bmw compV [Ew .*^-1]rtclosV -compA rtclosK
       -rtclosV -compV.
  Qed.
  
  Lemma E_incl_Bw : E `<=` Bw.
  Proof. (* ok with: by ra_unfold;rka. Qed. *)
    by rewrite -[E]compx1; apply: compS; apply: delta_rtclosS.
  Qed.
  
  Lemma EDwE_in_Bw: E `;` Δ_(W.^c) `;` E `<=` Bw.
  Proof. by ra_unfold;rka. Qed.
      
End Bw_facts. 

Section Bmw_facts.
  (** * Properties of Bmw *) 

  Lemma Einv_inc_Bmw: E^-1 `<=` Bmw.
  Proof. by ra_unfold;rka_cnv. Qed.
    
End Bmw_facts.

Section Kw_facts.
  (** * Properties of Kw *) 
  Lemma Kw_ends : Kw = Kw `;` Ew.*.
  Proof. (* ok with:  by ra_unfold;rka. Qed. *)
  by rewrite {2}/Kw compA -Bw_ends.
  Qed.

  Lemma Kw_ends1 : Kw `;` Ew `<=` Kw.
  Proof. by ra_unfold;rka. Qed.
  
  Lemma Kw_starts : Kw = (Emw.* `;` Kw).
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
    by rewrite {2}/Kw -compA -compA -Bmw_starts.
  Qed.
  
  Lemma Kw_starts_ends: Kw = (Emw.* `;` Kw `;` Ew.* ).
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
    by rewrite -Kw_starts -Kw_ends.
  Qed.
  
  Lemma E9e : Kw = ((Emw).+ `;` Ew.+).
  Proof. by ra_unfold;rkat_cnv. Qed.

  Lemma Kw_inverse: Kw^-1 = Kw.
  Proof. (* ok with: by ra_unfold;rka_cnv. Qed. *)
    by rewrite E9e  -tclosV compV inverseK.
  Qed.

  Lemma Kw_sym : @symmetric T Kw.
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
    by apply invP, Kw_inverse.
  Qed.
  
  Lemma Dx_Kw_Dx_sym: forall (X: set T), @symmetric T (Δ_(X) `;` (Kw `;` Δ_(X))).
  Proof. by ra_unfold;rka_cnv. Qed.
  
End Kw_facts.

Section DKD_facts.
  (** * Properties of DKD *)
  
  Lemma DKDsubCw: DKD `<=` Cw.
  Proof. by ra_unfold;rka. Qed.

End  DKD_facts.

Section CwCw_s_facts.
  (** * Properties of Cw and Cws *)   

  Lemma Dsym (X: set T): symmetric ( Δ_(X) `;` (Kw `;`  Δ_(X))).+ .
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
     by apply tclos_sym, Dx_Kw_Dx_sym.
  Qed.
  
  Lemma C_sym (X: set T) : symmetric (C X).
  Proof. by ra_unfold;rka_cnv. Qed.
  
  (* could be derived from below as Cw is a transitive closure *)
  Lemma C_transitive (X: set T) : (C X) `;` (C X) = (C X).
  Proof. by ra_unfold;rkat. Qed.
  
  (* Equivalence relation on W *)
  Lemma C_reflexive_W (X: set T): forall w, X w -> (C X) (w, w).
  Proof. by move => w';rewrite /C /D;right. Qed.
  
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
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
    by apply invP, C_sym.
  Qed.

  Lemma C_ends (X: set T): (C X) = (C X) `;`  Δ_(X).
  Proof. (* ok with:  by ra_unfold;rkat. Qed. *)
    by rewrite compUl  deltaK -tclos_deltar.
  Qed.
  
  Lemma C_starts (X: set T): (C X) =  Δ_(X) `;` (C X).
  Proof. by ra_unfold;rkat. Qed.
  
End CwCw_s_facts.

Section Cw_facts.
  (** * Properties of Cw *) 
  Lemma Cw_sym : @symmetric T Cw.
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
    by apply C_sym.
  Qed.
  
  (* could be derived from below as Cw is a transitive closure *)
  Lemma Cw_transitive : Cw `;` Cw = Cw.
  Proof.  (* ok with:  by ra_unfold;rkat. Qed. *)
     apply C_transitive. 
  Qed.
  
  (* Equivalence relation on W *)
  Lemma Cw_reflexive_W: forall w, W w -> Cw (w, w).
  Proof. (* ok with:  by apply C_reflexive_W. Qed. *)
      apply C_reflexive_W.
  Qed.
  
  Lemma Cw_n : forall (w w': T),
      w <> w' -> (Cw (w, w') <->  exists n, (Δ_(W) `;` Kw `;` Δ_(W))^(n.+1) (w, w')).
  Proof. by  apply C_n. Qed.
  
  Lemma Cw_inverse : Cw^-1 = Cw.
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
    apply C_inverse.
  Qed.
  
  Lemma Cw_ends : Cw = Cw `;`  Δ_(W).
  Proof. (* ok with:  by ra_unfold;rkat. Qed. *)
    apply C_ends. 
  Qed.
  
  Lemma Cw_starts : Cw =  Δ_(W) `;` Cw.
  Proof. (* ok with:  by ra_unfold;rkat. Qed. *)
    apply C_starts.
  Qed.
  
  Lemma Cw_Ewrt_Cw : (Cw `;` Ew.* `;` Cw) = Cw.
  Proof. by ra_unfold;rkat. Qed.
  
  Lemma Fset_CW : forall (X: set T), Cw#(Clos( Cw#X | E,W))= Cw#X.
  Proof. (* ok with:  by ra_unfold;rkat. Qed. *)
  by move => X; rewrite fset_comp fset_comp -/Ew Cw_Ewrt_Cw.
  Qed.
  
End Cw_facts.

Section Cw_s_facts.
  (** * Properties of Cw_s *) 
  Lemma Cw_s_sym : @symmetric T Cw_s.
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
      apply C_sym. 
  Qed.
  
  (* could be derived from below as Cw_s is a transitive closure *)
  Lemma Cw_s_transitive : Cw_s `;` Cw_s = Cw_s.
  Proof. (* ok with:  by ra_unfold;rkat. Qed. *)
      apply C_transitive.
  Qed.
  
  (* Equivalence relation on W *)
  Lemma Cw_s_reflexive_W: forall w, W_s w -> Cw_s (w, w).
  Proof. (* ok with:  by apply C_reflexive_W. Qed. *)
      apply C_reflexive_W. 
  Qed.
  
  Lemma Cw_s_n : forall (w w': T),
      w <> w' -> (Cw_s (w, w') <->  exists n, (Δ_(W_s) `;` Kw `;` Δ_(W_s))^(n.+1) (w, w')).
  Proof. by apply C_n. Qed.
  
  Lemma Cw_s_inverse : Cw_s^-1 = Cw_s.
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
     apply C_inverse. 
  Qed.

  Lemma Cw_s_ends : Cw_s = Cw_s `;`  Δ_(W_s).
  Proof.  (* ok with:  by ra_unfold;rkat. Qed. *)
        apply C_ends. 
  Qed.
  
  Lemma Cw_s_starts : Cw_s =  Δ_(W_s) `;` Cw_s.
  Proof. (* ok with:  by ra_unfold;rkat. Qed. *)
        apply C_starts.
  Qed.

End Cw_s_facts.

Section Sw_facts.
  (** * Properties of Sw *)       

  Lemma Sw_inverse : Sw^-1 = Smw.
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
      rewrite /Sw invU compV Cw_inverse invU.
    by rewrite Kw_inverse /Bmw inverseK deltaV -/Smw.
  Qed.
 
End Sw_facts.

Section CBK_facts.
  (** * Properties of CBK *) 

  Lemma CBK_Clos: forall (X: set T), Cw#(Clos(CBK X | E,W ))= CBK X.
  Proof. (* ok with:  by ra_unfold;rkat. Qed. *)
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
  Proof. by ra_unfold;rka. Qed.

  Lemma Einv_inc_Aw: E^-1 `<=` Aw.
  Proof. by ra_unfold;rka_cnv. Qed.
    
End  Aw_facts.

Section Aw_s_facts.
  (** * Properties of Aw *) 
  Lemma E_inc_Aw_s: E `<=` Aw_s.
  Proof. by ra_unfold;rka_cnv. Qed.

  Lemma Einv_inc_Aw_s: E^-1 `<=` Aw_s.
  Proof. by ra_unfold;rka_cnv. Qed.
  
End Aw_s_facts.

Section Aw_sp_facts.
  (** * Properties of Aw_sp *) 
  
  Lemma Awsp_L1: E^-1 `;` Δ_(W.^c) `;` E `<=` Aw_sp.
  Proof. by ra_unfold;rka_cnv. Qed.
  
  Lemma Awsp_L2: E `;` Δ_(W.^c) `;` E `<=` Aw_sp.
  Proof. by ra_unfold;rka. Qed.
  
End Aw_sp_facts.

Section Aw_sm_facts.
  (** * Properties of Aw_sm *) 
  
  Lemma Awsm_L1: E `;` Δ_(W_s) `;` E^-1 `<=` Aw_sm.
  Proof. by ra_unfold;rka_cnv. Qed.
  
  Lemma Awsm_L2: E^-1 `;` Δ_(W.^c) `;` E^-1 `<=` Aw_sm.
  Proof. by ra_unfold;rka_cnv. Qed.

End Aw_sm_facts.

(** already in E_incl_Bw *)
Lemma E9b1 : E `<=` Bw.
Proof. (* ok with:  by ra_unfold;rka. Qed. *)
  by rewrite -[E]compx1; apply: compS; apply: delta_rtclosS.
Qed.

(* Equation (9c) *)
Lemma E9c : Emw = E^-1 `;` Δ_(W.^c). 
Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
    by rewrite /Emw /Ew compV deltaV.
Qed.
 
(* Equation (9d) *)
Lemma E9d : Bmw = (Emw.* `;` E^-1).
Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
  by rewrite /Bmw /Bw /Emw /Ew compV rtclosV.
Qed.

Section Aw_sp_sm_facts.
  (** * Properties of Aw_sp *)   
  Lemma AwspE: (Aw_sp `;` Ew `<=` Aw_sp).
  Proof. by ra_unfold;rka. Qed.

  (** * Properties of Aw_sm *)   
  Lemma AwsmDE: (Aw_sm `;` Δ_(W.^c) `;` E^-1 `<=` Aw_sm).
  Proof. by ra_unfold;rka_cnv. Qed.

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

Section BwKw.

  Lemma BwKw_ends : Bw `|` Kw = (Bw `|` Kw) `;` Ew.* .
  Proof. (* ok with:  by ra_unfold;rka. Qed. *)
  by rewrite compUl -Bw_ends -Kw_ends.
Qed.

  Lemma BmKw_starts : Bmw `|` Kw = (Emw.* `;` (Bmw `|` Kw )).
  Proof. (* ok with:  by ra_unfold;rka_cnv. Qed. *)
  by rewrite compUr -Bmw_starts -Kw_starts.
Qed.

End BwKw.


