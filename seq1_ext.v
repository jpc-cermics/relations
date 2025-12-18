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

(** * This file in no more used
    it contains deployments which are not mandatory 
*) 

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot order.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import rel seq1. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

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
  
  Lemma ActiveOe_iff:  forall (E: relation T) (W: set T), ActiveOe W E = ActiveOe' W E.
  Admitted.
  
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
      by rewrite -ActiveOe_iff.
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
      have H8: stto [L\in]  (ActiveOe' W E) by rewrite -H7.
      rewrite -ActiveOe_iff in H8.
      move: H2 H3 H8;rewrite -H5 -H6 -H1 => H2 H3 H8.
      rewrite inP /D_U_a1 /mkset.
      have H9:  1 < size stto by rewrite H1.
      have H9':  0 < size stto by rewrite H1.
      have H10: stto [\in] (Oedge E)
        by move: H8;rewrite allset_I => /andP [H8 H8']; apply (@Rpath_L2 (T*T*O)).
  Admitted.
  (* 
     we need allL_I with intersection here to go from ActiveOe 
     to ChrelO 
      have H11: stto [L\in] ChrelO.

      rewrite /ActiveOe /A_tr in H8.
      ZZ
        by pose proof (@ActiveOe_ChrelO T);apply allset_subset with (ActiveOe W E);
        [apply ActiveOe_ChrelO |].
      have H12: stto [L\in] (A_tr W E)
        by apply allset_subset with (ActiveOe W E);[ rewrite /ActiveOe|].
      by rewrite /Eope H2 H3. 
  Qed.
*) 

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
