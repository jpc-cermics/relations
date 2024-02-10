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

From RL Require Import  seq1 ssrel rel erel3 aacset paper_relations paper_csbr_rel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(* begin snippet dsepnota *)  
Notation "( x [⊥d] y | W )" := (D_separated W E x y).
(* end snippet dsepnota *)

(** * some Lemmas for the paths part *)
  
Section utilities.
  (** * Lifto properties should be moved *)
  Lemma BmwBw_ht: forall (p:seq A) (x y:A) (o:O),
      Active_path W E (Lifto (x::(rcons p y)) o) x y
      -> Oedge E (x,head y p, o) /\ Oedge E (last x p,y,o).
  Proof.
    move => p x y o H1.
    pose proof H1 as H2.
    rewrite Lifto_crc in H1.
    rewrite -rcons_cons Lifto_rcc in H2.
    split. 
    by pose proof Active_path_c_hto H1 as [_ [_ [H3 _]]].
    by pose proof Active_path_rc_hto H2 as [_ [_ [H4 _]]].
  Qed.
  
  Lemma Kw_ht: forall (p q:seq A) (x y t:A),
      Active_path W E ((Lifto (x::(rcons p t)) N)++(Lifto (t::(rcons q y)) P )) x y
      -> Oedge E (x,head t p, N) /\ Oedge E (last t q,y,P).
  Proof.
    move => p q x y t.
    have H1: Lifto (x::(rcons p t)) N = rcons (Lifto (x::p) N) (last x p,t,N)
      by rewrite -rcons_cons Lifto_rcc.
    have H2: Lifto (t::(rcons q y)) P = (t,(head y q),P)::(Lifto (rcons q y) P)
      by rewrite Lifto_crc.
    rewrite H1 H2 => H3. 
    apply Active_path_split in H3 as [H3 [H4 H5]].
    pose proof Active_path_rc_hto H3 as [H6 [H7 [H8 H9]]].
    pose proof Active_path_c_hto H4 as [H10 [H11 [H12 H13]]].
    rewrite Lifto_head1 in H9.
    rewrite Lifto_last1 in H13.
    by []. 
  Qed.
  
End utilities.

Section Bw_implies_active_path.
  
  (** * Lemma 10 (33a) *)
  Lemma Bwpath: forall (x y:A),
      Bw (x,y) -> (exists (p: seq A),
                   Active_path W E (Lifto (x::(rcons p y)) P) x y
                   /\ p [\in] (Ew.+)#_(y)).
  Proof.
    rewrite /Bw -DuT_eq_Tstar /mkset .
    move => x y [x1 [/= H1 [/Delta_Id <- | H2]]];first by (exists [::]).
    pose proof (clos_t_to_paths_l H2) as [p [H3 [H4 H5]]].
    exists (x1::p);split. 
    apply Deployment_to_Active_path.
    split. by []. 
    rewrite /R_o allL_c H4 andbT. by apply mem_set.
    by [].
  Qed.
  
  (** simplified version for right composition *)
  Lemma Bwpath_1: forall (x y:A),
      Bw (x,y) -> exists (p : seq (Eo A O)) (y':A),
        Active_path W E (rcons p (y',y,P)) x y /\ Oedge E (y',y,P).
  Proof.
    move => x y H1.
    pose proof Bwpath H1 as [p [H2 _]].
    rewrite -rcons_cons Lifto_rcc in H2.
    pose proof Active_path_rc_hto H2 as [_ [_ [H5 _]]].
    by exists (Lifto (x :: p) P), (last x p).
  Qed.
  
  Lemma Bwpath': forall (x y:A),
      (Bw (x, y)) /\ W.^c x -> (exists (p: seq A),
                                Active_path W E (Lifto (x::(rcons p y)) P) x y
                                /\ (x::p) [\in] (Ew.+)#_(y)).
  Proof.
    move => x y [[x1 [H1 H2]] H3]. 
    have H4: Ew.+ (x, y) by rewrite -r_clos_rt_clos_t;exists x1;split;[exists x;split | ].
    pose proof clos_t_to_paths_l H4 as [p [H5 [H6 H7]]]. 
    move: H5 => /allset_cons [H5 H5'].
    by exists p;split;[ apply Deployment_to_Active_path |].
  Qed.
  
End Bw_implies_active_path.

Section Bmw_implies_active_path.

  (** * Lemma 10 (33b) *)
  Lemma Bmwpath: forall (x y:A),
      Bmw (x, y) -> (exists (p: seq A), Active_path W E (Lifto (x::(rcons p y)) N) x y
                               /\ p [\in] (Ew.+)#_(x)).
  Proof.
    rewrite /Bmw /inverse /Bw -DuT_eq_Tstar.
    move => x y [x1 [/= H1 [/Delta_Id <- | H2]]];first by (exists [::]).
    pose proof (clos_t_to_paths_l H2) as [p [H3 [H4 H5]]].  
    apply allL_rev in H4.
    move: H3 => /allset_cons [H3 H3'].
    exists (rcons (rev p) x1); split.
    apply Deployment_to_Active_path.
    split. 
    by rewrite allset_rcons -allset_rev.
    by rewrite /R_o allL_rev rev_rcons revK inverse_inverse allL_c;
    apply/andP; split;[apply mem_set| rewrite allL_rev].
    by rewrite allset_rev rev_rcons revK.
  Qed.
  
  (** simplified version for composition *)
  Lemma Bmwpath_1: forall (x y:A),
      Bmw (x, y) -> exists (p : seq (Eo A O)) (x':A),
        Active_path W E ((x,x',N)::p) x y /\ Oedge E (x,x',N).
  Proof.
    move => x y H1.
    pose proof Bmwpath H1 as [p [H2 _]].
    rewrite Lifto_crc in H2.
    pose proof Active_path_c_hto H2 as [_ [_ [H5 _]]].
    by exists (Lifto (rcons p y) N), (head y p).
  Qed.
  
  Lemma Bmwpath': forall (x y:A),
      Bmw (x, y) /\ W.^c y -> 
      (exists (p: seq A), Active_path W E (Lifto (x::(rcons p y)) N) x y
                     /\ (rcons p y) [\in] (Ew.+)#_(x)).
  Proof.
    move => x y [[x1 [H1 H2]] H3]. 
    have H4: Ew.+ (y, x) by rewrite -r_clos_rt_clos_t;exists x1;split;[exists y;split | ].
    pose proof clos_t_to_paths_l H4 as [p [H6 [H7 H8]]].
    move: H6 => /allset_cons [H6 H6'].
    apply allL_rev in H7.
    (exists (rev p));rewrite -Deployment_to_Active_path -rev_cons.
    by rewrite -2!allset_rev /R_o. 
  Qed.

End Bmw_implies_active_path.

Section Kw_implies_active_path.

  (** * Lemma 10 (33c) *)  
  Lemma Kwpath: forall (x y:A),
      Kw (x, y) -> (exists (p q: seq A),exists t,
                      Active_path W E 
                        ((Lifto (x::(rcons p t)) N)++(Lifto (t::(rcons q y)) P )) x y
                      /\ (rcons p t) [\in] (Ew.+)#_(x)
                      /\ (t::q) [\in] (Ew.+)#_(y)).
  Proof.
    move => x y [z [ [t [H2 [/= H3 <-]]] /= H4]]. 
    pose proof (Bmwpath' (conj H2 H3)) as [p [H5 H6]].
    pose proof (Bwpath' (conj H4 H3)) as [q [H7 H8]].
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
  
  Lemma Kwpath_1: forall (x y:A),
      Kw (x,y) ->  exists (p : seq (Eo A O)) (x' y':A),
        Active_path W E ((x,x',N)::(rcons p (y',y,P))) x y
        /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof.
    move => x y H1.
    pose proof Kwpath H1 as [p [q [t [H2 _]]]].
    pose proof @Lift_o_start_end A p q x y t as [x' [y' [r H3]]].
    rewrite H3 in H2. clear H3.
    pose proof Active_path_crc_a H2 as [[H3 _] [_ [H4 _]]].
    by exists r, x', y'.
  Qed.

End Kw_implies_active_path.

Section Cw_s_implies_active_path.
  (* we do not use Cw_s but use the fact that 
   * Cw_s := (DKD_s.+) + Δ_(W_s) 
   * and we consider (DKD_s.+) and  Δ_(W_s) separately
   *)

  Lemma BwKw_path1: forall (x y:A),
      let R:=(Bw `|` Kw) in R (x, y) -> exists (p : seq (Eo A O)) (y':A),
          Active_path W E (rcons p (y',y,P)) x y /\ Oedge E (y',y,P).
  Proof.
    move => x y H1 [H2 | H2].
    by apply Bwpath_1.
    pose proof Kwpath_1 H2 as [p [x' [y' [H3 [_ H5]]]]].
    exists ((x,x',N)::p), y'.
    by rewrite rcons_cons.
  Qed.

  Lemma BmwKw_path1: forall (x y:A),
      let R:=(Bmw `|` Kw) in R (x,y) -> exists (p : seq (Eo A O)) (x':A),
          Active_path W E ((x,x',N)::p) x y /\ Oedge E (x,x',N).
  Proof.
    move => x y H1 [H2 | H2].
    by apply Bmwpath_1.
    pose proof Kwpath_1 H2 as [p [x' [y' [H3 [H4 _]]]]].
    by exists (rcons p (y',y,P)), x'.
  Qed.
  
  (* Lemma 10 (33d) *)  
  Lemma Kwcomp: forall (x y:A),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s)) `;` (Δ_(W_s) `;` Kw `;` Δ_(W_s))
      in R (x, y)
         -> exists (p q: seq (Eo A O)), exists (x' y':A),
          Active_path W E q x y
          /\ q = (x,x',N)::(rcons p (y',y,P)) /\ Oedge E (x,x',N) /\Oedge E (y',y,P).
  Proof. 
    
    move => x y' R [z' [[z [[x' [[/= H1 /= <-] H2]] [/= H3 /= <-]]] H3']].
    move: H3' =>  [y [[v [[_ /= <-] H4]] [H5 /= <-]]].
    pose proof Kwpath H2 as [p1 [q1 [t1 [H6 [H7 H8]]]]].
    pose proof Kwpath H4 as [p2 [q2 [t2 [H9 [H10 H11]]]]].
    pose proof (Lift_o_start_end p1 q1 x z t1) as [x1 [z1 [r1 H12]]].
    pose proof (Lift_o_start_end p2 q2 z y t2) as [z2 [y2 [r2 H13]]].
    rewrite H12 in H6.
    rewrite H13 in H9.
    pose proof Active_path_crc_a H6 as [[H14' _] [_ [H14 _]]].
    pose proof Active_path_crc_a H9 as [[H15' _] [_ [H15 _]]].
    pose p := ((x, x1, N) :: rcons r1 (z1, z, P)). 
    pose q := ((z, z2, N) :: rcons r2 (y2, y, P)).
    exists ((rcons r1 (z1,z,P)) ++ (z,z2,N)::r2),(p ++ q), x1, y2.
    split. 
    apply Active_path_cat' with z.
    split;[ exists ((x, x1, N) :: r1), (rcons r2 (y2, y, P)), (z1, z, P), (z, z2, N) | ].
    by [].
    by rewrite /p /q; split. 
    by split;[ rewrite !rcons_cat | ].
  Qed.
  
  Lemma Kwcomp_1: forall (x y:A),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s))
      in R (x, y)
         -> exists (p q: seq (Eo A O)), exists (x' y':A),
          Active_path W E q x y
          /\ q = (x,x',N)::(rcons p (y',y,P)) /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof. 
    move => x y' R [z [[xx1 [[H1 /= <-] H2]] [H3 /= <-]]].
    pose proof Kwpath H2 as [p1 [q1 [t1 [H6 [H7 H8]]]]].
    pose proof (Lift_o_start_end p1 q1 x z t1) as [x1 [z1 [r1 H12]]].
    rewrite H12 in H6.
    pose proof Active_path_crc_a H6 as [[H14' _] [_ [H14 _]]].
    by exists r1, ((x, x1, N) :: rcons r1 (z1, z, P)), x1, z1.
  Qed.
  
  Lemma Kwcomp_n: forall (n: nat) (x y:A),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s))^(n.+1) 
      in R (x, y)
         -> exists (p q: seq (Eo A O)), exists (x' y':A),
          Active_path W E q x y
          /\ q = (x,x',N)::(rcons p (y',y,P)) /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof. 
    elim. 
    - by rewrite iter1_id; apply Kwcomp_1.
    - move => n Hn x y.
      rewrite -addn1 iter_compose.
      move => R [z [H1 H5]].
      move: H1 => /Hn [r1 [p [x1 [z1 [H1 [H2 [H3 H4]]]]]]].
      rewrite iter1_id in H5.
      have H5': W_s z by move: H5 => [z' [[z'' [[H'1 _] _]] _]].
      move: H5 => /Kwcomp_1 [r2 [q [z2 [y2 [H5 [H6 [H7 H8]]]]]]].
      exists ((rcons r1 (z1,z,P)) ++ (z,z2,N)::r2),(p ++ q), x1, y2.
      split. 
      by apply Active_path_cat' with z;
      split;[exists ((x, x1, N) :: r1), (rcons r2 (y2, y, P)), (z1, z, P), (z, z2, N) | ].
      by split;[rewrite H2 H6 !rcons_cat rcons_cons | split].
  Qed.
  
  Lemma Kwcomp_tc: forall (x y:A),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s)).+
      in R (x, y)
         -> exists (p q: seq (Eo A O)), exists (x' y':A),
          Active_path W E q x y
          /\ q = (x,x',N)::(rcons p (y',y,P)) /\ Oedge E (x,x',N) /\ Oedge E (y',y,P).
  Proof.
    move => x y H1 H2.
    pose proof clos_t_iterk H2 as [n H3].
    by apply Kwcomp_n with n.
  Qed.

  Lemma Kwcomp_tc2: forall (x y:A),
      let R:= (Δ_(W_s) `;` Kw `;` Δ_(W_s)).+
      in R (x, y) ->  W_s x /\ W_s y.
  Proof.
    move => x y H1 H2.
    rewrite /H1 in H2.
    pose proof H2 as H3.
    rewrite Delta_clos_trans_ends in H2.
    move: H2 => [y' [_ [H2 /= <-]]].
    rewrite composeA Delta_clos_trans_starts in H3.
    move: H3 => [z' [[H3 _] _]].
    by [].
  Qed.
  
End Cw_s_implies_active_path.

Section Aw_s_implies_active_path.

  (** * Lemma 11 *)
  Lemma Aw_s_path:  forall (x y:A),
      Aw_s (x, y) -> exists (p : seq (Eo A O)), Active_path W E p x y.
  Proof.
    move => x y [[[[/Delta_Id -> | H2] | H2] | H2] | H3].
    - by (exists [::]).
    - pose proof Bwpath H2 as [p [H3 H4]]. 
      by (exists (Lifto (x :: rcons p y) P)).
    - pose proof Bmwpath H2 as [p [H3 H4]]. 
      by (exists (Lifto (x :: rcons p y) N)).
    - pose proof Kwpath H2 as  [p [t [H3 [H4 [H5 H6]]]]]. 
      by (exists (Lifto (x :: rcons p H3) N ++ Lifto (H3 :: rcons t y) P)).
    - move:H3 => [z [[t [H3 H4]] H5]].
      move: H4;rewrite /Cw_s; move => [H4 | H4].
      + rewrite /DKD_s in H4.
        pose proof BwKw_path1 H3 as [p1 [y' [H6 Ho1]]].
        pose proof Kwcomp_tc H4 as [p2 [p3 [t' [z' [H7 [H8 [Ho2 Ho3]]]]]]].
        pose proof BmwKw_path1 H5 as [p4 [z'' [H9 Ho4]]].
        pose proof Kwcomp_tc2 H4 as [H10 H11].
        have H12: ActiveOe W E ((y', t, P), (t, t', N)) by [].
        have H13: ActiveOe W E ((z', z, P),(z, z'', N)) by [].
        have H14: Active_path W E
                    (rcons p1 (y', t, P) ++ (t, t', N)::(rcons p2 (z', z, P)))
                    x z
          by apply Active_path_cat with t;rewrite -H8.
        exists ((rcons p1 (y', t, P) ++ (t, t', N) :: rcons p2 (z', z, P)) ++ ((z, z'', N) :: p4)).
        rewrite -rcons_cons -rcons_cat.
        apply Active_path_cat with z.
        rewrite rcons_cat rcons_cons.
        by [].
      + move: H4 => [H1 /= H4]. rewrite -H4 in H5. clear H4.
        pose proof BwKw_path1 H3 as [p1 [y' [H6 Ho1]]].
        pose proof BmwKw_path1 H5 as [p4 [t' [H9 Ho4]]].
        have H12: ActiveOe W E ((y', t, P), (t, t', N)) by [].
        exists ((rcons p1 (y', t, P))++ ((t, t', N) :: p4)).
        by apply Active_path_cat with t.
  Qed.

  Lemma L11:  forall (x y:A),
      Aw (x, y) -> exists (p : seq (Eo A O)), Active_path W E p x y.
  Proof.
    by move => x y;rewrite L9;apply Aw_s_path.
  Qed.
  
  Proposition P12: forall (x y:A), Aw (x, y) -> ~ ( x [⊥d] y | W ).
  Proof.
    by move => x y /L11 H1 H2.
  Qed.
  
End Aw_s_implies_active_path.

Section Active_path_implies_Aw_s.
  
  (** * From active paths to Active relation *)
  
  Lemma Active_path_l2: forall (o1 o2:O) (x y t:A), 
      Active_path W E [::(x,t,o1);(t,y,o2)] x y
      -> ( ((let R:= E.-1 `;` Δ_(W.^c) `;` E in R (x, y))
            \/ (let R:= E `;` Δ_(W.^c) `;` E in R (x, y)))
           /\ o2 = P) 
         \/ 
           ( ((let R:= E `;` Δ_(W_s) `;` E.-1 in R (x, y))
              \/ (let R:= E.-1 `;` Δ_(W.^c) `;` E.-1 in R (x, y)))
             /\ o2 = N).
  Proof.
    move => o1 o2 x y t. 
    elim: o2 => [|] [H1 [H2 H3]].
    - elim: o1 H1 H3 => [|] _ /= /allL0' [/= H5 [H6 [_ H8]]].  
      by left;split;[right; exists t;split;[exists t| ] | ].
      by left;split;[left; exists t;split;[exists t| ] | ].
    - elim: o1 H1 H3 => [|] _ /= /allL0' [/= H5 [H6 [_ H8]]]. 
      by right;split;[left; exists t;split;[exists t| ] | ].
      by right;split;[right; exists t;split;[exists t| ] | ].
  Qed.
  
  
  Lemma Active_path_l2_1: forall (o1 o2:O) (x y t:A), 
      Active_path W E [::(x,t,o1);(t,y,o2)] x y
      -> ( Aw_sp (x, y) /\ o2 = P) \/ ( Aw_sm (x, y) /\ o2 = N).
  Proof.
    move => o1 o2 x y t H1.
    pose proof Active_path_l2 H1 as [[H2 H3 ] |[H2 H3]].
    by left;move: H2 => [H2 | H2];[split;[apply I1|] |split;[apply I3|]].
    by right;move: H2 => [H2 | H2];[split;[apply I6|] |split;[apply I8|]].
  Qed.

  (* Definition Aw_sp := Bw + Kw + ((Bw + Kw) `;` Cw_s `;` Kw). *)
  
  Lemma Last1: (Aw_sp `;` Ew `<=` Aw_sp).
  Proof.
    pose proof Bw_ends1 as H1.
    pose proof Kw_ends1 as H2.
    have H3: (Bw `;` Ew `|` Kw `;` Ew `<=` Bw `;` Ew `|` Kw)
      by apply union_inc_l.
    have H4: (Bw `;` Ew `|` Kw `<=` Bw `|` Kw)
      by apply union_inc_r.
    have H5: (Bw `;` Ew `|` Kw `;` Ew `<=` Bw `|` Kw)
      by apply subset_trans with (Bw `;` Ew `|` Kw).
    have H6: (Bw `;` Ew `|` Kw `;` Ew 
             `|` (Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew `<=` Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew)
      by apply union_inc_r.
    have H7: ((Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew `<=` (Bw `|` Kw) `;` Cw_s `;` Kw)
      by rewrite composeA; apply compose_inc.
    have H8: (Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew `<=` Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` Kw).
    by apply union_inc_l.
    
    rewrite /Aw_sp. 
    rewrite composeDr [((Bw `|` Kw) `;` Ew)]composeDr.
    by apply subset_trans with (Bw `|` Kw `|` (Bw `|` Kw) `;` Cw_s `;` Kw `;` Ew).
  Qed.
  
  Lemma Last2: (Aw_sp `;` Δ_(W_s) `;` E.-1 `<=` Aw_sm).
  Proof.
    by apply L8_E29c.
  Qed.
  
  Lemma Last3: (Aw_sm `;` Δ_(W.^c) `;` E `<=` Aw_sp).
  Proof.
    by apply L8_E29b.
  Qed.
  
  Lemma Last4: (Aw_sm `;` Δ_(W.^c) `;` E.-1 `<=` Aw_sm).
  Proof.
    have H1: (Bmw `;` Δ_(W.^c) `;` E.-1 `<=` Bmw).
    rewrite /Bmw /Bw /Ew.
    rewrite -DeltaE_inverse inverse_compose inverse_star inverse_compose.
    rewrite DeltaE_inverse DeltaE_inverse.
    pose R:= E.-1 `;` Δ_(W.^c). 
    rewrite -/R [R.* `;` E.-1 `;` Δ_(W.^c)]composeA -/R. 
    rewrite clos_rt_r_clos_t.
    apply composer_inc.
    apply clos_t_clos_rt.
    
    pose R:= Δ_(W.^c) `;` E.-1.
    rewrite composeA -/R.
    rewrite composeA -/R in H1.
    rewrite /Aw_sm.
    pose S:= ((Bw `|` Kw) `;` Cw_s).
    rewrite -/S.
    rewrite composeDr.
    have H2: (Bmw `;` R `|` S `;` Bmw `;` R `<=` Bmw `|` S `;` Bmw `;` R)
      by apply union_inc_r.
    have H3: (Bmw `|` S `;` Bmw `;` R `<=` Bmw `|` S `;` Bmw)
      by apply union_inc_l; rewrite composeA; apply compose_inc.
    by apply subset_trans with (Bmw `|` S `;` Bmw `;` R).
  Qed.
  
  Lemma L13: forall (n: nat) (p : seq (Eo A O)) (x y:A), 
      size (p) = n.+2 
      -> Active_path W E p x y
      -> exists (q: seq (Eo A O)) (o: O) (y':A),
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
      pose proof Active_path_cc_a H2 as [H7 [H8 [H9 H10]]].
      rewrite /ChrelO /mkset /fst /snd in H9.
      rewrite H9 H5 H6 in H2 *.
      exists [:: (u, v, o1)],o2,z.
      split; first by [].
      pose proof Active_path_l2_1 H2 as [H11 | H11].
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
      have H10: exists (r : seq (Eo A O)) (o : O) (y' : A),
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
        move: H7 => [/= H15 [H16 [/ChrelO_eq H17  H18]]].
        rewrite H17 in H4 *.
        split. 
        by [].
        rewrite H14 in H2 H18 H15 *.
        rewrite H17 in H15 H2 H18 H12 *.
        clear H8 H9 r H4 H17 H2 H14 y' o H1 H3 q.
        elim: o2 H16 H18 => [ H1 H2 | H1 H2].
        ++ have H3: (Aw_sp `;` Δ_(W.^c) `;` E) (x, t) by (exists z);split;[exists z | ].
           by rewrite composeA in H3;left;split;[apply Last1 |].
        ++ have H3: (Aw_sp `;` Δ_(W_s) `;` E.-1) (x, t) by (exists z);split;[exists z | ].
           by right;split;[apply Last2|].
      + move: H11 => /rcons_inj [_ _ H14];rewrite H13 in H14;clear H13.
        exists (rcons q (u, v, o1)),o2, v.
        move: H7 => [/= H15 [H16 [/ChrelO_eq H17  H18]]].
        rewrite H17 in H4 *.
        split. 
        by [].
        rewrite H14 in H2 H18 H15 *.
        rewrite H17 in H15 H2 H18 H12 *.
        clear H8 H9 r H4 H17 H2 H14 y' o H1 H3 q.
        elim: o2 H16 H18 => [ H1 H2 | H1 H2].
        ++ have H3: (Aw_sm `;` Δ_(W.^c) `;` E) (x, t) by (exists z);split;[exists z | ].
           by left;split;[apply Last3 |].
        ++ have H3: (Aw_sm `;` Δ_(W.^c) `;` E.-1) (x, t) by (exists z);split;[exists z | ].
           by right;split;[apply Last4 |].
  Qed.
  
  Lemma Active_path_to_Active: 
    forall (x y:A), (exists (p : seq (Eo A O)), Active_path W E p x y) -> Aw (x, y).
  Proof.
    move => x y [p H1].
    elim: p H1 => [ H1 | [[x1 y1] o1] p _ ];
                 (* p = [::]*)first by rewrite L9 L8_E29a;left;left;rewrite Delta_Id.
    elim: p => [[H1 [H2 H3]] | [[x2 y2] o2]  p _ H1].
    (* p = [::(x',y',o)] *)
    rewrite /= in H1 H2;rewrite -H1 -H2;clear H1 H2.
    by case: o1 H3 => [ ? | ?];[ apply E_inc_Aw | apply Einv_inc_Aw].
    (* general case *)
    pose q:= [:: (x1, y1, o1), (x2, y2, o2) & p].
    rewrite -/q in H1.
    have H2: size q = (size p).+2 by rewrite /q.
    rewrite L9 L8_E29a.
    pose proof L13 H2 H1 as [q' [o' [y' [_ [[H4 _] | [H4 _]]]]]].
    by left;right.
    by right.
  Qed.

End Active_path_implies_Aw_s.

Section Main_Result.
    
  Theorem Th4_1: 
    forall (x y:A), Aw (x, y) <-> (exists (p : seq (Eo A O)), Active_path W E p x y). 
  Proof.
    move => x y; split=> [ H1 | H1].
    by rewrite L9 in H1;apply Aw_s_path.
    by apply Active_path_to_Active. 
  Qed.
  
  Theorem Th4: forall (x y:A), ( x [⊥d] y | W ) <-> ~ Aw (x,y).
  Proof.
    move => x y;pose proof (Th4_1 x y) as H3.
    by split=> [ H1 H2 | H2];rewrite H3 in H2.
  Qed.
  
End Main_Result. 








