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

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_ssreflect ssralg matrix finmap order ssrnum.
From mathcomp Require Import mathcomp_extra boolp.
From mathcomp Require Import classical_sets.
Set Warnings "parsing coercions".

From RL Require Import  seq1 ssrel rel. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Types.
  (** * Needed Types *)
  Variables (T O: Type).
  Definition Eo (Z: Type) := prod (prod T T) Z.

End Types.

Section Active_relation.
  (** * D_U and active relation *)

  Variables (T: Type) (ptv: T*T).

  (** * Active paths  *)
  Variables (W: set T) (E: relation T).
  (* orientation  *)
  Definition EO := (T * T * O)%type.
  
  (* Active is now almost expressed as a transitive closure 
   * on an lifted space (A * A) * O as it uses AllL *)
  (* begin snippet Aeop:: no-out *)  
  Definition Active_path
    (W: set T) (E: relation T) (p: seq EO) (x y: T) :=
    match p with 
    | [::] => x = y 
    | [::eo1] => eo1.1.1 = x /\  eo1.1.2 = y /\  Oedge E eo1 
    | eo1 :: [:: eo2 & p]
      => eo1.1.1 = x /\ (last eo2 p).1.2 = y 
        /\ allL (ActiveOe W E) (belast eo2 p) eo1 (last eo2 p)
    end.
  (* end snippet Aeop *)

  Definition R_o (o:O):= match o with | P => E | N=> E.-1 end.

  Lemma R_o': forall (o:O) (xy: T*T),
      R_o o xy <-> match o with | P => E xy | N=> E.-1 xy end.
  Proof.
    by move => o xy; case: o.
  Qed.

  (** increase active path by left addition *)
  Lemma Active_path_cc: forall (p: seq EO) (eo1 eo2:  EO) (y: T),
      Active_path W E [:: eo1, eo2 & p] eo1.1.1 y
      <-> Active_path W E [:: eo2 & p] eo2.1.1 y /\ ActiveOe W E (eo1, eo2).
  Proof.
    elim => [ | eo3 p _] eo1 eo2 y. 
    - split.
      + by move => [_ [/= -> /allL0' H3]];move: (H3) => /ActiveOe_Oedge [_ H4].
      + by move => [[_ [<- H3]] /inP H4] /=; rewrite allL0.
    - split.
      by move => [H2 [/= H3 /= /allL_c/andP [/inP H4 H5]]] //.  
      by move => [[_ [H3 H4]] /inP H5] /=;
                  rewrite allL_c;split;[| split;[| apply /andP]].
  Qed.
  
  Lemma Active_path_cc_ht: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E [:: eo1, eo2 & p] x y -> 
      x = eo1.1.1 /\ y = (last eo2 p).1.2.
  Proof.
    by move => p eo1 eo2 x y [H1 [H2 _]].
  Qed. 
  
  Lemma Active_path_cc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E [:: eo1, eo2 & p] x y -> ActiveOe W E (eo1, eo2) .
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_cc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_cc [_ H1].
  Qed.
  
  Lemma Active_path_crc: forall  (p: seq EO) (eo1 eo2:  EO),
      Active_path W E (eo1::(rcons p eo2)) eo1.1.1 eo2.1.2
      <-> allL (ActiveOe W E) p eo1 eo2.
  Proof.
    elim => [ | eo p H1] eo1 eo2;
           first by split;[move => [_ [_ /= H2]] |move => H1;split;[ |split]].
    split; rewrite rcons_cons.
    move => /Active_path_cc [H2 /inP H3]. 
    by rewrite allL_c; apply/andP; split;[ | apply H1].
    by move => H2;split;[ | split;[ rewrite last_rcons | rewrite belast_rcons last_rcons]].
  Qed.
  
  Lemma Active_path_crc_ht: forall  (p: seq EO) (eo1 eo2: EO) (x y: T),
      Active_path W E (eo1::(rcons p eo2)) x y -> eo1.1.1 = x /\  eo2.1.2 = y.
  Proof.
    move => p eo1 eo2 x y;rewrite headI;move => [H1 [H2 _]].
    by elim: p H2 => [ //= | a p _ //=]; rewrite last_rcons.
  Qed.
  
  Lemma Active_path_crc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E (eo1::(rcons p eo2)) x y
      -> ActiveOe W E (eo1, (head eo2 p)) /\ ActiveOe W E ((last eo1 p), eo2).
  Proof.
    elim => [eo1 eo2 x y [_ [/= _ /allL0' H4]] // | eo3 p H1 eo1 eo2 x y].
    rewrite rcons_cons. move => H2.
    pose proof Active_path_cc_ht H2 as [H3 H4].
    pose proof Active_path_cc_a H2 as H5.
    move: H2;rewrite H3 Active_path_cc;move => [H6 H7].
    apply H1 in H6 as [H6 H8].
    by split;[ | rewrite last_cons].
  Qed.
  
  Lemma Active_path_rcrc: forall (p: seq EO) (eo1 eo2:  EO),
      Active_path W E (rcons (rcons p eo1) eo2) (head eo1 p).1.1 eo2.1.2
      <-> Active_path W E (rcons p eo1) (head eo1 p).1.1 eo1.1.2
        /\ ActiveOe W E (eo1, eo2).
  Proof.
    elim => [ | eo p H1] eo1 eo2.
    - split. 
      by move => [_ [_ /= /allL0' H3]];move: (H3) => /ActiveOe_Oedge [H4 _ /=].
      by move => [_ H2] /=;rewrite allL0'. 
    - 
      rewrite !rcons_cons.
    rewrite Active_path_crc.
    split. 
    move => /allL_rc/andP [/inP H2 H3].
    by rewrite Active_path_crc.
    rewrite Active_path_crc. move => [H2 /inP H3].
    rewrite allL_rc. 
    by apply/andP.
  Qed.

  Lemma Active_path_rcrc_ht: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E (rcons (rcons p eo1) eo2) x y 
      -> x = (head eo1 p).1.1 /\ y= eo2.1.2.
  Proof.
    elim => [ | eo p H1] eo1 eo2 x y; first by move => [H1 [H2 _]]; split.
    by rewrite !rcons_cons => /Active_path_crc_ht [H2 H3].
  Qed.

  Lemma Active_path_rcrc_a: forall (p: seq EO) (eo1 eo2:  EO) (x y: T),
      Active_path W E (rcons (rcons p eo1) eo2) x y 
      -> ActiveOe W E (eo1, eo2).
  Proof.
    move => p eo1 eo2 x y H1.
    pose proof Active_path_rcrc_ht H1 as [H2 H3].
    by move: H1; rewrite H2 H3; move => /Active_path_rcrc [_ H1].
  Qed.

  Lemma Active_path_rc_hto: forall (p: seq EO) (eo1:  EO) (x y: T),
      Active_path W E (rcons p eo1) x y ->
      x = (head eo1 p).1.1 /\ y = eo1.1.2 
      /\ Oedge E eo1 /\ Oedge E (head eo1 p).
  Proof.
    elim => [eo1 x y [H2 [H3 H4]] // | eo2 p _ eo1 x y H1]. 
    by pose proof Active_path_crc_ht H1 as [H2 H3];
    pose proof Active_path_crc_a H1 as [[H4 _] [_ [H8 _]]].
  Qed.
  
  Lemma Active_path_c_hto: forall (p: seq EO) (eo1:  EO) (x y: T),
      Active_path W E (eo1::p) x y -> 
      x = eo1.1.1 /\ y = (last eo1 p).1.2
      /\ Oedge E eo1 /\ Oedge E (last eo1 p).
  Proof.
    elim => [eo1 x y [H1 [H2 H3]] // | eo2 p _ eo1 x y H1]. 
    pose proof Active_path_cc_ht H1 as [H2 H3];
      pose proof Active_path_cc_a H1 as [H4 [H5 _]]. 
    rewrite lastI in H1.
    by pose proof Active_path_rc_hto H1 as [_ [_ [H8 _]]].
  Qed.
    
  Lemma Active_path_split: forall (p q: seq EO) (eop eoq:  EO) (x y: T),
      Active_path W E ((rcons p eop)++ eoq::q) x y
      -> Active_path W E (rcons p eop) x eop.1.2
        /\ Active_path W E (eoq::q) eoq.1.1 y
        /\ ActiveOe W E (eop, eoq).
  Proof.
    elim => [ q eop eoq x y // | z p Hr q eop eoq x y ].
    - rewrite cat_rcons cat0s => H1.
      pose proof Active_path_cc_ht H1 as [H2 _].
      pose proof Active_path_cc_a H1 as [H3 _].
      by move: H1; rewrite H2 Active_path_cc; move => [H4 H5];split.
    - elim/last_ind: q Hr eop eoq x y.
      + move => _ eop eoq x y.
        rewrite -cat_rcons cats0 => H1.
        pose proof Active_path_rcrc_ht H1 as [H2 H3].
        move: H1; rewrite H2 H3 Active_path_rcrc; move => [H4 H5]. 
        by pose proof H5 as [H6 [H7 _]].
      + move => q1 t _ H1 eo1 eo2 x y H3.
        rewrite rcons_cons cat_cons -rcons_cons -rcons_cat in H3.
        pose proof Active_path_crc_ht H3 as [H4 H5].
        move: H3; rewrite -H4 -H5.
        move => /Active_path_crc /allL_cat/andP [H6 /allL_c/andP [/inP H7 H8]]. 
        by rewrite rcons_cons Active_path_crc Active_path_crc.
  Qed.
  
  Lemma Active_path_cat: forall (p q: seq EO) (eop eoq :EO) (x y z: T),
      ActiveOe W E (eop, eoq)
      /\ Active_path W E (rcons p eop) x y 
      /\ Active_path W E (eoq::q) y z
      -> Active_path W E (rcons p eop++ eoq::q) x z.
  Proof.
    elim. 
    - move => q eop eoq x y z [H1 [H2 H3]].
      have -> : rcons [::] eop ++ eoq :: q = [:: eop, eoq & q] by [].
      pose proof Active_path_rc_hto H2 as [H4 _].
      pose proof Active_path_c_hto H3 as [H6 _].
      by rewrite H4 Active_path_cc -H6.
    - move => eo1 p1 Hr q eop eoq x y z [H1 [H2 H3]]. 
      rewrite rcons_cons cat_cons.
      rewrite rcons_cons in H2.
      elim/last_ind: q Hr H1 H2 H3.
      + move => _ /inP H1 H2 H3.
        pose proof Active_path_crc_ht H2 as [H4 H5].
        have [H7 H8]: y = eoq.1.1 /\ z = eoq.1.2 by move: H3 => [H3 [H3' _]].
        rewrite -H4 -H5 Active_path_crc in H2.
        rewrite cats1 -H4 H8 Active_path_crc allL_rc. 
        by apply/andP.
      + move => q1 eoq1 _ _ /inP H2 H3 H4.
        pose proof Active_path_crc_ht H3 as [H5 H6].
        pose proof Active_path_crc_ht H4 as [H7 H8].
        rewrite -H5-H6 Active_path_crc in H3.
        rewrite -H7 -H8 Active_path_crc in H4.
        rewrite -rcons_cons -{1}cat_rcons -/rcons -rcons_cat.
        rewrite -H5 -H8 Active_path_crc allL_cat. 
        apply/andP. rewrite allL_rc.
        split. by apply/andP. by [].
  Qed.

  Lemma Active_path_iff: forall (p q: seq EO) (eop eoq :EO) (x y z: T),
      ActiveOe W E (eop, eoq)
      /\ Active_path W E (rcons p eop) x y 
      /\ Active_path W E (eoq::q) y z
      <-> Active_path W E (rcons p eop++ eoq::q) x z /\ y= eop.1.2.
  Proof.
    move => p q eop eoq x y z.
    split => [ [H1 [H2 H3]] | [H1 H2]].
    - pose proof Active_path_rc_hto H2 as [_ [H4 _]].
      by split;[apply Active_path_cat with y | ].
    - pose proof Active_path_split H1 as [H3 [H4 H5]].
      pose proof H5 as [_ [H7 [H8 _]]].
      by split;[ | split;[rewrite H2 | rewrite H2 H8]].
  Qed.
  
  Lemma Active_path_cat': forall (p q: seq EO) (x y z: T),
      (exists (p' q': seq EO), exists (eop eoq: EO),
          p = rcons p' eop /\ q = eoq::q' /\  ActiveOe W E (eop, eoq))
      /\ Active_path W E p x y 
      /\ Active_path W E q y z
      -> Active_path W E (p++q) x z.
  Proof.
    move => p q x y z [[p1 [q1 [eop [eoq [H1 [H2 H3]]]]]] [H4 H5]].
    by rewrite H1 H2; apply Active_path_cat with y; rewrite -H1 -H2.
  Qed.

  
  Section Active_path_unique. 

    (** * If there exists an active path from x to y there exists a walk from x to y
        we just prove that when a variable is repeated twice we can shorten the
        active path * to prove the general property, we have maybe to switch from
        Type to eqType to use unique * in seq ?  *)
    
    Lemma Oedge_Fset:  forall (u v: T), Oedge E (u,v, P) /\ E.*#W v -> E.*#W u.
    Proof.
      move => u v [H1 H2]. 
      move: H2 => [w [H2 H3]].
      have H4: (E `;` E.* ) (u,w) by (exists v).
      have H5:  (E.+ `<=` E.*) by apply clos_t_clos_rt.
      have H6: E.* (u, w) by rewrite r_clos_rt_clos_t in H4 ;apply H5 in H4.
      by (exists w).
    Qed.
  
    Lemma Active_path_Fset:  forall (p: seq T) (x y: T),
        Active_path W E ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ E.*#W (last y p) -> E.*#W x. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        move => x y [[_ [_ H2]] H3].
        by apply Oedge_Fset with y.
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc. 
        move => [[H1 H2] H3].
        have H4: E.*#W y by apply Hr with z.
        move: H2 => [H2 _].
        by apply Oedge_Fset with y.
    Qed.
    
    Lemma Active_path_Fset':  forall (p: seq T) (x y: T),
        Active_path W E ((x, y, P) :: Lifto (y :: p) P) x (last y p) 
        /\ E.*#W (last y p) -> E.*#W y. 
    Proof.
      elim. 
      - rewrite /last /Lifto /pair_o /Lift.
        by move => x y [[_ [_ H2]] H3].
      - move => z p Hr x y.
        rewrite Lifto_c last_cons Active_path_cc.
        move => [[H1 H2] H3].
        have H4: E.*#W z by apply Hr with y.
        move: H2 => [_ [H2 _]].
        by apply Oedge_Fset with z.
    Qed.
    
    Lemma Active_path_shorten_L1: forall (p: seq EO) (x y z u v w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,v,N)) (v,w,N))] x w
        -> exists (q: seq T), Active_path W E (Lifto [::x,y & q] P) x (last y q) 
                        /\ (Fset E.* W) (last y q).
    Proof. 
      elim => [x y z u v w| ].
      - rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons Active_path_rcrc.
        have -> : [:: (x, y, P); (y, z, P)] = rcons [:: (x, y, P)]  (y, z, P) by [].
        rewrite Active_path_rcrc /head.
        move => [[H1 [H'2 [H'3 [/ChrelO_eq H'4 H'5]]]] [H3 [H4 [_ H6]]]].
        by (exists [::z]).
      - move => [[t s] o] p Hr x y z u v w.
        rewrite rcons_cons rcons_cons Active_path_cc.
        elim: p Hr.
        + move => Hr [H1 H2].
          move: (H1); rewrite Active_path_cc => [[_ [_ [_ [/ChrelO_eq H3 _]]]]];
                                               rewrite <- H3 in *.
          elim: o H1 => [ /Hr [q [H1 H4]] | ].
          ++ exists [:: z & q].
             by rewrite Lifto_c Lifto_c Active_path_cc -Lifto_c /last_cons. 
          ++ exists [::z].
             move: H1 => /Active_path_cc [H1 [_ [_ [_ H7]]]]. 
             move: (H2) => [H2' [H2'' _]].
             rewrite !Lifto_c Active_path_cc -Lifto_c /last.
             by split.
        + move => [[a b] o2] p _ H1 H2.
          move: (H2);rewrite Active_path_cc rcons_cons rcons_cons;
            move => [[_ [_ [_ [/ChrelO_eq H6 _]]]] _].
          rewrite <- H6 in *; clear H6.
          elim: o H2 => [[H2 H3] | ].
          ++ apply H1 in H2;move:H2 => [q H2].
             exists [::z].
             move: H2;rewrite Lifto_c => [[H2 H4]].
             rewrite /Lifto /Lift /pair_o.
             rewrite Active_path_cc last_cons /last.
             move: (H3) => [H5 [H6 _]].
             specialize Active_path_Fset' with q y z => H7.
             by split;[split | apply H7].
          ++ move => [H2 H3].
             pose proof H2 as H5.
             rewrite Active_path_cc in H2.
             rewrite Active_path_crc in H2.
             move: H2 => [H2 [_ [_ [_ H8 ]]]].
             exists [::z];rewrite last_cons /last.
             split. 
             by rewrite /= allL0'.
             by [].
    Qed.
    
    Lemma Active_path_shorten_L2: forall (p: seq EO) (x y z u w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> E.*#W y. 
    Proof. 
      move => p x y z u w H1.
      pose proof Active_path_shorten_L1 H1 as [q H2].
      rewrite Lifto_c in H2.
      by apply  Active_path_Fset' in H2.
    Qed.

    Lemma Active_path_shorten_L3: forall (p: seq EO) (x y z u w: T),
        Active_path W E [::(x,y,P),(y,z,P) & (rcons (rcons p (u,y,N)) (y,w,N))] x w
        -> ActiveOe W E ((x,y,P), (y,w,N)).
    Proof. 
      move => p x y z u w H1.
      move: (H1) => /Active_path_shorten_L2 H2.
      pose proof Active_path_cc_a H1 as [H3 _].
      move: (H1); rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons. 
      move => /Active_path_rcrc_a [_ [H4 _]].
      by [].
    Qed.
    
    (* the only complex case is (o1 o2 o3 o4)= ( P P N N) which was is treated 
       in the previous lemmata *) 
    Lemma Active_path_shorten: forall (p: seq EO) (x y z u w: T) (o1 o2 o3 o4:O) ,
        Active_path W E [::(x,y,o1),(y,z,o2) & (rcons (rcons p (u,y,o3)) (y,w,o4))] x w
        -> ActiveOe W E ((x,y,o1), (y,w,o4)).
    Proof. 
      move => p x y z u w o1 o2 o3 o4 H1. 
      move: (H1); rewrite -rcons_cons -rcons_cons -rcons_cons -rcons_cons. 
      move => /Active_path_rcrc_a [_ [H2 [_ H3]]].
      move: o1 o2 o3 o4 H1 H2 H3.
      case; case; case; case;
        move => H1 H2 H3;
               pose proof Active_path_cc_a H1 as [H4 [_ [_ H5]]];
               move: H5 => //= H5;move: H3 => //= H3.
      by apply Active_path_shorten_L3 with p z u.
    Qed.
    
  End Active_path_unique. 

End Active_relation.

Section Active. 
  (** * The Active relation as a relation on AxA *)

  Variables (T: Type). 

  (* begin snippet Active:: no-out *)  
  Definition Active (W: set T) (E: relation T) (x y: T) :=
   (exists (p: seq (T*T*O)), Active_path W E p x y).

  Definition D_separated  (W: set T) (E: relation T) (x y: T) := 
    ~(Active W E x y).
  (* end snippet Active *)  

  Lemma Deployment_to_Active_path:
    forall (W: set T) (E: relation T) (p: seq T) (x y: T) (o:O),
      p [\in] W.^c /\ allL (R_o E o) p x y 
      <-> Active_path W E (Lifto (x::(rcons p y)) o) x y.
  Proof.
    split.
    + elim: p x y => [x y [_ /allL0' /R_o' _] // | ]. 
      move => x1 p _ x y. 
      rewrite allset_consb allL_c. 
      move => [ /andP [H2 H'2] /andP [/inP H3 H4]].
      rewrite Lifto_crc Lifto_rcc Active_path_crc /=. 
      elim: p x x1 H3 H2 H'2 H4 => [x x1 H3 /inP H1 _ /allL0' H4 // | ].  
      ++ by rewrite allL0 /=; apply mem_set; split;case: o H3 H4 => /R_o' H3 /R_o' H4.
      ++ move => z p H1 x1 x H3 /inP H2 /allset_cons [H4 H4'] /allL_c/andP [/inP H5 H6] /=. 
         rewrite Lifto_c allL_c;apply /andP;split; last first. 
         by apply: (H1 x z H5 _ H4' H6); apply mem_set. 
         clear H1 H6;apply mem_set;rewrite ActiveOe_o /Oedge.
         by case: o H3 H5 => /R_o' H3 /R_o' H5. 
    + elim: p x y;
        first by move => x y //= [_ [_ H]];
                        split; elim: o H => H;[ | | apply /allL0'/R_o' | apply /allL0'/R_o'].
      
      move => z p H1 x y; rewrite Lift_o_cons;elim: p x y H1. 
      move => x y H1 /Active_path_cc [H2 [H3 [H4 [H5 H6]]]]. 
      elim: o H1 H2 H3 H4 H5 H6 => /= H1 H2 H3 H4 H5 H6.
      rewrite andbT.
      split. apply mem_set. by []. rewrite /allL /=.
      by move: H3 => /inP ->;move: H4 => /inP ->.
      rewrite andbT.
      split. apply mem_set. by []. rewrite /allL /=.
      by move: H3 => /inP ->;move: H4 => /inP ->.
      (* size p >= 2 *)
      move => t p _ x y H2;rewrite Lift_o_cons;move => /Active_path_cc [/H2 [H3 H5] H4].
      split.
        rewrite allset_cons andC. 
          split;[ | move: H4 => [_ [_ [_ H4]]]].
        by elim: o H2 H4 H5 => _ H4 H5.
        by elim: o H2 H4 H5 => _ /= H4 H5.
        rewrite allL_c H5 andbT.
        by elim: o H2 H4 H5 => _ [/= /inP H4 _] _ /=.
  Qed.
  
  Lemma Deployment_to_Active: forall (W: set T) (E: relation T) (p: seq T) (x y: T),
      p [\in] W.^c /\ allL E p x y -> Active W E x y.
  Proof.
    move => W E p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) P); apply Deployment_to_Active_path;split.
  Qed.

  Lemma Deployment_inv_to_Active: forall (W: set T) (E: relation T) (p: seq T) (x y: T),
      p [\in] W.^c /\ allL E.-1 p x y -> Active W E x y.
  Proof.
    move => W E p x y [H1 H2].
    by exists (Lifto (x::(rcons p y)) N); apply Deployment_to_Active_path;split.
  Qed.

End Active. 

Section PathRel_Examples.
  (** * Utilities *)
  
  Variables (T: Type) (E: relation T) (W: set T).

  Lemma clos_t_to_paths_l : forall (x y: T),
      (Δ_(W.^c) `;` E).+ (x, y) ->
      (exists (p: seq T), (x::p) [\in] W.^c /\ allL E p x y
                     /\ (x::p) [\in] ((Δ_(W.^c) `;` E).+)#_(y)).
  Proof.
    move => x y; rewrite {1}TCP; move => [p /= H1]; exists p.
    move: (H1) => /allL_WS_iff/andP [H2 H2'].
    apply allL_All in H1;apply allset_cons in H1;move: H1=> [/inP H1 H1'].
    by rewrite -allset_consb H1 H1' andbT.
  Qed.
  
  Lemma clos_t_to_paths_r : forall (x y: T),
      (E `;` Δ_(W.^c)).+ (x, y) ->
      (exists (p: seq T), (rcons p y) [\in] W.^c /\ allL E p x y
                     /\ (y::(rev p)) [\in] ((Δ_(W.^c) `;` E.-1).+)#_(x)).
  Proof.
    move => x y; rewrite {1}TCP; move  => [p H1]; exists p.
    rewrite allL_rev inverse_compose DeltaE_inverse /= in H1.
    move: (H1) => /allL_WS_iff/andP /= [/andP [/inP H2 H3] H2'].
    apply allL_All in H1;apply allset_cons in H1;move: H1=> [/inP /= H1 H1'].
    by rewrite H1 H1' andbT allL_rev H2' allset_rcons allset_rev H3. 
  Qed.
  
End PathRel_Examples.


Section Wip.
  (** * test to check how to prove that active path can be chosen uniq *)

  (* we use eqType here *)
  Variables (T: eqType).
  
  Lemma trunck_seq: forall (x: T) (p: seq T),
      ((x \in p) /\ exists (p1:seq T) , x \notin p1 /\ exists p2, (p= p1 ++ (x::p2)))
      \/ ~ (x \in p).
  Proof.
    move => x' p.
    elim: p => [ | x p [[H1 [p1 [H2 [p2 H3]]]] | H1] ].
    - by right.
    - left; split;first by rewrite in_cons H1 orbT.
      case Hx: (x'== x). 
      + by move: Hx => /eqP <-;(exists [::]);split;[|exists p].
      + by exists(x::p1);split;[rewrite in_cons Hx H2 | (exists p2); rewrite H3].
            - case Hx: (x'== x);last by right;rewrite in_cons Hx /=.
              left;split;first by rewrite in_cons Hx /=.
              by exists[::]; split;[ | exists p; move: Hx => /eqP ->].
  Qed.

  (* general property of seq *)
  Lemma trunck_seq_rev: forall (x: T) (p: seq T),
      ((x \in p) /\ exists (p1 p2:seq T), x \notin p2 /\ p= p1 ++ (x::p2))
      \/ ~ (x \in p).
  Admitted.
  
  (* P is compatible with truncation *)
  Axiom trunck_seq_P: forall (x: T) (p p1 p2: seq T) (P: T -> (seq T) -> Prop),
      P x p -> p = p1 ++ (x::p2) -> P x p2.
  
  (* existence with uniq *)
  Lemma P_uniq: forall (x: T) (p: seq T) (P: T-> (seq T) -> Prop),
      P x p -> exists (p2:seq T), x \notin p2 /\ P x p2.
  Proof.
    move => x p P H1.
    case Hx: (x \in p); last first.
    by (exists p);split;[rewrite Hx /= |].
    pose proof trunck_seq_rev x p as [[_ [p1 [p2 [H3 H4]]]] | H2].
    - exists p2. split. by []. by apply: (trunck_seq_P H1 H4).
    - by [].
  Qed.
           
End Wip.

