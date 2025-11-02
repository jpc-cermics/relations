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

From RL Require Import  ssrel rel  aacset paper_relations. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

Section Tcs.
  (** * proofs for the paper Topological conditional separation *)

  Section Tcs_Lemma14. 
    (** * Lemma 14 of Tcs *)
    Lemma L14_E38a : (Emw.* `;` Ew.* ) =
                       ('Δ `|` (Δ_(W.^c) `;` Bw) `|` (Bmw `;` Δ_(W.^c)) `|` Kw).
    Proof.
      have L14_E38a1 : Ew.+ = Δ_(W.^c) `;` Bw                            
        by rewrite /Bw -composeA -/Ew r_clos_rt_clos_t.
      have L14_E38a2 : Emw.+ = Bmw `;` Δ_(W.^c)
        by rewrite -inverse_clos_t L14_E38a1 composeIv -/Bmw DsetIv.
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

    (** * Equation (E38c) *)
    Local Lemma L14_E38c1 : (Cw `;` (Emw.* ) `;` (Ew.* )) `;` Cw  = Cw `;` ((Δ_(W) `|` Kw `;` Δ_(W)) `;` Cw).
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

    Local Lemma L14_E38c2 : forall (R: relation T), 
        R = R `;`  Δ_(W) -> (R.+ `;`  Δ_(W) = R.+).
    Proof.
      by move => R H1;rewrite {2}H1 [RHS]Delta_clos_trans_ends -H1. 
    Qed.

    Local Lemma L14_E38c3 : forall (R: relation T), 
        R =  Δ_(W) `;` R ->  Δ_(W) `;` R.+ = R.+.
    Proof.
      by move => R H1;rewrite {2}H1 [RHS]Delta_clos_trans_starts -H1. 
    Qed.
    
    Local Lemma L14_E38c4 : forall (R: relation T), 
        R = R `;`  Δ_(W) -> R =  Δ_(W) `;` R -> ( Δ_(W) `|` R.+) `;` ( Δ_(W) `|` R) = ( Δ_(W) `|` R.+).
    Proof. 
      move => R H1 H2.
      rewrite composeDr !composeDl Dset_compose_same -H2.
      rewrite L14_E38c2 //. 
      rewrite -setUA [in (R `|` _)]setUA [in (R `|` _)]setUC.
      rewrite -[in (R .+ `|` R `|` R .+ `;` R)]setUA.
      rewrite clos_t_decomp_rt_r. 
      by rewrite setUid.
    Qed.

    Local Lemma L14_E38c5 : forall (R: relation T), 
        R = R `;`  Δ_(W) -> R =  Δ_(W) `;` R -> ( Δ_(W) `|` R.+) `;` ( Δ_(W) `|` R.+) = ( Δ_(W) `|` R.+).
    Proof.
      move => R H1 H2.
      rewrite composeDr !composeDl Dset_compose_same.
      rewrite L14_E38c2 // L14_E38c3 //.
      by rewrite clos_t_decomp_2 -setUA setUid.
    Qed.
    
    (** * Equation (E38c) *)
    Lemma L14_E38c : (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Cw  = Cw. 
    Proof.
      have H1: DKD `;`  Δ_(W) = DKD
        by rewrite /DKD composeA Dset_compose_same.
      have H2:  Δ_(W) `;` DKD = DKD
        by rewrite /DKD -composeA -composeA Dset_compose_same.
      rewrite L14_E38c1.
      rewrite {1}Cw_ends.
      rewrite composeA. 
      rewrite -{1}[in ( Δ_(W) `;` (( Δ_(W) `|` Kw `;`  Δ_(W)) `;` Cw))]composeA. 
      rewrite [in  Δ_(W) `;` ( Δ_(W) `|` Kw `;`  Δ_(W))]composeDl.
      rewrite Dset_compose_same.
      rewrite -[in  Δ_(W) `;` (Kw `;`  Δ_(W))]composeA.
      rewrite /Cw -/DKD. 
      rewrite [in (DKD .+ `|`  Δ_(W))]setUC.
      rewrite -composeA. 
      by rewrite L14_E38c4; first by rewrite L14_E38c5. 
    Qed.
    
    (** * Equation (E38d) *)
    Lemma L14_E38d : (Cw `;` (Emw .* ) `;` (Ew .* )) `;` Δ_(W.^c)  = Cw `;` (Bmw `|` Kw)  `;` Δ_(W.^c).
    Proof.
      rewrite L14_E38b. 
      rewrite Cw_ends.
      rewrite composeA [in( 'Δ `|` Bmw `;` Δ_(W.^c) `|` Kw) `;` Δ_(W.^c)]composeDr.
      rewrite [in ('Δ `|` Bmw `;` Δ_(W.^c)) `;` Δ_(W.^c)]composeDr.
      rewrite [in  Bmw `;` Δ_(W.^c) `;` Δ_(W.^c)]composeA Dset_compose_same.
      rewrite [in LHS]composeA composeDl [in ( Δ_(W) `;` _)]composeDl.
      rewrite Delta_idem_l DeltaW_Wc  DeltaC_union_ideml. 
      rewrite -[in ( Δ_(W) `;` _ `|`  Δ_(W) `;` _)]composeDl.
      rewrite -[in (_ `;` Δ_(W.^c) `|` _ `;` Δ_(W.^c))]composeDr.
      rewrite -[in LHS]composeA -Cw_ends.
      by rewrite -composeA.
    Qed.

    (** * Equation (E38e) *)
    Lemma L14_E38e : Δ_(W.^c) `;` (Emw.* `;` Ew.* ) `;` Cw = Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw.
    Proof.
      have H0 : forall (R: relation T), 
          (Δ_(W.^c) `;` R `;` Cw).-1 = Cw `;` R.-1 `;` Δ_(W.^c)
          by move => R; rewrite composeIv  composeIv
                         Cw_inverse DsetIv composeA.
      have H1: inverse (Emw .* ) = (Ew .* )
        by rewrite inverse_star /Emw inverseK.
      have H2 : (Emw.* `;` Ew.* ).-1 = (Emw.* `;` Ew.* )
        by rewrite -H1; apply RRm_inverse. 
      have H3 : (Bw `|` Kw).-1 = (Bmw `|` Kw)
        by rewrite inverseU Kw_inverse.
      have H4 : (Δ_(W.^c) `;` ((Emw .* ) `;` (Ew .* )) `;` Cw).-1
                =  (Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw).-1
        by rewrite [LHS]H0 [RHS]H0 H2 H3 -[RHS]L14_E38d -composeA. 
      by apply inverseE in H4.
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
  
  Section closure_intersection_facts.
  (** * starting by closure intersection properties *) 
    
    Definition  ClosureI := 
      [set xy | Clos_(xy.1 | E,W) `&` Clos_(xy.2 | E,W) != set0 ].
    
    Lemma ClosureI_iff: ClosureI = (Emw.* `;` Ew.* ).
    Proof.
      rewrite predeqE /ClosureI /mkset => [[x1 x2]] /=.
      split;rewrite -notempty_exists.
      - move => [z /inP [[w1 [H1 <-]] [w2 [H2 <-]]]].
        by (exists z; split;[rewrite Emw_1 |]).
      - rewrite Emw_1 /inverse /mkset => [[z /= [H1 H2]]].
        by (exists z);rewrite in_setE;split;rewrite Clos_Ew. 
    Qed.
    
    Lemma Kw_W: Δ_(W) `;` (Emw.* `;` Ew.* ) `;` Δ_(W) =Δ_(W) `|` Δ_(W) `;` Kw `;` Δ_(W).
    Proof.
      rewrite L14_E38a.
      rewrite composeDl composeDl composeDl composeDr composeDr composeDr.
      have -> : Δ_(W) `;` 'Δ `;` Δ_(W) = Δ_(W)
        by rewrite  Delta_idem_r DsetK.
      have -> : Δ_(W) `;` (Δ_(W.^c) `;` Bw) `;` Δ_(W) = 'Δc
        by rewrite -composeA DeltaW_Wc !DeltaC_compose_absorbl.
      have -> : Δ_(W) `;` (Bmw `;` Δ_(W.^c)) `;` Δ_(W) = 'Δc
        by rewrite composeA [(Bmw `;` Δ_(W.^c) `;` Δ_(W))]composeA DeltaWc_W
             !DeltaC_compose_absorbr.
      by rewrite !DeltaC_union_idemr.
    Qed.
    
    Lemma WClosureI : forall (w1 w2: T),
        w1 \in W /\ w2 \in W /\ w1 <> w2 ->
                      Clos_(w1 | E,W) `&` Clos_(w2 | E,W) != set0 <-> 
                        (let R:= Δ_(W) `;` Kw `;` Δ_(W) in R (w1, w2)).
    Proof.
      move => w1' w2' [H1 [H2 H3]]; split => H4.
      - have H5: (Emw.* `;` Ew.* ) (w1', w2') by rewrite -ClosureI_iff.
        have H6: (Δ_(W) `;` (Emw.* `;` Ew.* ) `;` Δ_(W)) (w1', w2') by apply R_restrict.
        have H7: (Δ_(W) `|` Δ_(W) `;` Kw `;` Δ_(W))  (w1', w2') by rewrite -Kw_W.
        by move: H7 => [[z H7] | H7] //.
      - have H5:  (Δ_(W) `|` (Δ_(W) `;` Kw `;` Δ_(W)))  (w1', w2')
          by apply subsetUr.
        have H6: (Δ_(W) `;` (Emw.* `;` Ew.* ) `;` Δ_(W)) (w1', w2') by rewrite Kw_W.
        have H7: (Emw.* `;` Ew.* ) (w1', w2') by apply R_restrict in H6.
        by rewrite -ClosureI_iff in H7.
    Qed.
    
  End closure_intersection_facts.
  

  Section set_split. 
    (** * split of W and sub_split of W *)
    Definition set_sub_split {T: Type} (W' W'' W: set T) := 
      W' `<=` W /\ W''  `<=` W /\ W' `&` W'' = set0.
    
    Definition set_split  {T: Type} (W' W'' W: set T) := 
      W' `|` W'' = W /\ W' `&` W'' = set0.

    Lemma set_sub_splitC:  forall (W' W'' W: set T),
        set_sub_split W' W'' W <-> set_sub_split W'' W' W.
    Proof.
      move => W' W'' W;rewrite /set_sub_split {1}setIC.
      by split;move => [H1 [H2 H3]].
    Qed.
    
    Lemma set_splitC:  forall (W' W'' W: set T),
        set_split W' W'' W <-> set_split W'' W' W.
    Proof.
      by move => W' W'' W;rewrite /set_split {1}setUC {1}setIC.
    Qed.
    
    Lemma split_subsplit:  forall (W' W'' W: set T),
        set_split W' W'' W ->  set_sub_split W' W'' W.
    Proof.
      move => W' W'' W [H1 H2]. 
      have H3: W' `<=` W by rewrite -H1; apply: subsetUl.
      have H4: W'' `<=` W by rewrite -H1; apply: subsetUr.
      by split.
    Qed.

    Lemma subsplit_splitr:  forall (W' W'' W: set T),
        set_sub_split W' W'' W -> set_split W' (W'' `|` (W `\` (W' `|` W''))) W.
    Proof.
      move => W' W'' W [H1 [H2 H3]]. 
      have H4: (W `\` (W' `|` W''))  `<=` W by apply: subDsetl.
      have H5: W' `|` W'' `<=` W `|` W. by apply: setUSS.
      move: H5; rewrite setUid => H5.
      split.  
      - rewrite setUA; apply: setDUK H5. 
      - rewrite setIUr H3 set0U.
        have H6: W' `<=` (W' `|` W'') by apply: subsetUl.
        have H7: (W `\` (W' `|` W'')) `<=` (W `\` W') by apply: setDS H6.
        have H8:  W' `&` (W `\` (W' `|` W'')) `<=`  W' `&` (W `\` W'). by apply: setIS.
        have H9:   W' `&` (W `\` W') = set0 by apply: setDIK.
        by move: H8; rewrite H9 subset0.
    Qed.

    Lemma subsplit_splitl:  forall (W' W'' W: set T),
        set_sub_split W' W'' W -> set_split (W' `|` (W `\` (W' `|` W''))) W'' W.
    Proof.
      move => W' W'' W.
      rewrite set_sub_splitC set_splitC [in(W' `|` W'')]setUC.
      apply: subsplit_splitr.
    Qed.

    Lemma split_iff: forall (W' W'' W: set T),
        set_split  W' W'' W <->  W `\` W' = W'' /\ W' `<=` W.
    Proof.
      move => W' W'' W;split => [ [<- H2] | [<- H2]].
      - by split;[apply: setUKD;rewrite H2| apply subsetUl].
      - by split;[apply: setDUK|apply: setDIK].
    Qed.
    
  End set_split.


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
      rewrite H1 L14_E38a composeDl composeDl composeDl Delta_idem_r.
      rewrite -[Δ_(W.^c) `;` (Δ_(W.^c) `;` Bw)]composeA DsetK.
      rewrite composeDr composeDr composeDr  DsetK.
      rewrite H2  DsetK.
      rewrite [in RHS]composeDl [in RHS]composeDl [in RHS]composeDl Delta_idem_r.
      rewrite [in RHS]composeDr [in RHS]composeDr [in RHS]composeDr DsetK.
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
      rewrite /Smw /Sw composeDl composeDl !composeDr !Delta_idem_r.
      rewrite -[(Bw `;` Cw `|` Kw `;` Cw)]composeDr.
      rewrite -[(DKD.+ `;` (Bmw `|` Kw) `|` Δ_(W) `;` (Bmw `|` Kw))]composeDr -/Cw.
      (* now we have 4 terms as in the math proof *)
      rewrite L15_d L15_b L15_c L15_a setUid -setUA setUid.
      rewrite -composeDr. 
      have H1: (Δ_(W.^c) `;` ('Δ `|` Bw `|` Bmw `|` Kw) `|`
                  Δ_(W.^c) `;` (Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw))
               = (Δ_(W.^c) `;` ('Δ `|` Bw `|` Bmw `|` Kw)  `|`
                    Δ_(W.^c) `;` ((Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw)))
        by aac_normalise.
      rewrite H1 -composeDl /Aw /Dw.
      by aac_reflexivity.
    Qed.

  End Lemma_15.
  
  Section Theorem_5.
    (** * Theorem Th5 t-separation is equivalent to d-separation on W.^c *)
    
    Local Lemma T_not_t_separated : forall (x y: T),
        x \in W.^c -> y \in W.^c ->
        (Clos( Sw#_(x) | E, W) `&` Clos( Sw#_(y) | E, W) != set0 <-> Aw (x, y)).
    Proof. 
      move => x y Hx Hy.
      split.
      - rewrite -notempty_exists 2!Fset_comp.
        move=> [z /inP [ H1 H2]]. 
        have H3: ((Ew.* `;` Sw).-1 `;` (Ew.* `;` Sw)) (x, y)
          by apply Fset_intersect; exists z;split.
        have H4: (Δ_(W.^c) `;` ((Ew.* `;` Sw).-1 `;` (Ew.* `;` Sw))  `;` Δ_(W.^c)) (x, y)
          by apply R_restrict.
        have H5: (Δ_(W.^c) `;` Aw `;` Δ_(W.^c)) = 
                   (Δ_(W.^c) `;` ((Ew.* `;` Sw).-1 `;` (Ew.* `;` Sw)) `;` Δ_(W.^c))
          by rewrite -L15 composeIv Sw_inverse Emw_1;aac_reflexivity.
        have H6: (Δ_(W.^c) `;` Aw `;` Δ_(W.^c)) (x, y)
          by rewrite H5.
        by apply R_restrict in H6.
      - move => H1.
        have H2: (Δ_(W.^c) `;` Aw `;` Δ_(W.^c)) (x, y) by apply R_restrict.
        have H3: (Δ_(W.^c) `;` Aw `;` Δ_(W.^c)) = 
                   (Δ_(W.^c) `;` ((Ew.* `;` Sw).-1 `;` (Ew.* `;` Sw)) `;` Δ_(W.^c))
          by rewrite -L15 composeIv Sw_inverse Emw_1;aac_reflexivity.
        have H4: (Δ_(W.^c) `;` ((Ew.* `;` Sw).-1 `;` (Ew.* `;` Sw))  `;` Δ_(W.^c)) (x, y)
          by rewrite H3 in H2.
        apply R_restrict in H4; last by split.
        move: H4 => [z [/= H4 H5]].
        have H6: (Ew.* `;` Sw) (z, x) by [].
        move: H6 => [t [/= H6 H'6]].
        move: H5 => [u [/= H5 H'5]].
        rewrite -notempty_exists.
        (exists z); rewrite in_setE; split.
        + by rewrite /Sw /Fset /mkset; exists t; split;[ |exists x;split].
        + by rewrite /Sw /Fset /mkset;exists u;split;[ | exists y;split].
    Qed.

    Definition d_separated := Aw.^c.

    Definition t_separated := 
      [set xy :T *T | Clos( (Sw#_(xy.1)) | E,W) `&` Clos( (Sw#_(xy.2)) | E,W) = set0 ].
    
    (* Theorem 5 *)
    Theorem T5: forall (x y: T), 
        (x \in W.^c) -> (y \in W.^c) ->
        (t_separated (x, y) <-> d_separated (x, y)).
    Proof.
      move => x y Hx Hy.
      by rewrite /t_separated /d_separated /mkset -empty_iff T_not_t_separated /=.
    Qed.
    
    (* Theorem 5, relation version *)
    Theorem T5':  (Restrict t_separated W.^c) = (Restrict d_separated W.^c).
    Proof.
      rewrite predeqE /Restrict /mkset => [[x y]].
      split => [[? [? ?]] | [? [? ?]]].
      - have [H4 H5]: x \in W.^c /\  y \in W.^c by split;rewrite inP.
        pose proof (T5 H4 H5) as H6.
        by rewrite -H6;split;[ | split].
      - have [H4 H5]: x \in W.^c /\  y \in W.^c by split;rewrite inP.
        pose proof (T5 H4 H5) as H6.
        by rewrite H6;split;[ | split].
    Qed.
    
  End Theorem_5.
  
  Section Lemma_10.
    (** * This is Lemma 10 part 1 *)
    Lemma L10_1 : forall (w1 w2: T),
        (w1 \in W /\ w2 \in W /\ w1 <> w2) ->
        Clos_(w1 | E,W) `&` Clos_(w2 | E,W) != set0 <-> Kw (w1, w2).
    Proof.
      move => w1 w2 H1;rewrite (WClosureI H1).
      move: H1 => [H1 [H2 H3]].
      have H4: (Δ_(W) `;` Kw `;` Δ_(W)) (w1, w2) <-> Kw (w1,w2).
      by split;[rewrite -(@R_restrict T) | move => /(@R_restrict T) H5;apply: H5].
      by [].
    Qed.
    
    (** * This is Lemma 10 part 2 *)
    Lemma L10_2 : forall (w1 w2: T),
        (w1 \in W /\ w2 \in W /\ w1 <> w2) ->
        Clos_(w1 | E,W) `&` Clos_(w2 | E,W) != set0 -> Cw (w1, w2).
    Proof.
      move => w1 w2 [H1 [H2 H3]] /WClosureI H4. 
      by apply: DKDsubCw ;apply: H4.
    Qed.
    
  End Lemma_10.
  
  Section Lemma_7.
    (** * This is Lemma 7  *)
    Local Lemma L7_1: forall (x y: T), 
        x \in W.^c -> Bw (x, y) -> Clos_( x | E,W) `&` Clos_(y | E,W) != set0.
    Proof. 
      move => x y H1 H2.
      have H3: (Δ_(W.^c) `;` Bw) (x, y) by apply R_restrict_l.
      have H5: Ew.+ (x, y) by move: H3;rewrite /Bw -composeA -/Ew r_clos_rt_clos_t.
      have H7: Clos_(y | E,W) x by apply Clos_Ew; apply clos_t_clos_rt.
      have H8: Clos_(x | E,W) x by apply Clos_x_x.
      rewrite -notempty_exists; exists x. rewrite in_setE;by split.
    Qed.

    Local Lemma L7_2: forall (x y: T), 
        y \in W.^c -> Bmw (x, y) -> Clos_( x | E,W) `&` Clos_(y | E,W) != set0.
    Proof. 
      rewrite /Bmw => x y H1 H2.
      have H3: Clos_( y | E,W) `&` Clos_(x | E,W) != set0 by apply L7_1.
      by rewrite setIC.
    Qed.
    
    Local Lemma L7_3: forall (x y: T), 
        Kw (x,y) -> Clos_( x | E,W) `&` Clos_(y | E,W) != set0.
    Proof. 
      have H0: Ew.+ `<=` Ew.* 
        by move => xy; rewrite -DuT_eq_Tstar; apply subsetUr.
      rewrite E9e; move => x y [z [/= H1 H2]];rewrite -notempty_exists;exists z. 
      rewrite in_setE.
      rewrite -inverse_clos_t /inverse /mkset /Ew /= in H1.
      by split;[exists x;split;[apply H0 |] | exists y;split;[apply H0 |]].
    Qed.
    
    Local Lemma L7_4: forall (x y: T), 
        x \in W.^c -> y \in W.^c -> 
        (let R:= 'Δ `|` Bw `|` Bmw `|` Kw in R (x, y)) ->
        Clos_( x | E,W) `&` Clos_(y | E,W) != set0.
    Proof.
      move => x y Hx Hy [[[[_ /= H1]| H2] | H3] | H4]. 
      - rewrite -notempty_exists;exists x. rewrite in_setE. split.
        by rewrite /Fset /mkset;exists x;split;[apply: RTclosR|].
        by rewrite /Fset /mkset -H1;exists x;split;[apply: RTclosR|].
      - by apply: L7_1.
      - by apply: L7_2.
      - by apply: L7_3.
    Qed.
    
    Local Lemma L7_5: forall (x y: T), 
        x \in W.^c -> y \in W.^c ->
        Clos_( x | E,W) `&` Clos_(y | E,W) = set0 ->
        Aw (x, y) ->
        (let R:= (Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw) in R (x,y)).
    Proof.
      rewrite /Aw. 
      move => x y Hx Hy H1 [H2 | H2].
      - have H3: Clos_( x | E,W) `&` Clos_(y | E,W) != set0 by apply L7_4.
        by rewrite -empty_iff in H1.
      - by rewrite /Dw -composeA in H2.    
    Qed.
    
    Local Lemma L7_6l : forall (x y : T), Cw (x, y) -> W x.
    Proof.
      by rewrite Cw_starts; move => x y [w_x [[H1 H'1] _]]. 
    Qed.

    Local Lemma L7_6r : forall (x y : T), Cw (x, y) -> W y.
    Proof.
      by rewrite Cw_ends; move => x y [w_x [_ [H1 /= <-]]].  
    Qed.
    
    Local Lemma L7_7:  forall (x w: T), 
        x \in W.^c -> 
        (let R:= (Bw `|` Kw) in R (x, w)) ->
        Clos_( x | E,W) `&` Clos_(w | E,W) != set0.
    Proof.
      by move => x w Hx [H1 | H1];[apply L7_1 | apply L7_3].
    Qed.
    
    Local Lemma L7_8:  forall (y w: T), 
        y \in W.^c -> 
        (let R:= (Bmw `|` Kw) in R (w, y)) ->
        Clos_( y | E,W) `&` Clos_(w | E,W) != set0.
    Proof.
      rewrite /Bmw -Kw_inverse -inverseU.
      by move => y w H1 H2; have H3: (Bw `|` Kw) (y, w) by [];apply: L7_7.
    Qed. 
    
    (** * This is Lemma 7 of the paper: we could indicate in the proof the substeps 
        which follow the mathematical proof.
     *)
    Lemma L7: forall (x y: T), 
        x \in W.^c -> y \in W.^c -> Clos_(x |E,W) `&` Clos_(y|E,W) = set0 -> Aw (x, y) -> 
        exists w_x, exists w_y, w_x \in W /\ w_y \in W /\ Cw (w_x, w_y) 
                                /\ (Clos_(x| E,W) `&`  Clos_(w_x| E,W) != set0)
                                /\ (Clos_(y| E,W) `&`  Clos_(w_y| E,W) != set0).
    Proof.
      move => x y Hx Hy H1 H2.
      have [w_y [[w_x [H3 H4]] H5]]:
        (let R:= (Bw `|` Kw) `;` Cw `;` (Bmw `|` Kw) in R (x, y)) by apply L7_5.
      exists w_x; exists w_y.
      split; first by rewrite in_setE;apply: L7_6l H4.
      split; first by rewrite in_setE;apply: L7_6r H4.
      split; first by [].
      split; first by apply L7_7.
      by apply L7_8.
    Qed.

  End Lemma_7.
  
  Section Lemma_8_part1.
    (** * Lemma 8 part 1 *)
    
    Lemma L8_1 : forall (W' W'': set T),
        W' `<=` W /\ W'' `<=` W /\ (forall (w' w'': T), w' \in W' /\ w'' \in W'' -> ~(Cw (w', w'')))
        -> Clos(W' | E,W) `&` Clos(W''| E,W) = set0. 
    Proof.
      move => W' W'' [H1 [H2 H3]].
      rewrite empty_notexists.
      move => [z /inP [H5 H6]]. 
      move: H5 => /Clos_to_singleton [w1 [H10 H'10]].
      move: H6 => /Clos_to_singleton [w2 [H11 H'11]].
      have H12: Clos_(w1| E,W) `&` Clos_(w2 |E,W) != set0
        by rewrite -notempty_exists;exists z;rewrite in_setE; by split.
      have H6: w1 \in W by apply H1 in H10; rewrite in_setE.
      have H7: w2 \in W by apply H2 in H11; rewrite in_setE.
      have H8: ~ Cw (w1, w2) by rewrite -in_setE in H10;rewrite -in_setE in H11;apply H3.
      have H9:  w1 <> w2
        by move => H9; have H9': Cw (w1, w2) by rewrite H9;rewrite in_setE in H6;
                  rewrite in_setE in H7;apply Cw_reflexive_W.
      have H13: Cw (w1, w2) by apply: L10_2.
      by [].
    Qed.
    
  End Lemma_8_part1.

  Section Lemma8_part2.
    (** * Lemma 8 part 2 *)
    Local Lemma clos_t_sep_n : forall (n: nat) (W' W'': set T) (w' w'': T) (R: relation T),
        (W' `<=` W) /\ (W''= W `\` W') /\ 
          w' \in W' /\ w'' \in W'' /\ (Δ_(W) `;` R `;` Δ_(W))^(n.+1) (w', w'')
        -> let Rw := (Δ_(W) `;` R `;` Δ_(W)) in
           (exists (x' y': T), x'\in W' /\ y' \in W'' /\ Rw (x', y')).
    Proof.
      move => n X Y x y R.
      elim: n x y => [x y [H1 [H2 H3]] | n H0 y y' ].
      by (exists x; exists y; rewrite /iter Delta_idem_l in H3).
      rewrite /iter -/iter.
      move => [H2 [H3 [H4 [H5 [z [/= H6  H7]]]]]].
      pose proof lem (X z) as [Hz | Hz].
      - (exists z; exists y'). split. by rewrite in_setE. by [].
      - have H8: W z. by move: H7 => [u [[v [[H7 _] _]] _]].
        have H9: Y z.  rewrite H3 -in_setE in_setD. rewrite -notin_setE in Hz. 
        rewrite -in_setE in H8. by rewrite H8 Hz.
        have H10: let Rw:=(Δ_(W) `;` R `;` Δ_(W))in exists x' y' : T, x' \in X /\ y' \in Y /\ Rw (x', y').
        rewrite -in_setE in H9. by apply H0 with y z.
        move: H10 => [x2 [y2 [H11 [H12 H13]]]].
        by (exists x2; exists y2).
    Qed.
    
    Local Lemma clos_t_sep : forall (W' W'': set T) (w' w'': T) (R: relation T),
        (W' `<=` W) /\ (W''= W `\` W') /\ 
          w' \in W' /\ w'' \in W'' /\ (Δ_(W) `;` R `;` Δ_(W)).+ (w', w'')
        -> let Rw := (Δ_(W) `;` R `;` Δ_(W)) in
           (exists (x' y': T), x'\in W' /\ y' \in W'' /\ Rw (x', y')).
    Proof.
      move => W' W'' w' w'' R [H1 [H2 [H3 [H4 H5]]]].
      apply clos_t_iterk in H5.
      move: H5 => [n' H5].
      by apply clos_t_sep_n with n' w' w''.
    Qed.
    
    Local Lemma L8_a: forall (W' W'': set T) (w' w'': T),
        (W' `<=` W) /\ (W''= W `\` W') /\ w' \in W' /\ w'' \in W''
        /\ Cw (w', w'')
        -> let Rw := (Δ_(W) `;` Kw `;` Δ_(W)) in
           (exists (x' y': T), x'\in W' /\ y' \in W'' /\ Rw (x', y')).
    Proof.
      move => W' W'' w' w'' [H1 [H2 [H3 [H4 H5]]]].
      have H8:  W' `&` W'' = set0 by rewrite H2; apply: setDIK. 
      have H6: w' <> w'' 
        by move => H6; rewrite -H6 in H4;
             (have H7: W' `&` W'' != set0 by apply notempty_exists;exists w';rewrite in_setE;
              split;[ rewrite -in_setE | rewrite -in_setE]);
                  rewrite -notempty_iff in H7.
      have H7:  (Δ_(W) `;` Kw `;` Δ_(W)).+ (w', w'') by move: H5 => [H5 | [ x H5]].
      by apply clos_t_sep with w' w''.
    Qed.
    
    Local Lemma L8_b: forall (W' W'': set T) (w' w'': T),
        (W' `<=` W) /\ (W''= W `\` W') /\ w' \in W' /\ w'' \in W''
        /\ Cw (w', w'')
        -> (exists (w1' w1'': T), w1' \in W' /\ w1'' \in W'' /\
                                   Clos_( w1' | E,W) `&` Clos_(w1'' | E,W) != set0).
    Proof.
      move => W' W'' w' w'' H1.
      have [x' [y' [H2 [H3 H4]]]]:
        let Rw := (Δ_(W) `;` Kw `;` Δ_(W)) in (exists (x' y': T), x'\in W' /\ y' \in W'' /\ Rw (x', y'))
          by apply L8_a with w' w''.
      apply WClosureI in H4. rewrite -notempty_exists in H4.
      move: H4 => [z H4].
      by (exists x');(exists y');rewrite -notempty_exists;split;[| split;[ | exists z]].
      move: H1 => [H'1 [H'2 [H'3 [H'4 H'5]]]].
      split; first by rewrite in_setE;rewrite in_setE in H2;apply H'1 in H2.
      split; first by rewrite H'2 in_setD in H3;move: H3 => /andP [H3 _].
      move => H5.
      have H6: W' `&` W'' != set0
        by rewrite -notempty_exists;exists x';rewrite in_setE;split;[|rewrite H5];rewrite -in_setE.
      have H7: W' `&` W'' = set0 by apply W_part with W.
      by rewrite -empty_iff in H7.
    Qed.
    
    Lemma L8_2: forall (W' W'': set T),
        (W' `<=` W) /\ (W''= W `\` W') /\ Clos(W' | E,W) `&` Clos(W'' | E,W)=set0
        -> ~ (exists (w' w'': T), w' \in W' /\ w'' \in W'' /\ Cw (w', w'')).
    Proof.
      move => W' W'' [H1 [H2 H3]] [w' [w'' [H4 [H5 H6]]]].
      have H7:  (exists (w1' w1'': T), w1' \in W' /\ w1'' \in W'' /\
                                         Clos_( w1' | E,W) `&` Clos_(w1'' | E,W)!= set0)
        by apply L8_b with w' w''.
      move: H7 => [w1 [w2 [/inP H7 [/inP H8 H9]]]].
      
      have [z HH] : exists z, z \in  (Clos_( w1 | E,W) `&` Clos_( w2 | E,W))
            by rewrite notempty_exists.
      rewrite in_setE in HH. move: HH => [H10 H11].
      have H12:  Clos(W'|E,W) `&` Clos(W''|E,W) != set0.
      rewrite -notempty_exists;exists z;rewrite in_setE;split;rewrite Clos_to_singleton;[exists w1 |exists w2].
      by split;[ | ].
      by split;[ | ].
      by rewrite -empty_iff in H3.
    Qed.
    
  End Lemma8_part2.
  
  Section Lemma_9.
    Lemma L9 :  forall (w : T) (X : set T),
         X `<=` W.^c ->
        ( w \in (Cw `;` (Bmw `|` Kw))#X
          <-> (exists w', Cw (w,w') /\ (exists z, z \in Clos_(w'|E,W) /\ z \in Clos(X|E,W)))).
    Proof.
      move => w X H1;rewrite (Fset_restrict _ H1) -L14_E38d -Fset_restrict=> [|//].
      rewrite composeA; split.
      - move => H2. rewrite in_setE in H2.
        move: H2 => [x [[x' [H2 [z [H3 H'3]]]] H4] ].
        exists x'; split => [// |].

        exists z; split. rewrite in_setE. exists x'. split. by rewrite Emw_1 in H3. by []. 
        by rewrite in_setE; exists x; split.
      - move => [w' [H2 [z [H3 H4]]]].
        rewrite in_setE in H3. rewrite in_setE in H4. 
        move: H3 => [w'' [H3  H3']].
        move: H4 => [x [H4 H4']].
        rewrite in_setE /= . 
        exists x; split; last by [].
        exists w';split; first by[].
        exists z;split; first  by rewrite Emw_1 /inverse /mkset /= -H3'.
        by [].
    Qed.
  End Lemma_9. 
  
  Section Lemma_11.
    Lemma L11: forall (Θ: set T) (W': set T),
        (W' `&` (Cw `;` (Bmw `|` Kw))#Θ = set0) 
        ->  W' `<=` W
        ->  Θ `<=` W.^c
        -> ( Clos(W'| E,W) `&` Clos(Θ `|` (Cw `;` (Bmw `|` Kw))#Θ| E,W)= set0).
    Proof.
      move => Θ W' H0 H0' H0''.
      - (* first part *) 
        have H1:  Clos(W'| E,W) `&` Clos(Θ| E,W)= set0.
        rewrite empty_notexists.
        move => [t H]. rewrite in_setE in H. move: H=> [H2 H3].
        rewrite Clos_to_singleton in H2.
        move: H2 => [y [H2 H4]].
        have H5: y \in (Cw `;` (Bmw `|` Kw))#Θ.
        
          rewrite L9.
          - exists y;split. 
            + apply Cw_reflexive_W. apply H0' in H2. by [].
            + exists t. split. by rewrite in_setE. by rewrite in_setE.
          - by []. 
            
        have H6: y \in ( W' `&` (Cw `;` (Bmw `|` Kw))#Θ). 
        rewrite in_setE. split. by []. by rewrite -in_setE.
        
        have H7: W' `&` (Cw `;` (Bmw `|` Kw))#Θ != set0 by rewrite -notempty_exists;exists y.
        by rewrite -empty_iff  in H0.
      - (* second part *) 
        have H'1:  Clos(W'| E,W) `&` Clos( (Cw `;` (Bmw `|` Kw))#Θ| E,W)= set0.
        rewrite empty_notexists.
        move => [t H].  rewrite in_setE in H. move: H=> [H2 H3].
        rewrite Clos_to_singleton in H2.
        rewrite Clos_to_singleton in H3.
        move: H2 H3 => [w [H2 H4]] [θ [H3 H5]].
        have H6: θ <> w
          by (move => H6;
                     (have H7: W' `&` (Cw `;` (Bmw `|` Kw))#Θ != set0
                       by rewrite -notempty_exists;exists θ;rewrite in_setE;split;[rewrite H6|]);
                     rewrite -empty_iff  in H0).
        have H8_1: w \in W by apply H0' in H2;rewrite in_setE.
        have H8_2: θ \in W by apply CBK_W in H3;rewrite in_setE.
        have H8_3: w  <> θ by symmetry. 
        have H8: Cw (w, θ)
          by apply: L10_2;[| rewrite -notempty_exists;exists t;rewrite in_setE;split].
        have H9: w \in (Cw `;` (Cw `;` (Bmw `|` Kw)))#Θ 
            by rewrite -Fset_comp in_setE;(exists θ); split.
        have H10: w \in (Cw `;` (Bmw `|` Kw))#Θ
          by rewrite - Cw_transitive composeA.
        have H11:  W' `&` (Cw `;` (Bmw `|` Kw))#Θ != set0 
          by rewrite -notempty_exists;exists w;rewrite in_setE;split;[|rewrite -in_setE].
        by rewrite -empty_iff  in H0.
      - (* combine *)
        by rewrite Clos_union setIUr H1 H'1 set0U.
    Qed.
  End Lemma_11.
  
  Section Proposition_6.
    (** * Proposition 6 *)
    
    Local Lemma P6_1imp2_a_contra: forall (Γ Λ: set T) (W' W'': set T),
        (W' = (Cw `;` (Bmw `|` Kw))#Λ) -> 
        (W''= (Cw `;` (Bmw `|` Kw))#Γ ) ->
        ( Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W) != set0) ->
        ~ (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> (t_separated (λ, γ))).
    Proof.
      move => Γ Λ W' W'' H4 H5 -/notempty_exists [z H6]. 
      move: H6;rewrite in_setE => [[H6 H7]].
      rewrite Clos_to_singleton in H6; move: H6 => [λ [H6 H6'']].
      rewrite Clos_to_singleton in H7; move: H7 => [γ [H7 H7']].
      have H8: Sw#Λ λ
        by move: H6 => [H6 | H6];rewrite /Sw -Fset_union_rel Fset_D;
                      [left| right;rewrite -H4].
      have H9: Sw#Γ γ 
        by move: H7 => [H7 | H7];rewrite /Sw -Fset_union_rel Fset_D;
                      [ left | right;rewrite -H5].
      move: H8 => /Fset_union_set H8; move: H8 => [x [H8 H10]].
      move: H9 => /Fset_union_set H9; move: H9 => [y [H9 H11]].
      have H12: Clos( Sw#_(x) | E, W) `&` Clos( Sw#_(y) | E, W) != set0.
      by rewrite -notempty_exists;exists z; rewrite in_setE;
      split;rewrite Clos_to_singleton;[exists λ | exists γ].
      move => H. 
      have H13: t_separated (x, y) by apply H; rewrite !in_setE.
      by rewrite /t_separated /mkset /= -empty_iff  in H13.
    Qed.
    
    Local Lemma P6_1imp2_a: forall (Γ Λ: set T) (W' W'': set T),
        (W' = (Cw `;` (Bmw `|` Kw))#Λ) -> 
        (W''= (Cw `;` (Bmw `|` Kw))#Γ )->
        (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> t_separated (λ,γ)) 
        -> ( Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W) = set0).
    Proof.
      move => Γ Λ W' W'' H1 H2;apply: contraPP => H6. 
      by apply: (P6_1imp2_a_contra H1 H2);rewrite -notempty_iff. 
    Qed.
    
    Local Lemma P6_1imp2_b: forall (Γ: set T) (W': set T),
        (W' = (Cw `;` (Bmw `|` Kw))#Γ) -> W' `<=` W.
    Proof.
      by rewrite Cw_starts /Fset; move => Γ W' -> x [y [[z [[t [/= /DsetE [H2 _] _]] _]] _]].
    Qed.
    
    Local Lemma P6_1imp2_c: forall (Γ Λ: set T) (W' W'': set T),
        W' `<=` W -> W'' `<=` W ->
        ( Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W) = set0)
        -> set_sub_split W' W'' W.
    Proof.
      move => Γ Λ W' W'' H1 H2 H3.
      have H4:  W' `<=`  Clos(Λ `|` W'| E,W) by apply: ClosU_containsr H1. 
      have H5:  W'' `<=`  Clos(Γ `|` W''| E,W) by apply: ClosU_containsr H2. 
      have H6:  W'  `&`  W''  `<=`  Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W)
        by apply: setISS H4 H5.
      by move: H6; rewrite H3 subset0 => H8.
    Qed.
    
    Local Lemma P6_1imp2_d: forall (Γ Λ: set T) (W' W'': set T),
        (W' = (Cw `;` (Bmw `|` Kw))#Λ) -> 
        (W''= (Cw `;` (Bmw `|` Kw))#Γ )->
        (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> t_separated (λ, γ)) 
        -> ( Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W) = set0) 
          /\ set_sub_split W' W'' W. 
    Proof.
      move =>  Γ Λ W' W'' H3 H4 /(P6_1imp2_a H3 H4) H5.
      move: H3 H4 => /P6_1imp2_b H3 /P6_1imp2_b H4.
      by split;last by apply: (P6_1imp2_c H3 H4 H5).
    Qed. 
    
    Lemma P6_1imp2_e: forall (Γ Λ: set T) (W' W'' Wt: set T),
        ( Γ `<=` W.^c) /\ ( Λ `<=` W.^c) /\ (Γ `&` Λ = set0)
        -> (W' = (Cw `;` (Bmw `|` Kw))#Λ) 
        -> (W''= (Cw `;` (Bmw `|` Kw))#Γ)
        -> (Wt = W `\` (W'`|` W''))
        -> Clos(Λ `|` W'|E,W) `&` Clos(Γ `|` W''|E,W) = set0
        -> ( Clos(Λ `|` (W' `|` Wt) | E,W) `&` Clos(Γ `|` W''| E,W) = set0).
    Proof.
      move => Γ Λ W' W'' Wt [H1 [H2 H3]] H4 H5 H6 H7.
      have H8: (W'`|` W'') `&` Wt = set0 by rewrite H6; apply: setDIK.
      have [H9 H10]: (Wt `&` W' = set0) /\ (Wt `&` W'' = set0)
        by rewrite setIC setIUr setU_eq0 in H8. 
      have H11: (Wt `&` (Cw`;`(Bmw `|` Kw))#Γ = set0) by rewrite -H5.
      have H12: Wt `<=` W by  rewrite H6;apply: subDsetl.
      pose proof (L11 H11 H12 H1) as H13.
      by rewrite setUA Clos_union setIUl H7 set0U H5.
    Qed.

    Lemma P6_1imp2_f: forall (Γ Λ: set T) (W' W'' Wt: set T),
        ( Γ `<=` W.^c) /\ ( Λ `<=` W.^c) /\ (Γ `&` Λ = set0)
        -> (W' = (Cw `;` (Bmw `|` Kw))#Λ) 
        -> (W''= (Cw `;` (Bmw `|` Kw))#Γ)
        -> (Wt = W `\` (W'`|` W''))
        -> (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> t_separated (λ, γ)) 
        -> ( Clos(Λ `|` (W' `|` Wt) | E,W) `&` Clos(Γ `|` W''| E,W) = set0)
          /\ set_split (W' `|` Wt) W'' W.
    Proof.
      move => Γ Λ W' W'' Wt H1 H4 H5 H6 H7.
      pose proof (P6_1imp2_d H4 H5 H7) as [H8 H9]. 
      split;first  by apply: P6_1imp2_e.
      by rewrite H6; apply: subsplit_splitl.
    Qed.
    
    Lemma P6_1imp2: forall (Γ Λ: set T),
        ( Γ `<=` W.^c) /\ ( Λ `<=` W.^c) /\ (Γ `&` Λ = set0)
        ->  (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> t_separated (λ, γ)) 
        ->  ( exists (W1: set T), exists (W2: set T), 
               ( Clos(Λ `|` W1| E,W) `&` Clos(Γ `|` W2| E,W) = set0)
               /\  set_split W1 W2 W).
    Proof.
      move =>  Γ Λ H1 H4.
      set W' := ((Cw `;` (Bmw `|` Kw))#Λ).
      set W'' := ((Cw `;` (Bmw `|` Kw))#Γ ).
      set Wt :=  W `\` (W'`|` W'').
      by exists (W' `|` Wt); exists W'';apply: (P6_1imp2_f H1 _ _ _ H4);rewrite /W' /W'' /Wt.
    Qed.
    
    (* second part using Lemma 7 and Lemma 8 *)
    Lemma P6_2imp1_a: forall (Γ Λ: set T),
        ( Γ `<=` W.^c) /\ ( Λ `<=` W.^c) /\ (Γ `&` Λ = set0) 
        -> ( exists (W': set T), exists (W'': set T), 
              ( W' `<=` W) /\ (W''= W `\` W') 
              /\ ( Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W) = set0) )
        -> (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> t_separated (λ, γ)).
    Proof.
      move => Γ Λ [H3 [H4 H5]] [W' [W'' [H1 [H2 H6]]]] λ γ [/inP H7 /inP H8].
      have H9: λ \in W.^c by apply H4 in H7;rewrite in_setE.
      have H10:  γ \in  W.^c  by apply H3 in H8;rewrite in_setE.
      rewrite (T5 H9 H10).
      move => H11.
      have H12:  Clos_(γ | E,W) `<=` Clos(Γ `|` W''| E,W) by apply Clos_s_inc.
      have H13:  Clos_(λ | E,W) `<=` Clos(Λ `|` W'| E,W) by apply Clos_s_inc.
      have H14:  Clos_(λ | E,W) `&` Clos_(γ | E,W) `<=`
                  Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W)
        by move => t [H'1 H'2]; apply H13 in H'1;apply H12 in H'2;split.
      have H15:  Clos_(λ|E,W) `&` Clos_(γ|E,W) `<=` set0
        by rewrite H6 in H14.
      have H17: Clos_(λ|E,W) `&` Clos_(γ|E,W) = set0
        by rewrite predeqE => x;split;[apply H15|].
      clear H12 H13 H14 H15.
      have [w_x [w_y [H12 [H13 [H14 [H15 H16]]]]]]:
        exists w_x, exists w_y, w_x \in W/\ w_y \in W /\ Cw (w_x, w_y )
                                /\ (Clos_(λ| E,W) `&` Clos_(w_x| E,W) != set0)
                                /\ (Clos_(γ| E,W) `&` Clos_(w_y| E,W) != set0).
      by apply L7.
      have H18:  Clos(W''| E,W) `<=` Clos(Γ `|` W''| E,W) by apply Clos_inc_r.
      have H19:  Clos(W' | E,W) `<=` Clos(Λ `|` W'| E,W) by apply Clos_inc_r.
      have H20:  Clos(W'| E,W) `&` Clos(W''| E,W)  `<=`
                  Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W)
        by move => x [H'1 H'2]; apply H19 in H'1;apply H18 in H'2;split.
      
      have H21:  Clos(W'| E,W) `&` Clos(W''| E,W) `<=` set0
        by rewrite H6 in H20.        
      have H22: Clos(W'| E,W) `&` Clos(W''| E,W) = set0
        by rewrite predeqE => x;split;[apply H21|].                               
      clear H18 H19 H20 H21.
      have H18: ~ (exists (w' w'': T), w' \in W' /\ w'' \in W'' /\ Cw (w', w''))
        by apply L8_2.

      move: H15 => /notempty_exists [t H15]. rewrite in_setE in H15. move: H15 => [H15 H'15].
      
      move: H16 => /notempty_exists [u H16]. rewrite in_setE in H16. move: H16 => [H16 H'16].

      pose proof lem (w_x \in W') as [H19 | H19];pose proof lem (w_y \in W') as [H20|H20].
      
      - have H21: Clos(Λ `|` W' | E,W) u
          by rewrite Clos_to_singleton;exists w_y;split;[right;rewrite -in_setE |].
        have H23: Clos(Γ `|` W'' | E,W) u
          by rewrite Clos_to_singleton; exists γ;split;[left|].
        
        have H24: Clos(Λ `|` W'|E,W) `&` Clos(Γ `|` W''|E,W) != set0
          by rewrite -notempty_exists; exists u;rewrite in_setE; split.
        by  rewrite -empty_iff  in H6.
      - have H21: w_y \in W''
            by rewrite H2 in_setD H13 notin_setE; move => H21; by rewrite -in_setE in H21. 
        have H23: (exists w' w'' : T, w' \in W' /\ w'' \in W'' /\ Cw (w', w''))
          by (exists w_x;exists w_y).
        by [].
      - have H21: w_x \in W''
            by rewrite H2 in_setD H12 notin_setE; move => H21; by rewrite -in_setE in H21. 
        have H23: (exists w' w'' : T, w' \in W' /\ w'' \in W'' /\ Cw (w', w''))
          by (exists w_y;exists w_x; split;[ |split;[ |apply Cw_sym]]).
        by [].
      - have H21: Clos(Λ `|` W' | E,W) t
            by rewrite Clos_to_singleton; exists λ; split;[left|].
        have H23: w_x \in W''
            by rewrite H2 in_setD H12 notin_setE; move => H24; by rewrite -in_setE in H24.
        have H24: Clos(Γ `|` W'' | E,W) t
          by  rewrite Clos_to_singleton;exists w_x; split;[right;rewrite -in_setE|].
        have H25: Clos(Λ `|` W'|E,W) `&` Clos(Γ `|` W''|E,W) != set0
          by rewrite -notempty_exists; exists t; rewrite in_setE; split.
        by  rewrite -empty_iff  in H6.
    Qed.


    Lemma P6_2imp1: forall (Γ Λ: set T),
        ( Γ `<=` W.^c) /\ ( Λ `<=` W.^c) /\ (Γ `&` Λ = set0) 
        -> ( exists (W': set T), exists (W'': set T), 
              ( Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W) = set0)
              /\ set_split W' W'' W)
        -> (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> t_separated (λ, γ)).
    Proof.
      move => Γ Λ H1 [W1 [W2 [H2 H3]]].
      apply: (P6_2imp1_a H1).
      exists W1; exists W2.
      by move: H3;rewrite H2 split_iff => [[H3 H4]].
    Qed.
    
    Proposition P6: forall (Γ Λ: set T),
        ( Γ `<=` W.^c) /\ ( Λ `<=` W.^c) /\ (Γ `&` Λ = set0) 
        -> (
            (forall (λ γ: T), λ \in Λ /\ γ \in Γ -> t_separated (λ, γ))
            <->
              (exists (W': set T), exists (W'': set T), 
                  ( Clos(Λ `|` W'| E,W) `&` Clos(Γ `|` W''| E,W) = set0)
                  /\ set_split W' W'' W)
            ).
    Proof.
      by move => Γ Λ H1;split;[apply: P6_1imp2 | apply: P6_2imp1].
    Qed.

  End Proposition_6.

  Section test1.
    (** * Topologies *)
    Variables (I: Type).
    
    (** * Fset and bigcup *)
    Lemma Fset_bigcup: forall (R : relation T) (F : I -> set T),
        R#( \bigcup_ i (F i) ) =  \bigcup_ i (R# (F i)).
    Proof.
      move => R F;rewrite /Fset predeqE => x;split.
      by move => [y [H1 [n Pn Fny]]]; exists n;[ | exists y].
      by move => [n Pn [y [H1 H2]]];exists y;split;[|exists n].
    Qed.
    
    (** * Fset and bigcap *)
    Lemma Fset_bigcap: forall (R : relation T) (F : I -> set T),
        R#( \bigcap_ i (F i) ) `<=`  \bigcap_ i (R# (F i)).
    Proof.
      by move => R F x [y [H1 H2]];exists y; split;[| apply: H2]. 
    Qed.
    
    Lemma Fset_stableU: forall (R : relation T) (F : I -> set T),
        (forall i, R#(F i) `<=` (F i)) -> R#(\bigcup_ i (F i)) `<=` (\bigcup_ i (F i)).
    Proof.
      by move => R F H1;rewrite Fset_bigcup => x [n Pn Fn];exists n;[|apply: H1].
    Qed.

    Lemma Fset_stableI: forall (R : relation T) (F : I -> set T),
        (forall i, R#(F i) `<=` (F i)) -> R#(\bigcap_ i (F i)) `<=` (\bigcap_ i (F i)).
    Proof.
      move => R F H1. 
      have H2: (\bigcap_ i R#(F i)) `<=` (\bigcap_ i (F i))
        by move => x H2 i /H2/H1 H3.
      have H3: R#( \bigcap_ i (F i) ) `<=`  \bigcap_ i (R# (F i)) by apply:Fset_bigcap.
      by apply: (subset_trans H3 H2).
    Qed.

    Lemma Fset_stableIf: forall (R : relation T) (A B: set T),
       R#A  `<=` A -> R#B  `<=` B -> R#(A `&` B)  `<=` A   `&` B.
    Proof.
      move => R A B ? ?.
      have H1: (R#A) `&`  (R#B)  `<=`  A   `&` B by apply: setISS.
      apply: (subset_trans _ H1); apply: FsetI.
    Qed.
    
    Lemma Fset_0 : forall (R : relation T), R#set0 `<=` set0.
    Proof.
      by move => R x [y [_ H1]].
    Qed.

    Lemma Fset_T : forall (R : relation T), R#setT `<=` setT.
    Proof.
      by []. 
    Qed.

    Lemma Aset_bigcup: forall (R : relation T) (F : I -> set T),
        ( \bigcup_ i (F i) ):#R =  \bigcup_ i ((F i):#R).
    Proof.
      by move => R F;apply: Fset_bigcup.
    Qed.

    Lemma Aset_bigcap: forall (R : relation T) (F : I -> set T),
        (\bigcap_ i (F i)):#R `<=`  \bigcap_ i ((F i):#R).
    Proof.
      by move => R F;apply: Fset_bigcap.
    Qed.

    Lemma Aset_stableU: forall (R : relation T) (F : I -> set T),
        (forall i, (F i):#R `<=` (F i)) -> (\bigcup_ i (F i)):#R `<=` (\bigcup_ i (F i)).
    Proof.
      by move => R F H1;apply: Fset_stableU.
    Qed.

    Lemma Aset_stableI: forall (R : relation T) (F : I -> set T),
        (forall i, (F i):#R `<=` (F i)) -> (\bigcap_ i (F i)):#R `<=` (\bigcap_ i (F i)).
    Proof.
      by move => R F H1;apply: Fset_stableI.
    Qed.
    
    Lemma Aset_stableIf: forall (R : relation T) (A B: set T),
        A:#R `<=` A -> B:#R `<=` B -> (A `&` B):#R  `<=` A `&` B.
    Proof.
      by move => R A B ? ?;apply: Fset_stableIf.
    Qed.
    
    Lemma Aset_0 : forall (R : relation T), set0:#R `<=` set0.
    Proof.
      by move => R x [y [_ H1]].
    Qed.
    
    Lemma Aset_T : forall (R : relation T), setT:#R `<=` setT.
    Proof.
      by []. 
    Qed.

    (** * topology *)
    Definition To (R : relation T) := 
      [ set O | O:#R `<=` O].
    
    Lemma To_stableU: forall (R : relation T) (F : I -> set T),
         (forall i, ((To R) (F i))) -> (To R) (\bigcup_ i (F i)).
    Proof.
      by move => R F ?;apply:Aset_stableU.
    Qed.

    Lemma To_stableI: forall (R : relation T) (F : I -> set T),
         (forall i, ((To R) (F i))) -> (To R) (\bigcap_ i (F i)).
    Proof.
      by move => R F ?;apply:Aset_stableI.
    Qed.
    
    Lemma To_sset0: forall (R : relation T), (To R) set0. 
    Proof.
      by move => R;apply:Aset_0.
    Qed.

    Lemma To_ssetT: forall (R : relation T), (To R) setT. 
    Proof.
      by move => R;apply:Aset_T.
    Qed.
    
    (** * properties of open sets *)
    Lemma Ropen1: forall (R : relation T) (X: set T),
        R.*#X = X <-> R.*#X `<=` X.
    Proof.
      move => R X;split => [-> | H1];first by [].
      have H2: X `<=` R.*#X
        by rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D;apply: subsetUl.
      by rewrite eqEsubset.
    Qed.

    Lemma Ropen2: forall (R : relation T) (X: set T),
        R.*#X `<=` X <-> R.+#X `<=` X.
    Proof.
      move => R X;rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D.
      split => [ H1 | H1].
      - have H2: R.+#X `<=` X `|` R.+#X by apply: subsetUr.
        by apply: (subset_trans H2 H1).
      - have H2: X `<=` X by [].
        have H3: X `|` R.+#X `<=` X `|` X by apply: setUSS.
        by move: H3;rewrite setUid.
    Qed.

    Lemma Ropen3: forall (R : relation T) (X: set T),
        R#X `<=` X -> forall (n: nat), R^(n.+1)#X `<=` X.
    Proof.
      move => R X H1 n. 
      elim: n => [ | n H2]; first by rewrite iter1_id.
      have H3: R^(n.+2)#X = (R^(n.+1) `;` R^(1))#X
        by rewrite -iter_compose addn1.
      rewrite H3 -Fset_comp iter1_id.
      have H4: R^(n.+1)#(R#X) `<=` R^(n.+1)#(X) by apply: Fset_inc1.
      by apply: (subset_trans H4 H2).
    Qed.

    Lemma Ropen4: forall (R : relation T) (X: set T),
        R.+#X `<=` X <-> R#X  `<=` X.
    Proof.
      move => R X;split => [H1 | H1 x [y [H2 H3]]].
      - have H2:  R `<=` R.+ by apply: iter1_inc_clos_trans.
        have H3: R#X  `<=` R.+#X by apply: Fset_inc.
        by apply: (subset_trans H3 H1).
      - have [n H4]: exists (n:nat), R^(n.+1) (x,y) by apply: clos_t_iterk.
        have H5: R^(n.+1)#X x by (exists y).
        have H6: R^(n.+1)#X `<=` X by apply: (Ropen3 H1).
        by move: H5 => /H6 H5.
    Qed.

    Lemma Ropen5: forall (R : relation T) (X: set T),
        R#X  `<=` X -> (X.^c :#R ) `&` X = set0.
    Proof.
      move => R X H1.
      rewrite empty_notexists => -[z /inP [[w [H2 H3]] H4]].
      by have /H1 H5: R#X w by (exists z).
    Qed.

    Lemma Ropen6: forall (R : relation T) (X: set T),
        R#X  `<=` X -> (X.^c :#R ) `<=` X.^c.
    Proof.
      by move => X H1;rewrite -disjoints_subset;apply: Ropen5.
    Qed.
    
    (** * Closure of a set *)
    
    Definition T_closure (R : relation T) (Y: set T) (X: set T) 
      := Y = R.*#Y /\ X`<=` Y /\ (forall Z, Z = R.*#Z /\ X `<=` Z -> Y `<=` Z).
    
    Lemma T_closure_iff: forall (R : relation T) (Y: set T) (X: set T),
        T_closure R Y X <-> Y = R.*#X.
    Proof.
      move => R Y X.
      have H4: R.*#X = R.*#(R.*#X) by rewrite Fset_comp compose_rt_rt.
      have H5: X `<=` R.*#X by rewrite -DuT_eq_Tstar -Fset_union_rel Fset_D;apply: subsetUl.
      split  => [ [H1 [H2 H3]] | H1].
      - have H6: Y `<=`  R.*#X by apply: H3.
        have H7: R.*#X `<=` Y by rewrite H1; apply: Fset_inc1 .
        by rewrite eqEsubset.
      - split;rewrite H1;first by[].
        split;first by [].
        move => Z [H2 H3].
        have H6:  R.*#X `<=`  R.*#Z by apply: Fset_inc1 .
        by rewrite H2.
    Qed.
    
  End test1.

  Section order.

    Context (disp : Order.disp_t).
    Variable (T : porderType disp).
    
    Definition downset (X: set T) := [set y :T | exists x, X x /\ (y <= x)%O].
    Definition upset (X: set T) := [set y :T | exists x, X x /\ (x <= y)%O].
    


  End order.

End Tcs.











