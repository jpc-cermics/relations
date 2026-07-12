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

(******************************************************************************)
(* Some results for finite binary relations over a finType T                  *)
(******************************************************************************)

From HB Require Import structures.

Set Warnings "-parsing -coercions".
From mathcomp Require Import all_boot seq order finset boolp classical_sets contra. 
From mathcomp Require Import zify. (* enabling the use of lia tactic for ssrnat *)
Set Warnings "parsing coercions".
From RL Require Import  seq1 seq2 rel paper_meunier_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope. (* we can use %classic *)
Local Open Scope set_scope. (* we can use %SET *)

Definition fin_relation (T: finType) := {set (T * T)}.
Notation "{ 'relation' T }" := (fin_relation T) (format "{ 'relation'  T }"): type_scope.

Section FinsetToClassical.
  (** * from {set T} to (set T) classicals_sets and finTYpe *) 
  (** * from fin_relation {set T} to relation {set T} *)
  
  Variable (T : finType).
  Implicit Types (A B : {set T}) (x: T).
  
  Definition set_of_fin A : set T := [set x | x \in A ].
  Notation "[ ':set:' A ]" := (set_of_fin A) (format "[ ':set:'  A ]").
  (* Coercion set_of_fin : set_of >-> set. *)
  
  (* reverse conversion which works for finType *)
  Definition fin_of_set (A: set T) : {set T} := [set x in A]. 
  Notation "[:fin: A ]" := (fin_of_set A).    
  
  Lemma in_set_of_fin A x: x \in [:set: A] <-> x \in A.
  Proof.  by rewrite /set_of_fin in_setE. Qed.
  
  Lemma in_fin_of_set (A: set T) x: x \in [:fin: A] <-> x \in A.
  Proof. by split => [H | H];[by rewrite inE in H | rewrite inE]. Qed.
  
  Lemma in_finP A x: reflect (x \in [:set: A]) (x \in A).
  Proof.  by apply: (iffP idP);move/in_set_of_fin. Qed.
  
  Lemma fin_setInvol (A: {set T}): [:fin: [:set: A]] = A.
  Proof. 
    apply/setP => x; case H1: (x \in A).
    + by move: H1 => /in_set_of_fin/in_fin_of_set ->.
    + move: H1 => /negP/in_set_of_fin/in_fin_of_set H1.
      by case H2: (x \in [:fin:[:set:A]]).
  Qed.
  
  Lemma set_finInvol (A: set T): [:set: [:fin: A]] = A.
  Proof. 
    rewrite predeqE => x. 
    split => [/inP/in_set_of_fin/in_fin_of_set/inP // | /inP H1].
    by rewrite -inP in_set_of_fin in_fin_of_set.
  Qed.
  
  Lemma set_of_fin0 : [:set: finset.set0] = set0.
  Proof.
    rewrite predeqE => x.
    split;rewrite -in_setE;last by rewrite in_set0.
    by move => /in_set_of_fin;rewrite finset.in_set0. 
  Qed.
  
  Lemma set_of_finU A B: 
    [:set: (A :|: B)] = [:set: A] `|` [:set: B].
  Proof.
    rewrite predeqE => x.
    rewrite -[set_of_fin _ x]in_setE -[(_ `|` _) x]in_setE.
    rewrite in_set_of_fin finset.in_setU.
    split.
    by move => /orP [? | ?];apply/inP;[left| right];apply/inP/in_finP.
    by move/inP => [/inP/in_finP -> |/inP/in_finP ->];[rewrite orTb| rewrite orbT].
  Qed.
  
  Lemma set_of_finI A B : 
    set_of_fin (A :&: B) = (set_of_fin A) `&` (set_of_fin B).
  Proof.
    rewrite predeqE => x.
    rewrite -[set_of_fin _ x]in_setE -[(_ `&` _) x]in_setE.
    rewrite in_set_of_fin finset.in_setI.
    split;last by move => /inP [/inP/in_finP -> /inP/in_finP ->].
    move => /andP [/in_finP ? /in_finP ?].
    by rewrite inP;split;by rewrite -inP.
  Qed.
  
  Lemma set_of_fin_inj: injective set_of_fin.
  Proof.
    move => A B;rewrite predeqE -setP => /[swap] x /(_ x) H1.
    case H2: (x \in A);first by move/in_finP: H2 => /inP/H1/inP/in_finP ->.
    case H3: (x \in B);last exact.
    by move/in_finP: H3 H2 => /inP/H1/inP/in_finP ->.
  Qed.

  Lemma set_of_sfin v:  [:set: [set v]] = [set v]%classic.
  Proof.
    rewrite predeqE => x. 
    split;first by rewrite -inP in_set_of_fin inE => /eqP ->.
    by move => ->;rewrite -inP in_set_of_fin inE.
  Qed.

  Lemma set_of_set0 :  [:set: finset.set0] = set0.
  Proof.
    by rewrite predeqE => x;split;[rewrite -inP in_set_of_fin inE |].
  Qed.

End FinsetToClassical.

Notation "[ ':set:' A ]" := (set_of_fin A) (format "[ ':set:'  A ]").
Notation "[ ':fin:' A ]" := (fin_of_set A) (format "[ ':fin:'  A ]").

Section Finite. 
  (** * for a finType we have ~ (iic_inj R) *)
  Variable (T : finType).
  Implicit Types (R U O D: relation T).

  Definition Sink R v := forall w, ~ R (v,w).
  Definition vRloop R v := forall w, R (v, w) -> R(w,v).
  
  Lemma Sink_to_Rloop R v: Sink R v -> vRloop R v.
  Proof. by move => + w H1 => /(_ w) H2. Qed.
  
  Lemma fin_not_iic_inj R: ~ (iic_inj R). 
  Proof. 
    move => [f [_ finj]].
    have inj_restrict : injective (fun i : 'I_(#|T|).+1 => f i)
      by move=> x y /finj Exy;apply/val_inj. 
    move: (leq_card _  inj_restrict) => H1.
    by rewrite card_ord ltnn in H1. 
  Qed.

  Lemma fin_not_iic R: (sporder R) -> ~ (iic R).
  Proof.
    move => /[dup] Hsp /sporder_antisym Ha.
    by move: (@fin_not_iic_inj R) => H1 /(sporder_iic_injective R Hsp)H2. 
  Qed.
  
  Lemma fin_rloop R: (NotEmpty T) -> (sporder R) -> exists v, (vRloop R v).
  Proof.
    move => Hne /[dup] /fin_not_iic Hniic /sporder_asym/AsymEq Has.
    by rewrite -Has in Hniic;move: (@notiic_rloop _ R Hne Hniic). 
  Qed.
  
  Lemma fin_sink R: (NotEmpty T) -> (sporder R) -> exists v, (Sink R v).
  Proof.
    move => Hne /[dup] /sporder_asym Has Hsp.
    move: (fin_rloop Hne Hsp) => [v H1].
    by exists v;move => w /[dup] Rvw /[dup] /Has nRwv /H1 Rwv. 
  Qed.
  
  Lemma fin_rloop1 R U: (NotEmpty T) -> (sporder R)
                      -> exists v, (v)_:#(R) `<=` U#_(v).
  Proof.
    move => Hne Hsp;move: (@fin_sink _ Hne Hsp) => [v Rl].
    exists v;move: Rl => /[swap] w /(_ w) Rl.
    by rewrite /Aset 2!Fset_s => ?.
  Qed.
  
  Lemma fin_rloop2 O R D:
    (NotEmpty T) -> (sporder O) -> R `<=` O -> exists v, (v)_:#(R) `<=` D#_(v).
  Proof.
    move => Hne Hsp Hinc;move: (@fin_rloop1 O D Hne Hsp) => [v H1].
    exists v.
    have H2: (v)_:#R `<=`  (v)_:#O 
      by rewrite /Aset;apply: Fset_inc;apply: inverseS.
    by apply: (@subset_trans T _ _ _ H2 H1). 
  Qed.
  
End Finite. 

Reserved Notation "A [:<=:] B" (at level 4, no associativity). 
Reserved Notation "A [:<= R :] S" (at level 4, no associativity). 

(** * leSet_fin: leSet version for finite sets and a finite relation on T *)
Definition leSet_fin (T: finType) (R : relation T) : {relation {set T}} := 
  [set AB : {set T}*{set T} | ([:set: AB.1], [:set: AB.2]) \in (@leSet T R) ].
Notation "A [:<= R :] B" := ((A,B) \in (leSet_fin R)).

Section leSet_fin_props.
  (** * reflection lemma for leSet_fin and leSet *)
  Variable (T : finType).
  Implicit Type (A B: {set T}). 

  Lemma leSet_finE (R : relation T) A B: 
    (A,B) \in (leSet_fin R) <->  (([:set: A], [:set: B]) \in (@leSet T R)).
  Proof. 
    rewrite -in_set_of_fin. 
    split => [/in_finP H1 | ?].
    by rewrite finset.in_set /= in H1.
    by rewrite in_set_of_fin finset.in_set.
  Qed.
  
  Lemma leSet_finP (R : relation T) A B: 
    reflect ((A,B) \in (leSet_fin R)) (([:set: A], [:set: B]) \in (@leSet T R)).
  Proof. by apply: (iffP idP);move/leSet_finE. Qed.
  
End leSet_fin_props.

Section RelIndep_fin. 
  (** * finite Independent sets  *)
  
  Variable (T : finType).
  Implicit Types (R : relation T) (S: {set T}).
  
  Definition RelIndep_fin R S: bool :=
  [forall x in S, forall y in S, (x == y) || ~~ ((x, y) \in R)].
  
  Local Lemma RelIndep_P R S:
    reflect (forall x y, x \in S -> y \in S -> x != y -> ~~ ((x,y) \in R))
      (RelIndep_fin R S).
  Proof.
    apply: (iffP forall_inP) => [H x y xS yS xy | H x xS].
    - move/(_ x xS)/forall_inP/(_ y yS): H => /orP [ |//].
      by rewrite (negbTE xy).
    - apply/forall_inP => y yS;apply/orP.
      by case: (eqVneq x y) => [-> | xy];[left | right; apply: H].
  Qed.

  Lemma RelIndepE R S: (RelIndep R [:set: S]) <-> (RelIndep_fin R S).
  Proof.
    split => [H1| /RelIndep_P H1 x y /in_finP xS /in_finP yS Hxy].
    + apply/RelIndep_P => x y /in_finP xS /in_finP yS Hxy.
      move: H1 => /(_ x y xS yS).
      contra => /inP H1. 
      split; last exact.
      by move: Hxy => /[swap] ->;rewrite eqxx.
    + have H2: x != y by apply/negP => /eqP H3.
      move: H1 => /(_ x y xS yS H2) H1 /inP H3.
      by rewrite H3 in H1.
  Qed.
  
  Lemma RelIndepP R S: 
    reflect (RelIndep R [:set: S]) (RelIndep_fin R S).
  Proof. by apply: (iffP idP);move/RelIndepE. Qed.
  
  Lemma RelIndep_fin_subset R (S S': {set T}) :
    S' \subset S -> RelIndep_fin R S -> RelIndep_fin R S'.
  Proof.
    move=> /fintype.subsetP SS' /RelIndepP H; apply/RelIndepP. 
    by apply: (RelIndep_Ir SS' H).
  Qed.
  
  Lemma RelIndep_fin0 R: RelIndep_fin R finset.set0.
  Proof. by apply/RelIndepP;rewrite set_of_set0;apply/RelIndep_set0. Qed.
         
  Lemma RelIndep_fin1 R a : RelIndep_fin R [set a].
  Proof. apply/RelIndepP;rewrite set_of_sfin;apply/RelIndep_set1. Qed.

  Lemma RelIndep_fin_Iv R S: RelIndep_fin R S <-> RelIndep_fin R^-1 S.
  Proof. 
    by split;rewrite -RelIndepE;move => /RelIndep_Iv/RelIndepP;
                                       [| rewrite inverseK].
  Qed.

  Lemma RelIndep_fin_IE R S: RelIndep_fin R S = RelIndep_fin R^-1 S.
  Proof. 
  Admitted.
  
End RelIndep_fin. 

#[local] Set Warnings "-projection-no-head-constant,-redundant-canonical-projection".

Section SubSetPType.
  (** * defining a new finType isomorphic to {S : {set T} | P S} *)
  Variables (T : finType)  (P : pred {set T}).
  Record setP_type := SetP { setP_val : {set T}; setP_proof : P setP_val }.

  (* subType structure *)
  HB.instance Definition _ := [isSub for setP_val].
  HB.instance Definition _ := [Finite of setP_type by <:].
  (* explicit coercion *)
  Coercion setP_val : setP_type  >-> set_of. 
  
End SubSetPType.
#[local] Set Warnings "+projection-no-head-constant,+redundant-canonical-projection".

Module fin_Maximal.
  (** * There's always a maximal element in a finite nonempty poset *)
  (** we consider here the simplest case *)
  (** and give a proof by recursion 
      we first give the proof for a sequence(seq T) 
      and then use mem_enum to have a finite sequence 
      representation of a finite set. *)
  (** Note that this proof is valid for R: relation T 
      R: {relation T} is not requested *)

  Section fin_maximal.
    
  Variables (T: finType).
  Implicit Types (m : T) (s : seq T) (R: relation T).

  Definition seq_maximal m s R : Prop :=
    forall x, x \in s -> R (m,x) -> m = x.

  Definition maximal m R: Prop := forall x,  R (m,x) -> m = x.
  
  #[local] Lemma seq_has_maximal_step (s : seq T) (h : T) R:
    porder R -> (exists m, m \in s /\ seq_maximal m s R) \/  s = [::]
    ->  exists m, m \in h :: s /\ seq_maximal m (h :: s) R.
  Proof.
    move => [Hr Ha Ht] [[m [Hm Hmax]] | ->].
    (* s is non-empty with maximal m *)
    + move: (EM (R (m,h))) => [Rmh | hle_m].
      ++ (* R (m,h)  *)
        exists h; split;first by rewrite in_cons eqxx.
        move=> x; rewrite in_cons => /orP [/eqP -> // | Hxs] Hlt.
        have Rmx: R (m,x) by apply: (Ht m h x Rmh Hlt).
        have meqx: m = x by apply: (Hmax x Hxs Rmx).
        move: Rmh;rewrite meqx => Rxh.
        rewrite /antisymmetric in Ha.
        by move: (Ha h x Hlt Rxh).
      ++ (* ~ (R (m,h)) *)      
        exists m; split;first by rewrite in_cons;rewrite Hm orbT. 
        move => x; rewrite in_cons => /orP [/eqP -> ? //| H1 H2].
        by move: (Hmax x H1 H2).
    + (exists h);split;first by rewrite mem_seq1.
      by move => x; rewrite mem_seq1 => /eqP ->.
  Qed.
  
  #[local] Lemma seq_has_maximal R: 
    porder R -> forall s, ~ (s = [::]) -> (exists m, m \in s /\ seq_maximal m s R).
  Proof.
    move => ?;elim => [// | a s Hr _ ].
    apply: seq_has_maximal_step;first by [].
    by move: (EM (s = [::])) => [-> | /Hr ?];[right | left].
  Qed.    
  
  Lemma has_maximal R: porder R -> (exists x, x\in T) -> (exists m, maximal m R).
  Proof.
    move => Hp [x -];rewrite -mem_enum => Hx.
    have H2: ~ (enum T = [::]) by move: Hx => /[swap] ->.
    move: Hp => /seq_has_maximal/(_ (enum T) H2) [m [Hm HM]]. 
    exists m;move: HM => /[swap] x' /(_ x') HM H5.
    by apply: HM;[rewrite  mem_enum |].
  Qed.
  
  End fin_maximal.

End fin_Maximal.

Export fin_Maximal.

Section SubSetPType_order.
  (** * When O is a sporder then [:<=: O] restricted to M-independent sets is a porder *)
  
  Context (T : finType).
  Implicit Types (O R M: relation T) (S: {set T}).
  
  Definition setRM_fin R M S := (asbool ([:set: S]:#R `<=` M#([:set: S]))).

  Definition prekernel_fin O R M: pred {set T} := 
    fun S => (RelIndep_fin O S) && ((setRM_fin R M S) && (([:set: S]) != set0)).
  
  (** * setIndep doit s'appeller  prekernelfinType ? *)
  Definition setIndep O R M := setP_type (prekernel_fin O R M). 

  Lemma prekernel_fin_Iv O R M S: 
    prekernel_fin O R M S = prekernel_fin O^-1 R M S.
  Proof.
    by rewrite /prekernel_fin RelIndep_fin_IE.
  Qed.
  
  Lemma prekernelE O R M S: 
    prekernel_fin O R M S <->
    RelIndep O [:set: S] /\ setRM R M [:set: S] /\ [:set: S] != set0.
  Proof.
    split.
    by move => /andP [/RelIndepE H1 /andP [/asboolP H2 H3]].
    move => [H1 [H2 H3]].
    apply/andP;rewrite -RelIndepE H3 andbT.
    split;first exact.
    by  apply/asboolP.
  Qed.
  
  Lemma prekernel_notempty O R M 
    (A1: NotEmpty T) (At: sporder O^-1) (Au: R `<=` O^-1):
    exists v, prekernel_fin O R M [set v].
  Proof.
    move: (At) (@fin_not_iic_inj T O^-1) => /[dup] Hsp [H1 /[dup] Ht /Tclos_iff H2] H3.
    have H4: ~(iic O^-1)
      by move => /(@sporder_iic_injective _ _ At ) ?.
    move: (@fin_rloop2 T O^-1 R M A1 At Au) => [v H6].
    exists v.
    apply/andP.
    split;first by apply: RelIndep_fin1.
    apply/andP.
    split;first by apply/asboolP;rewrite /setRM_fin set_of_sfin.
    rewrite set_of_sfin.
    apply/asboolP => H.
    have H7: [set v]%classic v by exact.
    by rewrite H in H7.
  Qed.
  
  Lemma leSet2_porder O R M :
    sporder O -> 
    @porder (setIndep O R M) 
      [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic.
  Proof.
    move => H_sp.
    split => [A /= | A B /= Ha Hb | A B C /= Ha Hb].
    + (* reflexive *)  apply: le_refl.
    + (* antisymmetric *) 
      move: (valP A) => /andP[/RelIndepE Pa _].
      move: (valP B) => /andP[/RelIndepE Pb _].
      move: (le_antisym_if_sp H_sp Pa Pb Ha Hb) => /set_of_fin_inj/eqP H5.
      by apply/eqP;rewrite -val_eqE.
    + (* transitive *)
      move: H_sp => [_ H1];move: (le_trans_if_tr H1) => H2. 
      by move: H2 => /(_ [:set:\val A] [:set:\val B] [:set:\val C] Ha Hb) H2.
  Qed.
  
  Lemma exists_setIndep O R M 
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1):
      (exists x : setIndep O R M, x \in {: (setIndep O R M)}).
  Proof.
    move: Asp => /sporder_inv Asp.
    move: (@prekernel_notempty O R M A1 Asp Au) => [v Pv].
    by exists (SetP Pv).
  Qed.
  
  Lemma Maximal_fin O R M 
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1):
    exists (m: (setIndep O R M)),
      @maximal (setIndep O R M) m [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic.
  Proof.
    move: (Asp) => /sporder_inv Asp'. 
    move: (leSet2_porder R M Asp) => po.
    pose proof (@exists_setIndep O R M A1 Asp Au) as Hne.
    by move: (@has_maximal (setIndep O R M) 
            [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic
         po Hne).
  Qed.
  
  Lemma Maximal O R M
    (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1):
    exists S, prekernel_fin O R M S /\ (forall U, prekernel_fin O R M U ->
                                    [:set: S] [<= O] [:set: U] -> S = U).
  Proof.
    move: (@Maximal_fin O R M A1 Asp Au)  => [S H3].
    exists S;move: (valP S) => Pr;split; first exact.
    move => U H4; move: H3 => /(_ (SetP H4)) H3.
    by move => /H3/eqP ?;apply/eqP. 
  Qed.

  Variables (x y z :T ).
  Compute (nth x [:: x;y] 1).
  Compute (size [:: x;y]).

  Definition Inc O R M (SS: (setIndep O R M)*(setIndep O R M))
    := [:set: (val SS.1)] `<=` [:set: (val SS.2)].
  
  Lemma Inc_Tr  O R M: transitive (@Inc O R M).
  Admitted.

  Lemma poo O R M  (Sq: seq (setIndep O R M)) (S1:(setIndep O R M)) : 
    0 < size Sq
    -> (forall j, j <= (size Sq) -> ~ ([:set: (val (nth S1 (S1::(rcons Sq S1)) j))] = 
                 [:set: (val (nth S1 (S1::(rcons Sq S1)) j.+1))]))
    -> exists j, j <= (size Sq) /\ exists aj, aj \in (val (nth S1 (S1::(rcons Sq S1)) j))
                 /\ ~( aj \in (val (nth S1 (S1::(rcons Sq S1)) j.+1))).
  Proof.
    move => H1. contra => H2.
    have H4: forall j, j <= (size Sq) -> [:set: (val (nth S1 (S1::(rcons Sq S1)) j))] `<=`
                    [:set: (val (nth S1 (S1::(rcons Sq S1)) j.+1))]
        by move => j Hs b;rewrite -inP => /in_finP/(H2 j Hs)/in_finP/inP.
    
    rewrite -(@allL_nth' (setIndep O R M) (@Inc O R M) Sq S1 S1 S1
      ) in H4.
        
    move: (H4) => /(@allL_All (setIndep O R M)) H4'.
    move: (@Inc_Tr O R M) => /Tclos_iff H5.
    rewrite -H5 in H4'.
    
    have H6: forall S:(setIndep O R M) , S \in (S1 :: Sq) -> ((@Inc O R M) (S, S1)).
    move => S H7.
    move: (@allset_in _ (S1 :: Sq) S (Inc (M:=M))#_(S1) H7 H4').
    by move => /inP/Fset_s HH. 

    move: H4 => /(@allL_AllA (setIndep O R M)) H4''.
    rewrite -H5 in H4''.

    have H6': forall S:(setIndep O R M) , S \in (rcons Sq S1) -> ((@Inc O R M) (S1, S)).
    move => S H7.
    move: (@allset_in _ (rcons Sq S1) S ((S1)_:#(Inc (M:=M))) H7 H4'').
    by move => /inP/Fset_s HH. 
    
    have H8:  forall S : setIndep O R M, S \in Sq -> S = S1.
    move => S P1.
    have P2: S \in S1 :: Sq by rewrite in_cons P1 orbT.
    have P3: S \in rcons Sq S1 by rewrite in_rcons P1 orTb.
    move: P2 P3 => /(H6 S) P2 /(H6' S) P3.

    have P4: [:set: (val S)] = [:set: (val S1)].
    rewrite eqEsubset. by split.
    by move: P4 => /set_of_fin_inj/val_inj P4.

    exists 0. lia.
    rewrite /= // nth_rcons H1. 
    have P5: (nth S1 Sq 0) \in Sq.
    by apply: mem_nth.
    by move: P5 => /H8 ->.
  Qed.

End SubSetPType_order.

Section ChampetierExt_Theorem.

  Context (T : finType) (O R B: relation T).
  Implicit Types (O R B: relation T) (X: {set T}).
  
  Context (A2 : Assumption2 R) (A6 : Assumption6 B (M R B) O) 
    (A7 : Assumption7 R B (M R B)) (A8 : Assumption8 R B (M R B)).
  Context (A1: NotEmpty T) (Asp: sporder O) (Au: R `<=` O^-1).
  Context (Apk : forall X , RelIndep O [:set: X] <->  RelIndep (M R B) [:set: X]).
  
  Lemma prekernelP S: 
    (prekernel_fin O R (M R B) S) <-> preKernel R (M R B) [:set: S].
  Proof. by rewrite (@prekernelE T O R (M R B) S) Apk. Qed.
  
  Lemma maximal_mabsorbant S:
    (prekernel_fin O R (M R B) S) /\ (forall U, prekernel_fin O R (M R B) U ->
                                  [:set: S] [<= O] [:set: U] -> S = U)
    -> Mabsorbant R B [:set: S].
  Proof.
    contra; move => H1 /prekernelP Hpk.
    have H3: Non_Mabsorbant R B [:set: S]
      by move: H1 => [y H1] H3;exists y;rewrite inP;
                    split;[ |rewrite notin_setE in H3;rewrite inP].
    
    move: (@extend T R B O [:set: S] A2 A6 A7 A8 Hpk H3) 
        => [S' [Hpre [H7 [x' [H8 H9]]]]].
    exists [:fin: S'].
    by rewrite prekernelP set_finInvol.
    split;first by  rewrite set_finInvol.
    apply/negP => /eqP Heq.
    by rewrite Heq set_finInvol in H9.
  Qed.
  
  Lemma Kernel_ChampetierExt: 
    exists (S : {set T}), RelIndep (M R B) [:set: S] /\ Mabsorbant R B [:set: S].
  Proof.
    (* There exist a maximal set *)
    move: (@Maximal T O R (M R B) A1 Asp Au) => [S Hm].
    move: Hm => /[dup] /maximal_mabsorbant Ma [/prekernelP [Hpk _] _].
    by (exists S).
  Qed.

End ChampetierExt_Theorem.

Section simpleGraph. 

  Context (T : Type).
  Implicit Types (G D O Re: relation T).

  Definition simpleGraph G := symmetric G /\ irreflexive G.
  Definition Direction G D := D `|` D^-1 = G. 
  Definition Orientation G O := Direction G O /\ asymmetric O.

  Lemma RelIndep_sym Re S: (RelIndep Re S) <-> (RelIndep (Re `|` Re^-1) S).
  Proof.
    split => [+ x y Hx Hy Hne|+ x y Hx Hy Hne].
    have Hne': ~ (y = x). by move => H1;rewrite H1 in Hne.
    by move => /[dup] /(_ y x Hy Hx Hne') H1 /(_ x y Hx Hy Hne) H2 [H3 | H3].
    by move => /(_ x y Hx Hy Hne);contra => ?;left.
  Qed.
  
  Lemma direction_relIndep G D S: 
    Direction G D -> (RelIndep D S <-> RelIndep G S).
  Proof. by move => Hd;rewrite RelIndep_sym Hd. Qed.

  Lemma orientation_relIndep G D S: 
    Orientation G D -> (RelIndep D S <-> RelIndep G S).
  Proof. by move => [Hd _];rewrite RelIndep_sym Hd. Qed.
  
End simpleGraph.

Section Champ.

  Context (T : finType) (G D O: relation T).
  
  Context (Asg: simpleGraph G).
  Context (Ao: Orientation G O).
  Context (Ad: Direction G D).

  Definition R := D `&` O^-1.
  Definition B := D `&` O.

  Context 
    (A1: NotEmpty T) 
    (Asp: sporder O)
    (A6 : Assumption6 B (M R B) O) 
    (A7 : Assumption7 R B (M R B))
    (A8 : Assumption8 R B (M R B)).
  
  Lemma RB: (M R B) = D.
  Proof.
    have H1:  R `<=` D. by rewrite /R;apply: subIsetl.
    have H2:  B `<=` D. by rewrite /R;apply: subIsetl.
    rewrite predeqE => -[x y].
    split => [[/H2 H0 | /H1 H0] // | H3].
    case H4: ((x,y) \in O).
    + move: H4 => /inP H4.
      ++ case H5: ((y,x) \in O).
         move: H5 => /inP H5.
         by right;split.
         by left;split.
    + case H5: ((y,x) \in O).
      move: H5 => /inP H5.
      by right;split.
      (** (x, y) \in O) = false /\ (y, x) \in O) = false *)
      (** is not possible *)
      have H6: D `|` D^-1 = G by [].
      have H7: O `|` O^-1 = G by move: (Ao) => [Do _].
      have H8:  D `|` D^-1 = O `|` O^-1. by rewrite H6 H7. 
      have [/inP //| H9]: (O `|` O^-1) (x,y) by rewrite -H8; left.
      by rewrite H4.
      have: (y,x) \in O by rewrite inP.  
      by rewrite H5.
  Qed.
  
  Lemma AspIv: sporder O^-1.
  Proof. by apply: sporder_inv. Qed.
  
  Lemma Au:  R `<=` O^-1. 
  Proof. by rewrite /R;apply: subIsetr. Qed.

  Lemma Onoticc: ~ (iic  O^-1). 
  Proof. by apply: (@fin_not_iic _ O^-1 AspIv). Qed.
  
  Lemma Rnotiic: ~ (iic R).
  Proof. by move: Onoticc => ? /(@iic_sub T R O^-1 (Au)) ?. Qed.

  Lemma Apk:  forall X , RelIndep O [:set: X] <->  RelIndep (M R B) [:set: X].
  Proof. move => X. rewrite RB. 
         rewrite (@direction_relIndep T G D [:set: X] Ad).
         by rewrite (@orientation_relIndep T G O [:set: X] Ao).
  Qed.
  
  Lemma Rsym : asymmetric R.
  Proof.
    move => x y /Au H1 /Au H2.
    by move: H1 Ao => + [_ /(_ x y) Ha] => /Ha H3.
  Qed.
  
  Lemma haveA2 : ~ (iic (Asym R)).
    move: Rsym => /AsymEq ->;apply: Rnotiic.
  Qed.

  Lemma haveA6 : forall x y : T, B (x, y) /\ ~ (M R B) (y, x) -> O (x, y).
  Proof. by move => x y [[_ H1] _]. Qed.

  Lemma Kernel_Champetier: 
    exists (S : {set T}), RelIndep (M R B) [:set: S] /\ Mabsorbant R B [:set: S].
  Proof.
    by pose proof (@Kernel_ChampetierExt T O R B (haveA2) (haveA6)
                     A7 A8 A1 Asp (Au) (Apk)).
  Qed.
  
End Champ.

Section test.

Variable T : Type.
Variable s : seq T.   (* s = [:: x1; x2; ...; xk] *)
Variable x1: T.
Hypothesis Hs : ~ (s = [::]).

Definition f (n : nat) : T := nth x1 s (n %% size s).

Lemma f_periodic n : f (n + (size s)) = f n.
Proof. by rewrite /f (modnDr n (size s)). Qed.
  
End test.

