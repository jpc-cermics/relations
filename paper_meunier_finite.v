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

Section Finite. 
  (** * could be in rel.V *)
  (** * for a finType we have ~ (iic_inj R) *)
  Context {T : finType}.
  Implicit Types (U V W: relation T).

  Definition Sink U v := forall w, ~ U (v,w).
  Definition vRloop U v := forall w, U (v, w) -> U (w,v).
  
  Lemma Sink_to_Rloop U v: Sink U v -> vRloop U v.
  Proof. by move => + w H1 => /(_ w) H2. Qed.
  
  Lemma notF_to_notS U: 
    (exists (v0:T), (v0 \in setT)) -> (forall v, ~(vRloop U v)) -> (forall v, ~(Sink U v)). 
  Proof.
    by move => Hne;contra => -[x Hx];exists x;apply: Sink_to_Rloop.
  Qed.
  
  Lemma notS_to_total U: (forall v, ~(Sink U v)) <-> total_rel U.
  Proof. 
    split;contra => -[x Hx];exists x;first exact.
    by move:Hx => + y => /(_ y) Hx.
  Qed.
    
  Lemma sink2iic U: (nonempty [set: T]) -> (forall v, ~(Sink U v)) -> (iic U).
  Proof. 
    move => Hne  Hnsink. apply: DC;first by [].
    by move: Hnsink;contra;move => [x Hx];exists x. 
  Qed.
  
  Lemma cyclic U: (iic U) -> ( exists s, U.+ (s,s)). 
  Proof. move => [h Hhiic];by apply: cyclic. Qed.
  
  Lemma fin_not_iic_inj U: ~ (iic_inj U). 
  Proof. 
    move => [f [_ finj]].
    have inj_restrict : injective (fun i : 'I_(#|T|).+1 => f i)
      by move=> x y /finj Exy;apply/val_inj. 
    move: (leq_card _  inj_restrict) => H1.
    by rewrite card_ord ltnn in H1. 
  Qed.
  
  Lemma fin_not_iic U: (sporder U) -> ~ (iic U).
  Proof.
    move => /[dup] Hsp /sporder_antisym Ha.
    by move: (@fin_not_iic_inj U) => H1 /(sporder_iic_injective Hsp)H2. 
  Qed.
  
  Lemma fin_rloop U: (nonempty [set: T]) -> (sporder U) -> exists v, (vRloop U v).
  Proof.
    move => Hne /[dup] /fin_not_iic Hniic /sporder_asym/AsymEq Has.
    by rewrite -Has in Hniic;move: (@notiic_rloop _ U Hne Hniic). 
  Qed.
  
  Lemma fin_sink U: (nonempty [set: T]) -> (sporder U) -> exists v, (Sink U v).
  Proof.
    move => Hne /[dup] /sporder_asym Has Hsp.
    move: (fin_rloop Hne Hsp) => [v H1].
    by exists v;move => w /[dup] Rvw /[dup] /Has nRwv /H1 Rwv. 
  Qed.
  
  Lemma fin_rloop1 U V: 
    (nonempty [set: T]) -> (sporder U) -> exists v, (v)_:#(U) `<=` V#_(v).
  Proof.
    move => Hne Hsp;move: (@fin_sink _ Hne Hsp) => [v Rl].
    exists v;move: Rl => /[swap] w /(_ w) Rl.
    by rewrite /Aset 2!Fset_s => ?.
  Qed.
  
  Lemma fin_rloop2 U V W:
    (nonempty [set: T]) -> (sporder U) -> V `<=` U -> exists v, (v)_:#(V) `<=` W#_(v).
  Proof.
    move => Hne Hsp Hinc.
    move: (@fin_rloop1 U W Hne Hsp) => [v H1];( exists v).
    have H2: (v)_:#V `<=`  (v)_:#U 
      by rewrite /Aset;apply: Fset_inc;apply: inverseS.
    by apply: (@subset_trans T _ _ _ H2 H1). 
  Qed.
  
  Lemma NotCyclic_exists_sink U: 
    (nonempty [set: T]) ->  ~ (exists s, U.+ (s,s)) -> exists v, (Sink U v).
  Proof.
    move => Hne;contra => Hnsink.
    apply/cyclic/(sink2iic Hne) => v Hsink.
    by move: Hnsink Hsink => /(_ v) [x Rvx] /(_ x) nRvx.
  Qed.
  
  Lemma NotCyclic_exists_preabsorbant U V: 
    (nonempty [set: T]) ->  ~ (exists s, U.+ (s,s)) -> exists v, (v)_:#(U) `<=` V#_(v).
  Proof.
    (* use NotCyclic_exists_sink *)
    move => Hne Hncl;move: (NotCyclic_exists_sink Hne Hncl)=> [v Hsink].
    (* now prove that exists v, (Sink U v) ->  exists v, (v)_:#(U) `<=` V#_(v). *)
    exists v;move => y;rewrite /Aset Fset_s => Rvy.
    by move: Hsink => /(_ y) nRvy.
  Qed.
  
End Finite. 


Module BHExt.
  Section BHExt.
    (** * Extended Blida en H. Theorem *)
  
    Context {T: finType} (O R B: relation T).

    Definition M := B `|` R.

    Context (A2: Assumption2 R) (A6: Assumption6 B M O)
      (A7: Assumption7 R B M) (A8: Assumption8 R B M). 
    Context (A1: nonempty [set: T]) (Au: R `<=` O^-1).
    Context (Apk : forall X , RelIndep O X <-> RelIndep M X).
    Context (A_Onotcyclic: ~ (exists s, O.+ (s,s))).
    
    Lemma preKernelP S: 
      preKernel O R M S <-> preKernel M R M S.
    Proof. by rewrite /preKernel /= Apk. Qed.
    
    Lemma extend_pk X: preKernel M R M X -> ~ (absorbant M X) ->
                       exists X', preKernel M R M X' /\ X [<< O] X'.
    Proof.
      move => Hpk Hnma.
      move: (@extend T R B O X A2 A6 A7 A8 Hpk Hnma) => [X' [Hpk' Hrst]].
      by exists X'. 
    Qed.

    Lemma A0 S: S \in ((preKernel M R M) `&` (absorbant M).^c)
                -> exists S', S' \in (preKernel M R M) /\ (S [<< O] S').
    Proof.
      rewrite inE => -[Hpk Hna];move: (extend_pk Hpk Hna) 
              => [S' [/mem_set Hpk' [Hle Hd]]].
      by exists S'. 
    Qed.

    Lemma Oinv_notcyclic: ~ (exists s, O^-1.+ (s,s)).
    Proof. by rewrite -TclosIv. Qed.
    
    Lemma A1': exists S,  S \in (preKernel M R M).
    Proof.
      (* exists a sink and thus a preabsorbant node *)
      move: (@NotCyclic_exists_preabsorbant T O^-1 M A1 Oinv_notcyclic) => [v Hpa].
      (* [set v] is in (preKernel M R M). *)
      exists [set v]%classic;rewrite inE. 
      have Hinc:  (v)_:#R  `<=` (v)_:#O^-1 
          by rewrite /Aset;apply: Fset_inc;apply: inverseS.
      split;first by apply: RelIndep_set1.
      split;first by apply: (subset_trans Hinc _).
      + apply/negP => /eqP H.
        have Hv: [set v]%classic v by [].
        by rewrite H /= in Hv.
    Qed.
    
    Lemma choose: (exists h, (iic_fun ([<< O]%O) h) /\ (forall n, (h n) \in  (preKernel M R M)))
                  \/ (exists S, (S \in (preKernel M R M)) /\ S \in (absorbant M)).
    Proof.
      move: (@choose_sub _ ([<< O]%O) (preKernel M R M) (absorbant M).^c A0 A1')
          => [Hiic | [S [Hpk Hna]]].
      by left.
      right. exists S.
      split. by [].
      by move: Hna;rewrite 2!inE /= => /contrapT.
    Qed.
    
    (* we prove that the first condition 
       (exists h, (iic_fun ([<< O]%O) h) /\ (forall n, (h n) \in  (preKernel M R M)))
       would lead to cyclicity for relation O *)
    
    Lemma iic_to_allL  (h : nat -> (set T)):  
      (iic_fun ([<< O]%O) h) -> (forall n, (h n) \in  (preKernel O R M)) ->
      exists n p, h n = h (n+p+1)
             /\ allL ([<< O]%O) (mkseq (fun i => h (n + i+1)) p) (h n) (h n)
             /\ ((h n)::(mkseq (fun i => h (n + i+1)) p)) [\in] (preKernel O R M).
    Proof. 
      move => Hiic_fun Hpk.
      (* non injectivity prop as T is finType *)
      have [n [m Heq]]:  exists n p : nat, h n = h (n + p.+1)
          by apply: set_fin_codomain_prop.
      move: Hiic_fun => /f2allL /(_ n m) HallL.
      rewrite -addn1 addnA in Heq;rewrite -Heq in HallL. 
      by exists n, m;split;[|split;[|apply: f2in]].
    Qed.
    
    Lemma Ocyclic S Sq: 
      @allL (set T) ([<< O]%O) Sq S S
      -> (S::Sq) [\in] (preKernel O R M)
      ->  exists s, O.+ (s,s).
    Proof.
      move => A0 A3.
      move: (exists_g A0 A3) => [g [G1 [G2 [G3 G4]]]].
      move: (exists_h G2 G3 G4) => [h [H1 [H2 H3]]].
      move: (hmap' G1 H1 H2 H3) => Hhmap.
      move: (fin_codomain_prop (fun k => h(k*(size(S::Sq))))) => [n [p H4]].
      by exists (h (n * size (S :: Sq)));rewrite {2}H4;apply: Hhmap.
    Qed.
    
    Lemma iic_and_prekernels_to_cyclic (h : nat -> (set T)):
      (iic_fun ([<< O]%O) h) -> (forall n, (h n) \in  (preKernel O R M))
      -> exists s, O.+ (s,s).
    Proof.
      move => Hiic Hpk';move: (iic_to_allL Hiic Hpk') => [n [p [Ha [HallL Hpk]]]].
      by apply: (Ocyclic HallL Hpk).
    Qed.
    
    Lemma exists_kernel: exists S, S \in (preKernel M R M) /\ S \in (absorbant M).
    Proof.
      move: choose => [[h [Hiic Hk]] | H1];last by [].
      have HpkO: (forall n, (h n) \in  (preKernel O R M))
        by move => n; rewrite inE preKernelP -inE.
      by move: (iic_and_prekernels_to_cyclic Hiic HpkO) => HOcyclic.
    Qed.
    
  End BHExt.
End BHExt.

Export BHExt(exists_kernel).

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

  Lemma set_to_finK : cancel fin_of_set set_of_fin.
  Proof.
    move=> A;rewrite predeqE /fin_of_set /set_of_fin /= => x.
    by split => [|?];rewrite inE;[move => /asboolP|apply/asboolP].
  Qed.
  
  Lemma fin_to_setK : cancel set_of_fin fin_of_set.
  Proof.
    move=> A;apply/setP => x; case H1: (x \in A).
    + by move: H1 => /in_set_of_fin/in_fin_of_set ->.
    + move: H1 => /negP/in_set_of_fin/in_fin_of_set H1.
      by case H2: (x \in [:fin:[:set:A]]).
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
    by move => /orP [? | ?];apply/asboolP;[left| right];apply/asboolP/in_finP.
    by move/set_mem => [/mem_set/in_finP -> |/asboolP/in_finP ->];[rewrite orTb| rewrite orbT].
  Qed.

  Lemma set_of_finI A B : 
    set_of_fin (A :&: B) = (set_of_fin A) `&` (set_of_fin B).
  Proof.
    rewrite predeqE => x.
    rewrite -[set_of_fin _ x]in_setE -[(_ `&` _) x]in_setE.
    rewrite in_set_of_fin finset.in_setI.
    split;last by move => /set_mem [/mem_set/in_finP -> /mem_set/in_finP ->].
    move => /andP [/in_finP ? /in_finP ?].
    by rewrite inE;split;by rewrite -inE.
  Qed.
  
  Lemma set_of_fin_inj: injective set_of_fin.
  Proof.
    move => A B;rewrite predeqE -setP => /[swap] x /(_ x) H1.
    case H2: (x \in A);first by move/in_finP: H2 => /set_mem/H1/mem_set/in_finP ->.
    case H3: (x \in B);last exact.
    by move/in_finP: H3 H2 => /set_mem/H1/mem_set/in_finP ->.
  Qed.

  Lemma fin_of_set_inj: injective fin_of_set.
  Proof.
    move => A B;rewrite predeqE -setP => /[swap] x /(_ x).
    rewrite 2!inE => H1. 
    by split;move => /mem_set;[rewrite H1|rewrite -H1];apply/set_mem.
  Qed.
  
  Lemma set_of_sfin v:  [:set: [set v]] = [set v]%classic.
  Proof.
    rewrite predeqE => x. 
    split;first by rewrite -inE in_set_of_fin inE => /eqP ->.
    by move => ->;rewrite -inE in_set_of_fin inE.
  Qed.

  Lemma set_of_set0 :  [:set: finset.set0] = set0.
  Proof.
    by rewrite predeqE => x;split;[rewrite -inE in_set_of_fin inE |].
  Qed.

End FinsetToClassical.

Notation "[ ':set:' A ]" := (set_of_fin A) (format "[ ':set:'  A ]").
Notation "[ ':fin:' A ]" := (fin_of_set A) (format "[ ':fin:'  A ]").

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
  Implicit Types (m : T) (s : seq T) (U: relation T).

  Definition seq_maximal m s U : Prop :=
    forall x, x \in s -> U (m,x) -> m = x.

  Definition maximal m U: Prop := forall x,  U (m,x) -> m = x.
  
  Lemma seq_has_maximal_step s (t : T) U:
    porder U -> (exists m, m \in s /\ seq_maximal m s U) \/  s = [::]
    ->  exists m, m \in t :: s /\ seq_maximal m (t :: s) U.
  Proof.
    move => [Hr Ha Ht] [[m [Hm Hmax]] | ->].
    (* s is non-empty with maximal m *)
    + move: (EM (U (m,t))) => [Umh | hle_m].
      ++ (* U (m,h)  *)
        exists t; split;first by rewrite in_cons eqxx.
        move=> x; rewrite in_cons => /orP [/eqP -> // | Hxs] Hlt.
        have Umx: U (m,x) by apply: (Ht m t x Umh Hlt).
        have meqx: m = x by apply: (Hmax x Hxs Umx).
        move: Umh;rewrite meqx => Uxh.
        rewrite /antisymmetric in Ha.
        by move: (Ha t x Hlt Uxh).
      ++ (* ~ (U (m,h)) *)      
        exists m; split;first by rewrite in_cons;rewrite Hm orbT. 
        move => x; rewrite in_cons => /orP [/eqP -> ? //| H1 H2].
        by move: (Hmax x H1 H2).
    + (exists t);split;first by rewrite mem_seq1.
      by move => x; rewrite mem_seq1 => /eqP ->.
  Qed.
  
  Lemma seq_has_maximal U: 
    porder U -> forall s, ~ (s = [::]) -> (exists m, m \in s /\ seq_maximal m s U).
  Proof.
    move => ?;elim => [// | a s Hr _ ].
    apply: seq_has_maximal_step;first by [].
    by move: (EM (s = [::])) => [-> | /Hr ?];[right | left].
  Qed.    
  
  Lemma has_maximal U: porder U -> (exists x, x\in T) -> (exists m, maximal m U).
  Proof.
    move => Hp [x -];rewrite -mem_enum => Hx.
    have H2: ~ (enum T = [::]) by move: Hx => /[swap] ->.
    move: Hp => /seq_has_maximal/(_ (enum T) H2) [m [Hm HM]]. 
    exists m;move: HM => /[swap] x' /(_ x') HM H5.
    by apply: HM;[rewrite  mem_enum |].
  Qed.
  
  End fin_maximal.
End fin_Maximal.
Export fin_Maximal(has_maximal,maximal).

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

Module Maximal_in_preKernels.
Section Maximal_in_preKernels.
  (** * Existence of a Maximal set in preKernels when T is a finType *)
  (* we use a detour on {set T} *)
  Context (T : finType).
  Implicit Types (O R M U: relation T) (S: {set T}).

  (** * propagate definition on (set T) to definitions on {set T} *)
  Definition RelIndep_fin U S: bool := (asbool (RelIndep U [:set: S])).
  
  Section RelIndep_fin.
  
    Lemma RelIndep_iff U S: (RelIndep U [:set: S]) <-> (RelIndep_fin U S).
    Proof. split => [Hri | /asboolP Hri]. by apply/asboolP. by []. Qed.
    
    Lemma RelIndepP U S: reflect (RelIndep U [:set: S]) (RelIndep_fin U S).
    Proof. by apply: (iffP idP);move/RelIndep_iff. Qed.
    
    Lemma Unused_RelIndep_fin_subset U (S S': {set T}) :
      S' \subset S -> RelIndep_fin U S -> RelIndep_fin U S'.
    Proof.
      move=> /fintype.subsetP SS' /RelIndepP H; apply/RelIndepP. 
      by apply: (RelIndep_Ir SS' H).
    Qed.
    
    Lemma Unused_RelIndep_fin0 U: RelIndep_fin U finset.set0.
    Proof. by apply/RelIndepP;rewrite set_of_set0;apply/RelIndep_set0. Qed.
    
    Lemma RelIndep_fin1 U a : RelIndep_fin U [set a].
    Proof. apply/RelIndepP;rewrite set_of_sfin;apply/RelIndep_set1. Qed.

    Lemma Unused_RelIndep_fin_Iv U S: RelIndep_fin U S <-> RelIndep_fin U^-1 S.
    Proof. 
      split;first by move/RelIndepP => ?;apply/RelIndepP/RelIndep_Iv.
      by move/RelIndepP/RelIndep_Iv;rewrite inverseK => ?;apply/RelIndepP.
    Qed.
    
    Lemma Unused_RelIndep_fin_IE U S: RelIndep_fin U S = RelIndep_fin U^-1 S.
    Proof. 
      apply/RelIndepP/RelIndepP;first by apply: RelIndep_Iv.
      by move => ?;rewrite -(inverseK U);apply: RelIndep_Iv.
    Qed.
    
  End RelIndep_fin. 
  
  Definition pre_absorbant_fin R M S := (asbool (pre_absorbant R M [:set: S])).
  
  Definition prekernel_fin O R M: pred {set T} := 
    fun S => (RelIndep_fin O S) && ((pre_absorbant_fin R M S) && (([:set: S]) != set0)).

  Lemma prekernelE O R M S: 
    prekernel_fin O R M S <-> preKernel O R M [:set: S].
  Proof.
    split;first by move => /andP [/asboolP H1 /andP [/asboolP H2 H3]].
    move => [H1 [H2 H3]].
    apply/andP;split;first by apply/asboolP.
    by apply/andP;split;[apply/asboolP |].
  Qed.
  
  Lemma prekernel_fin_notempty O R M 
    (A1: nonempty [set: T]) (At: sporder O^-1) (Au: R `<=` O^-1):
    exists v, prekernel_fin O R M [set v].
  Proof.
    move: (At) (@fin_not_iic_inj T O^-1) => /[dup] Hsp [H1 /[dup] Ht /Tclos_iff H2] H3.
    have H4: ~(iic O^-1)
      by move => /(@sporder_iic_injective _ _ At ) ?.
    move: (@fin_rloop2 T O^-1 R M A1 At Au) => [v H6].
    exists v.
    apply/andP;split;first by apply: RelIndep_fin1.
    apply/andP;split;first by apply/asboolP;rewrite /pre_absorbant_fin set_of_sfin.
    rewrite set_of_sfin;apply/asboolP => H.
    have H7: [set v]%classic v by exact.
    by rewrite H in H7.
  Qed.

  (** * defining a new finType isomorphic to {S : {set T} | prekernel_fin S} *)
  Definition setIndep O R M := setP_type (prekernel_fin O R M). 
  
  (** * an order on setIndep O R M *)
  Definition prekernel_fin_order O R M: relation (setIndep O R M):= 
    [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic.
  
  (* now we have a porder on setIndep O R M *)
  Lemma prekernel_fin_order_is_porder O R M:
    sporder O -> porder (@prekernel_fin_order O R M).
  Proof.
    move => H_sp.
    split => [A /= | A B /= Ha Hb | A B C /= Ha Hb].
    + (* reflexive *)  apply: le_refl.
    + (* antisymmetric *) 
      move: (valP A) => /andP[/asboolP Pa _].
      move: (valP B) => /andP[/asboolP Pb _].
      move: (le_antisym_if_sp H_sp Pa Pb Ha Hb) => /set_of_fin_inj/eqP H5.
      by apply/eqP;rewrite -val_eqE.
    + (* transitive *)
      move: H_sp => [_ H1];move: (le_trans_if_tr H1) => H2. 
      by move: H2 => /(_ [:set:\val A] [:set:\val B] [:set:\val C] Ha Hb) H2.
  Qed.

  Lemma exists_setIndep O R M 
    (A1: nonempty [set: T]) (Asp: sporder O) (Au: R `<=` O^-1):
      (exists x : setIndep O R M, x \in {: (setIndep O R M)}).
  Proof.
    move: Asp => /sporder_inv Asp.
    move: (@prekernel_fin_notempty O R M A1 Asp Au) => [v Pv].
    by exists (SetP Pv).
  Qed.
  
  (* we use the general existence theorem for finite types *)
  Lemma Maximal_in_setIndep O R M 
    (A1: nonempty [set: T]) (Asp: sporder O) (Au: R `<=` O^-1):
    exists (m: (setIndep O R M)),
      @maximal (setIndep O R M) m (@prekernel_fin_order O R M).
  Proof.
    move: (Asp) => /sporder_inv Asp'. 
    move: (prekernel_fin_order_is_porder R M Asp) => po.
    pose proof (@exists_setIndep O R M A1 Asp Au) as Hne.
    by move: (@has_maximal (setIndep O R M) 
            [set AB | [:set: (val AB.1)] [<= O] [:set: (val AB.2)]]%classic
         po Hne).
  Qed.
  
  (* back to prekernel_fin objects *)
  Lemma Maximal_in_prekernel_fin O R M
    (A1: nonempty [set: T]) (Asp: sporder O) (Au: R `<=` O^-1):
    exists S, prekernel_fin O R M S /\ (forall S', prekernel_fin O R M S' ->
                                    [:set: S] [<= O] [:set: S'] -> S = S').
  Proof.
    move: (@Maximal_in_setIndep O R M A1 Asp Au)  => [S H3].
    exists S;move: (valP S) => Pr;split; first exact.
    move => U H4; move: H3 => /(_ (SetP H4)) H3.
    by move => /H3/eqP ?;apply/eqP. 
  Qed.
  
  (* back to preKernels *)
  Lemma Maximal O R M
    (A1: nonempty [set: T]) (Asp: sporder O) (Au: R `<=` O^-1):
    exists (S:set T), preKernel O R M S /\ (forall S':set T, preKernel O R M S' -> S [<= O] S' -> S = S').
  Proof.
    move: (@Maximal_in_prekernel_fin O R M A1 Asp Au)  => [S [HSpk Hm]].
    exists [:set: S]. 
    split =>[|U HUpk Hle];first by apply/prekernelE.
    move: Hm => /(_ [:fin: U]) Hm.
    rewrite -(@set_to_finK T U).
    apply/fin_of_set_inj.
    rewrite 2!fin_to_setK.
    apply: Hm;last by rewrite set_to_finK.
    by apply/prekernelE;rewrite set_to_finK.
  Qed.
  End Maximal_in_preKernels.
End Maximal_in_preKernels.

Export Maximal_in_preKernels(Maximal).

Section Extended_Champetier_Theorem.
    
  Context (T : finType) (O R B: relation T).
  Implicit Types (O R B: relation T). 
  
  Notation M := (B `|` R).

  Context (A2 : Assumption2 R) (A6 : Assumption6 B M O) 
    (A7 : Assumption7 R B M) (A8 : Assumption8 R B M).
  Context (A1: nonempty [set: T]) (Asp: sporder O) (Au: R `<=` O^-1).
  Context (Apk : forall X, RelIndep O X <->  RelIndep M X).
  
  Lemma maximal_mabsorbant S:
    (preKernel O R M S) /\ (forall U, preKernel O R M U -> S [<= O] U -> S = U)
    -> absorbant M S.
  Proof.
    contra; move => H1;rewrite /preKernel /= Apk => Hpk.
    have H3: ~ absorbant M S.
    {
      move: H1 => [y H1] H3.
      rewrite notin_setE in H3.
      rewrite /absorbant /mkset => /(_ y) H4. 
      by move: H1 => /H4;rewrite inE => H1.
    }
    move: (@extend T R B O S A2 A6 A7 A8 Hpk H3)
        => [S' [Hpre [/DeltaCP H7 Hne]]].
    exists S';first by rewrite (Apk S').
    by split;[| apply/negP => /eqP Heq].
  Qed.
  
  Lemma Kernel_ChampetierExt: 
    exists S, RelIndep M S /\ absorbant M S.
  Proof.
    (* There exist a maximal set *)
    move: (@Maximal T O R M A1 Asp Au) => [S Hm].
    move: Hm => /[dup] /maximal_mabsorbant Ma [[/Apk Hpk _] _]. 
    by (exists S).
  Qed.
  
End Extended_Champetier_Theorem.

Section Blidia_Engel_Ext_Theorem.
  (** * Similar to Champetier but  (Asp: sporder O) *)
  (** * is replaced by Acyclicity *)

  Context (T : finType) (O R B: relation T).
  Implicit Types (O R B: relation T).

  Notation M := (B `|` R).  

  Context (A2 : Assumption2 R) (A6 : Assumption6 B M O) 
    (A7 : Assumption7 R B M) (A8 : Assumption8 R B M).
  Context (A1: nonempty [set: T]) (Au: R `<=` O^-1).
  Context (Apk : forall (X:set T) , RelIndep O X <->  RelIndep M X).
  Context (Anc : ~ ( exists s, R.+ (s,s))).
  
End Blidia_Engel_Ext_Theorem.

Section simpleGraph. 
  (** * simpleGraph definition *)
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

Section Champetier_Theeorem.
  (** * The original Champetier Theorem *)
  Context (T : finType) (G D O: relation T).
  
  Context (Asg: simpleGraph G).
  Context (Ao: Orientation G O).
  Context (Ad: Direction G D).

  Definition R := D `&` O^-1.
  Definition B := D `&` O.

  Notation M := (B `|` R).

  Context 
    (A1: nonempty [set: T]) 
    (Asp: sporder O)
    (A6 : Assumption6 B M O) 
    (A7 : Assumption7 R B M)
    (A8 : Assumption8 R B M).
  
  Lemma RB: M = D.
  Proof.
    have H1:  R `<=` D. by rewrite /R;apply: subIsetl.
    have H2:  B `<=` D. by rewrite /R;apply: subIsetl.
    rewrite predeqE => -[x y].
    split => [[/H2 H0 | /H1 H0] // | H3].
    case H4: ((x,y) \in O).
    + move: H4 => /set_mem H4.
      ++ case H5: ((y,x) \in O).
         move: H5 => /set_mem H5.
         by right;split.
         by left;split.
    + case H5: ((y,x) \in O).
      move: H5 => /set_mem H5.
      by right;split.
      (** (x, y) \in O) = false /\ (y, x) \in O) = false *)
      (** is not possible *)
      have H6: D `|` D^-1 = G by [].
      have H7: O `|` O^-1 = G by move: (Ao) => [Do _].
      have H8:  D `|` D^-1 = O `|` O^-1. by rewrite H6 H7. 
      have [ //| H9]: (O `|` O^-1) (x,y) by rewrite -H8; left.
      by rewrite -inE H4.
      have: (y,x) \in O by rewrite inE.  
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

  Lemma Apk:  forall X , RelIndep O X <->  RelIndep M X.
  Proof.
    move => X. rewrite RB. 
    rewrite (@direction_relIndep T G D X Ad).
    by rewrite (@orientation_relIndep T G O X Ao).
  Qed.
  
  Lemma Rsym : asymmetric R.
  Proof.
    move => x y /Au H1 /Au H2.
    by move: H1 Ao => + [_ /(_ x y) Ha] => /Ha H3.
  Qed.
  
  Lemma haveA2 : ~ (iic (Asym R)).
    move: Rsym => /AsymEq ->;apply: Rnotiic.
  Qed.

  Lemma haveA6 : forall x y : T, B (x, y) /\ ~ M (y, x) -> O (x, y).
  Proof. by move => x y [[_ H1] _]. Qed.

  Lemma Kernel_Champetier: 
    exists S, RelIndep M S /\ absorbant M S.
  Proof.
    by pose proof (@Kernel_ChampetierExt T O R B (haveA2) (haveA6)
                     A7 A8 A1 Asp (Au) (Apk)).
  Qed.
  
End Champetier_Theeorem.


