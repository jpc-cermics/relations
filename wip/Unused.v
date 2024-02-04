  Lemma Epe_L1: forall (spt: seq (T*T)) (x y:T),
      size(spt) > 0 -> spt [Suc\in] (@Chrel T) -> Epe spt = (x, y) 
      -> exists st, size(st) > 1 /\ spt = Lift st /\ Pe st =(x,y).
  Proof.
    move => spt x y H1 H2 H3.
    have H4: spt \in (@I T) by apply inP.
    pose proof Lift_surj H4 as [st [H5 H6]].
    have H7:(UnLift (Lift st) ptv.1) = st by apply UnLift_left;rewrite inP in H5.
    by exists st; rewrite -Lift_sz2 H6; rewrite /Epe -H6 H7 in H3.
  Qed.
  
  Lemma Epe_L2: forall (st: seq T) (x y:T),
      size st > 1 -> Pe st =(x,y) -> exists q, st = x::(rcons q y).
  Proof.
    move => st x y H1 H2.
    pose proof seq_crc H1 as [q [x' [y' H3]]].
    move: H2;rewrite /Pe H3 //= => [[H2 //= H4]].
    have H5: forall q' x'', last x'' (rcons q' y') = y'
        by elim;[| move => z q' Hr x'';rewrite rcons_cons /=; rewrite Hr].
    by exists q;rewrite H2 -H4 H5.
  Qed.

  Lemma Epe_L2': forall (st: seq T) (x y:T),
      size st > 1 -> Pe st =(x,y) -> Epe1 (Lift st) = (x,y).
  Proof.
    move => st' x y H1 H2.
    pose proof Epe_L2 H1 H2 as [st H3].
    rewrite H3 /Epe1.
    pose proof Lift_head st ptv x y as H9.
    pose proof Lift_last st ptv x y as H10.
    by rewrite H9 H10 /=.
  Qed.
  
  Lemma Epe_L3: forall (spt: seq (T*T)) (x y:T),
      size(spt) > 0 -> spt [Suc\in] (@Chrel T) -> Epe spt = (x, y) 
      -> exists (st: seq T), spt = Lift (x::(rcons st y)).
  Proof.
    move => spt x y H1 H2 H3.
    pose proof Epe_L1 H1 H2 H3 as [st' [H4 [H5 H6]]].
    pose proof Epe_L2 H4 H6 as [st H7].
    by exists st; rewrite -H7 -H5.
  Qed.
  
  Lemma Epe_L4: forall (spt: seq (T*T)) (pt: T*T) (x y:T),
      size(spt) > 0 -> spt [Suc\in] (@Chrel T) -> Epe spt = (x, y) 
      -> Epe1 spt = (x,y).
  Proof.
    move => spt pt x y H1 H2 H3.
    pose proof Epe_L1 H1 H2 H3 as [st' [H5 [H6 H7]]].
    pose proof Epe_L2 H5 H7 as [st H8].
    rewrite H6 H8.
    rewrite /Epe1. 
    pose proof Lift_head st ptv x y as H9.
    pose proof Lift_last st ptv x y as H10.
    by rewrite H9 H10 /=.
  Qed.

  (** * XXXX unused but kept for intermediate nodes *)

  Definition decomp (st: seq T) := 
    (head t st, last t st, behead (behead (belast t st))).
  Definition comp (tr: T*T*(seq T)) := tr.1.1::(rcons tr.2 tr.1.2).

  Lemma Pe_eq: forall (st: seq T), Pe st = (decomp st).1.
  Proof. move => st //. Qed.

  Definition Edecomp (spt: seq (T*T)) := (decomp (UnLift spt t)).
  Definition Ecomp (tr: T*T*(seq T)) := Lift (comp tr).

  Lemma Epe_eq: forall (spt: seq (T*T)), Epe spt = (Edecomp spt).1.
  Proof. move => spt //. Qed.
  
  Definition D1 (x y :T) := [set st:seq T | (decomp st).1 = (x,y)].
  Definition I1 (x y :T) := [set spt:seq (T*T) | (Edecomp spt).1 = (x,y)].

  Lemma D1_eq: forall (x y:T), D1 x y = [set st:seq T | Pe st = (x,y)]. 
  Proof.
    by move => x y;rewrite /D1 /mkset predeqE => st;rewrite Pe_eq.
  Qed.

  Lemma I1_eq: forall (x y:T), I1 x y = [set spt:seq (T*T) | Epe spt = (x,y)].
  Proof.
    move => x y; rewrite /I1 /mkset predeqE => spt.
    by rewrite /Edecomp /Epe /Pe /decomp /=.
  Qed.
  
  Lemma Lxx: forall (st:seq T), size(st)> 1 -> comp (decomp st) = st.
  Proof. 
    move => p.
    pose proof seq_cases p as [H1 | [[x H1] | [r [x [y H1]]]]];rewrite H1 //.
    move => _.
    by rewrite /decomp /comp /= belast_rcons last_rcons /=.
  Qed.

  Lemma Lyy: forall (tr: T*T*(seq T)),  decomp (comp tr) = tr.
  Proof. 
    move => [[x p] y].
    by rewrite /comp /decomp /=  belast_rcons last_rcons /=.
  Qed.

