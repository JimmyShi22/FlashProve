-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SeenTerms.lean: CONDITIONAL. Statements with their proofs.

Not shown here. No property is claimed. That the premises can be met: no example is known. EQUATIONS
BETWEEN MACHINE WORDS ALONE: what the batched sumcheck's job reads off the rounds shown in front of
it is what one round of the played row shows, and what the ledger behind the step shows under that
round's slots: nothing on the values under these slots (Law/SlotsTrue.lean, `OpenedLeft.terms`, has
what the slots are worth).

What is here: one job of the honest row of the layers' own rounds (the sub-protocol K4), the batched
sumcheck's, reads words that the row itself has sent: the second token sumcheck's end values, by
their round's number in the first chain (`k4SentAt`, `k4TermsEnds`, `k4SumSeen`,
Honest/K4/Part.lean). At a stand (`K4Stand`, Law/SlotsTrue.lean) these are tied here to the tape of
the played rounds and to the ledger that the step leaves. WHO NEEDS IT: whoever shows the batched
sumcheck's own claim (`OwnBack.stack`, Johnson/Road/K4/W/Join.lean): the verifier's panels read the
array that its run of shown values returns (OnBytes/Desc/First/K4/Hear.lean, `hearStack`), the
honest job's panels read `k4SentAt` …: `stand_terms_run` says that the two arrays are one.

THE PREMISES: `K4Stand`; `Thr`, the thread's own proposition on a stand (Honest/Thread/Thr.lean),
for one number: as many rounds have been shown in front of the member as the public data count.

  `elems_leading_list`, `sayE_all`, `sum_ends_move`   three small steps: the next at lists; what a
      move that says scalars sends; which move of a masked sumcheck says its end values
  `elems_leading`   on a message of elements of the extension field alone, "every such item" and
      "the leading such items" are one list
  `k4_said_vals`   a round of the played row whose move says scalars is there, and all its items are
      elements of the extension field
  `stand_terms_seen`   **what the job reads is what round `rJ3` + lt + 2 of the played row shows**,
      as the verifier's tape takes it
  `stand_terms_shown`, `stand_terms_size`   **so it is what the ledger that the step leaves shows
      under the slots of the second token sumcheck's end values**, member by member; and it has as
      many members as there are such slots
  `stand_terms_run`   **so it is the array that the verifier's run of shown values under these slots
      returns** (`shownRun`, OnBytes/Desc/First/K4/Engine.lean, by `shownRun_spec`,
      OnBytes/Desc/First/K4/StackTape.lean), on any ledger than which the one that the step leaves
      is later

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Desc.ProofFile.Honest.K4.Law.Starts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.K.Kc (leading)
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open ProofFile.Honest.SumLaw (mvOf)

/-- The list form. -/
theorem elems_leading_list : ∀ l : List Fmt.ItemValue,
    (l.all fun x => match x with | .e _ => true | _ => false) = true →
    (l.filterMap fun
      | .e x => some (OnBytes.E.ofTriple x)
      | _ => none) = leading l
  | [], _ => rfl
  | .e x :: l, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    show OnBytes.E.ofTriple x :: _ = OnBytes.E.ofTriple x :: leading l
    rw [elems_leading_list l h.2]
  | .f _ :: _, h => by simp at h
  | .word _ :: _, h => by simp at h
  | .root _ :: _, h => by simp at h
  | .answer _ :: _, h => by simp at h

/-- What `sayE` says holds elements of the extension field alone. -/
theorem sayE_all : ∀ l : List OnBytes.E,
    (((sayE l).vals.map Said.got).all fun x => match x with | .e _ => true | _ => false) = true
  | [] => rfl
  | _ :: l => sayE_all l

/-- The move of a masked sumcheck's part that says its end values. -/
theorem sum_ends_move (name endName : String) (J : SumJob K4In Unit)
    (en : VerifiableInference.Desc.Part.MaskedSum.Ends) (hen : J.shape.ends = some en) :
    (sumPart (V := Unit) name endName J).moves[J.shape.vs.length + 2]? =
      some (mvOf (SumLaw.askG name endName J (SumLaw.saidEnds J en) (J.shape.vs.length + 2))) := by
  rw [SumLaw.sumPart_moves]
  refine List.getElem?_map.trans ?_
  rw [sumGs_ends name endName J en hen]
  rfl

/-- On a message whose items are all elements of the extension field, the elements that are kept
item by item are the leading ones. -/
theorem elems_leading : ∀ l : List Fmt.ItemValue,
    (l.all fun x => match x with | .e _ => true | _ => false) = true →
    (l.toArray.filterMap fun
      | .e x => some (OnBytes.E.ofTriple x)
      | _ => none) = (leading l).toArray := by
  intro l h
  rw [List.filterMap_toArray, elems_leading_list l h]

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
  {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}

/-- **The items that round `movesTo` + r of the played row shows, where move number r of part number
i says scalars, are all elements of the extension field.** -/
theorem k4_said_vals (Z : K4Played T b cells weights tokens look Q p blk k m E ds y cols c)
    (i : Nat) (P₀ : Part Unit K4In Unit) (hp : (k4RowIn Q)[i]? = some P₀) (r : Nat)
    (g : P₀.Coins → Seen → State K4In Unit → List OnBytes.E)
    (hm : P₀.moves[r]? = some (mvOf g)) :
    ∃ rv, (roundsOf y.1)[movesTo (k4RowIn Q) i + r]? = some rv ∧
      (rv.vals.all fun x => match x with | .e _ => true | _ => false) = true := by
  obtain ⟨⟨l, hl, hy⟩, _⟩ := Z.moved
  have hc' : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c := by
    rw [Z.seat.place]
    exact Z.lent
  have hpart : (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts[i]? =
      some (k4SeatOf Q cells weights tokens (look Q) P₀) := by
    show ((k4RowIn Q).map _)[i]? = _
    rw [List.getElem?_map, hp]
    rfl
  obtain ⟨cp, hcp⟩ := rowAt_some _ c _ _ hpart
  have hmv : (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q) P₀).moves[r]? =
      some (Move.lift (k4Wit Q cells weights tokens (look Q)) (fun _ => ()) (fun x _ => x)
        (mvOf g)) := by
    show (P₀.moves.map _)[r]? = _
    rw [List.getElem?_map, hm]
    rfl
  have hmt : movesTo (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts i =
      movesTo (k4RowIn Q) i := movesTo_lift _ _ _ _ _ i
  obtain ⟨st, z, _, _, e3, e4, _⟩ := row_said hl Z.seat.half hc' hy i _ cp hcp r _ hmv
    (row_lt hl Z.seat.half i _ r hpart (List.getElem?_eq_some_iff.1 hmv).1)
  rw [hmt] at e3 e4
  obtain ⟨rv, h1, h2⟩ := Option.map_eq_some_iff.1 e4
  refine ⟨rv, h1, ?_⟩
  rw [h2, ← Except.ok.inj e3]
  exact sayE_all _

/-- **WHAT THE BATCHED SUMCHECK's JOB READS OFF THE ROUNDS SHOWN IN FRONT OF IT IS WHAT THE ROUND OF
THE SECOND TOKEN SUMCHECK's END VALUES SHOWS**, as the verifier's tape takes it. CONDITIONAL on the
stand and on `Thr` there. -/
theorem stand_terms_seen
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) :
    k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q) =
      (sentAt y (rJ3 Q.P Q.g + (Q.P.y.h.lt + 2))).toArray := by
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  have hv : (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)).vs.length = Q.P.y.h.lt :=
    List.length_replicate
  have hs := stand_seen Z.seat hT
  obtain ⟨rv, h1, h2⟩ := k4_said_vals Pl (k0 Q.g + 6) _ (k4RowIn_at Q 6) _ _
    (sum_ends_move _ _ _ ⟨1, nEndT Q.P.y⟩ rfl)
  rw [(k4_row_nums Q).m3] at h1
  have h1' : (roundsOf y.1)[rJ3 Q.P Q.g + (Q.P.y.h.lt + 2)]? = some rv := by
    rw [← hv]
    exact h1
  have e1 : (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g)))[k4TermsEnds Q]? = some rv := by
    rw [k4_termsEnds, List.getElem?_append_right (by rw [hs]; omega), hs,
      show Q.r0 + rJ3 Q.P Q.g + Q.P.y.h.lt + 2 - Q.r0 = rJ3 Q.P Q.g + (Q.P.y.h.lt + 2) by omega]
    unfold roundsOf
    rw [List.map_take, List.getElem?_take_of_lt (by unfold rJ4; omega)]
    exact h1'
  unfold k4SentAt sentAt
  rw [e1, h1']
  exact elems_leading rv.vals h2

/-- **So it is what the ledger that the step leaves shows under the slots of these end values.**
CONDITIONAL on the stand and on `Thr` there. -/
theorem stand_terms_shown
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) : ∀ tT, o.H.tT = some tT → ∀ e, e < nEndT Q.P.y →
    A.F.vp.getD (tT.sEnd + e) zeroE =
      (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)).getD e zeroE := by
  intro tT hTT e he
  obtain ⟨_, _, _, U, _, _, _⟩ := stand_ground Z
  have h := ((U.terms tT hTT).2 e he).shown
  rw [paired_sent] at h
  rw [h, stand_terms_seen Z hT]
  simp [sentAt]

/-- **It has as many members as that sumcheck has end values**: so it is, as an array, what the
ledger shows under these slots. CONDITIONAL on the stand and on `Thr` there. -/
theorem stand_terms_size
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) :
    (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)).size =
      nEndT Q.P.y := by
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  have hv : (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)).vs.length = Q.P.y.h.lt :=
    List.length_replicate
  rw [stand_terms_seen Z hT, List.size_toArray]
  obtain ⟨cp, _, _, hs⟩ := k4_said Pl (k0 Q.g + 6) _ (k4RowIn_at Q 6) _ _
    (sum_ends_move _ _ _ ⟨1, nEndT Q.P.y⟩ rfl)
  rw [(k4_row_nums Q).m3] at hs
  have hl := congrArg List.length hs
  rw [List.length_map] at hl
  rw [← hv]
  refine hl.trans ?_
  unfold SumLaw.askG
  exact SumLaw.saidEnds_length _ ⟨1, nEndT Q.P.y⟩ _ _ _ _ _ _

/-- **So it is the array that a run of shown values under these slots returns**, on any ledger than
which the one that the step leaves is later: such is the ledger from which the verifier hears the
batched sumcheck. "Later" is the library's `Fo.Later`. CONDITIONAL on the stand and on `Thr` there.
-/
theorem stand_terms_run
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) : ∀ tT, o.H.tT = some tT → ∀ (Fz : OnBytes.Model.Fork)
    (a : Array OnBytes.E), Fo.Later Fz A.F →
    ((Array.range (nEndT Q.P.y)).mapM fun i => Fz.shown (tT.sEnd + i)) = some a →
    a = k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q) := by
  intro tT hTT Fz a hLz hrun
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at hrun
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp hrun
  have hlen : l.length = nEndT Q.P.y := by
    rw [OnBytes.Maker.mapM_length _ _ _ hl, List.length_range]
  have hsz := stand_terms_size Z hT
  rw [← e]
  refine Array.ext (by rw [List.size_toArray, hlen, hsz]) fun i h1 h2 => ?_
  have hi : i < nEndT Q.P.y := by
    rw [List.size_toArray, hlen] at h1
    exact h1
  obtain ⟨b', hb, hb'⟩ := OnBytes.Desc.First.K4.mapM_range_get _ hl (i := i) hi
  obtain ⟨_, hfill, hval⟩ := OnBytes.Desc.First.P1.shown_some hb
  have k2 := (hLz.keep (tT.sEnd + i) hfill).2.1
  have k3 := stand_terms_shown Z hT tT hTT i hi
  have e1 : l.toArray[i] = b' := by
    rw [List.getElem_toArray]
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hi)] at hb'
    exact Option.some.inj hb'
  rw [e1, hval, ← k2, k3, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.elems_leading_list
#print axioms ProofFile.Honest.K4.sayE_all
#print axioms ProofFile.Honest.K4.sum_ends_move
#print axioms ProofFile.Honest.K4.elems_leading
#print axioms ProofFile.Honest.K4.k4_said_vals
#print axioms ProofFile.Honest.K4.stand_terms_seen
#print axioms ProofFile.Honest.K4.stand_terms_shown
#print axioms ProofFile.Honest.K4.stand_terms_size
#print axioms ProofFile.Honest.K4.stand_terms_run
