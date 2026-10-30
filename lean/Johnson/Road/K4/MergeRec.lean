-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MergeRec.lean: THE SEVENTH RECORD: where the merge of the weight claims returns
(`flatForkEnd`, OnBytes/K/Kc/QuietLink.lean), its sumcheck's record is the library's `RecAt`
(OnBytes/Tie/Pv/Lay/HearTieAll.lean) AT THE WORDS THAT THE CHAIN's DATA READ OFF THE TAPE (`pscT`,
OnBytes/Desc/First/P1/TailTape.lean). Statements and proofs.

The merge's files have the record as `Ended` at lists under "there are", tied to the tape by one
equation (`hear_ended`, Johnson/Top/H0/MergeLaw/Said.lean; `hear_of_flat`, MergeLaw/Flat.lean). Here
these lists are read off that equation.

  `pairs_qs`: of a tape that begins with the rounds `qs.map (MergeLaw.rd name 0)`: `heardPairs
    qs.length` is what these rounds sent, each with what it drew.
  `merge_recAt`: `RecAt (pscT 0 lay.lk (t.drop 1)) (lay.lk times `Weight.plain 3`) lay.lk 1 _ wo.p`;
    the element that the round in front drew is `tapeEps t`; the record's target is what the ledger
    in front shows of the start form at that element's powers; the one end value is the word that
    the values' round sent.
  `own_rec7`: so where `hear` returns in a group that is not the first: the seventh record, on the
    cut `Ks.tcW` of the tape (`own_calls7`, OwnRecs.lean).

NO NEW ARGUMENT: the merge's files' two theorems, and lists.

Limits. One direction: from a return. Those of the merge's files. Nothing on the row, on the
slot of the end value, or on soundness.
-/
import Johnson.Road.K4.OwnRecs
import Johnson.Top.H0.MergeLaw.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Psc (Weight)
open OnBytes.Model (Fork WsLay WsClaim WsForkOut wsForkStart)
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Desc.First.K4 (hear engFl)
open OnBytes.Tie.Pv.Lay (RecAt)
open OnBytes.Desc.First.P1 (pscT heardPairs msOf msOf_cons msOf_nil tapeEps sentOf roundAt
  drop_length_add)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)

theorem pairs_qs (name : String) : ∀ (qs : List (Nat × List E × E)) (more : Tape),
    heardPairs qs.length (qs.map (MergeLaw.rd name 0) ++ more) = qs.map fun q => (q.2.1, q.2.2)
  | [], more => by
    unfold heardPairs
    show (msOf [] more).map _ = []
    rw [msOf_nil]
    rfl
  | q :: qs, more => by
    have ih := pairs_qs name qs more
    unfold heardPairs at ih ⊢
    show (msOf (Weight.plain 3 :: List.replicate qs.length (Weight.plain 3))
      (MergeLaw.rd name 0 q :: (qs.map (MergeLaw.rd name 0) ++ more))).map _ = _
    rw [msOf_cons, List.map_cons, ih]
    rfl

/-- **The merge's record, at the words that the chain's data read.** -/
theorem merge_recAt {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    RecAt (pscT 0 lay.lk (t.drop 1)) (List.replicate lay.lk (Weight.plain 3)) lay.lk 1
        (pscT 0 lay.lk (t.drop 1)).v.length wo.p ∧
      F.publicPart (wsForkStart sv (OnBytes.Model.powers (tapeEps t) sv.size)) =
        some wo.p.target ∧
      (pscT 0 lay.lk (t.drop 1)).v.length = 1 ∧ u = (t.drop 1).drop (lay.lk + 3) := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, hq, et, hT, hE, _⟩ :=
    hear_ended (hear_of_flat h)
  rw [← hn] at hE ⊢
  have d1 : t.drop 1 =
      ⟨some OnBytes.Model.RoundName.pscEpsilon.name, 0, r1, [mu], [wo.p.eps]⟩ ::
        (qs.map (MergeLaw.rd OnBytes.Model.RoundName.pscRound.name 0) ++
          ⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
          ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: u) := by
    rw [et]
    rfl
  have len : (qs.map (MergeLaw.rd OnBytes.Model.RoundName.pscRound.name 0)).length = qs.length :=
    List.length_map _
  have dk : ∀ j, (t.drop 1).drop (qs.length + 1 + j) =
      ((⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
        ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: u : Tape)).drop j := by
    intro j
    have e := drop_length_add (qs.map (MergeLaw.rd OnBytes.Model.RoundName.pscRound.name 0))
      (⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
        ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: u : Tape) j
    rw [len] at e
    rw [d1, show qs.length + 1 + j = (qs.length + j) + 1 by omega, List.drop_succ_cons, e]
  have e1 : (pscT 0 qs.length (t.drop 1)).mu = mu := by
    show (sentOf (t.drop 1)).getD 0 zeroE = mu
    rw [d1]
    rfl
  have e2 : (pscT 0 qs.length (t.drop 1)).eps = wo.p.eps := by
    show tapeEps (t.drop 1) = _
    rw [d1]
    rfl
  have e3 : (pscT 0 qs.length (t.drop 1)).rs = qs.map fun q => (q.2.1, q.2.2) := by
    show heardPairs qs.length ((t.drop 1).drop 1) = _
    rw [d1, List.drop_succ_cons, List.drop_zero]
    exact pairs_qs _ qs _
  have e4 : (pscT 0 qs.length (t.drop 1)).sentY = [c] := by
    show (roundAt (Weight.atZero 1) ((t.drop 1).drop (qs.length + 1))).2.1 = _
    rw [show qs.length + 1 = qs.length + 1 + 0 from rfl, dk 0]
    rfl
  have e5 : (pscT 0 qs.length (t.drop 1)).beta = beta := by
    show (roundAt (Weight.atZero 1) ((t.drop 1).drop (qs.length + 1))).2.2 = _
    rw [show qs.length + 1 = qs.length + 1 + 0 from rfl, dk 0]
    rfl
  have e6 : (pscT 0 qs.length (t.drop 1)).v = [v] := by
    show sentOf ((t.drop 1).drop (qs.length + 2)) = _
    rw [show qs.length + 2 = qs.length + 1 + 1 from rfl, dk 1]
    rfl
  have ex : tapeEps t = x := by
    rw [et]
    rfl
  refine ⟨⟨⟨wsForkStart sv (OnBytes.Model.powers x sv.size), T, F.next, ?_⟩, ?_, ?_, rfl⟩, ?_, ?_,
    ?_⟩
  · rw [e1, e2, e3, e4, e5]
    exact hE
  · rw [e3, List.map_map]
    refine List.eq_replicate_iff.2 ⟨List.length_map _, fun b hb => ?_⟩
    obtain ⟨q, hqm, rfl⟩ := List.mem_map.1 hb
    exact hq q hqm
  · rw [e4]
    rfl
  · rw [ex, hE.target]
    exact hT
  · rw [e6]
    rfl
  · rw [show qs.length + 3 = qs.length + 1 + 2 from rfl, dk 2]
    rfl

/-- **The seventh record, where the hearing returns in a group that is not the first.** -/
theorem own_rec7 {P : Pub} {hp : HPlan2} {g : Nat} {fo : OnBytes.Model.Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hg : (g == 0) = false) :
    RecAt (pscT 0 P.wsLay.lk (((ksOf P hp).tcW (t0.drop 1)).drop 1))
      (List.replicate P.wsLay.lk (Weight.plain 3)) P.wsLay.lk 1
      (pscT 0 P.wsLay.lk (((ksOf P hp).tcW (t0.drop 1)).drop 1)).v.length o.wo.p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, u4, _, _, _, _, _, _, _, _, _, _, hu4, _, _,
    _, _, _, e9⟩ := own_calls7 h hg
  rw [hu4] at e9
  exact (merge_recAt e9).1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pairs_qs
#print axioms OnBytes.Road.K4.merge_recAt
#print axioms OnBytes.Road.K4.own_rec7
