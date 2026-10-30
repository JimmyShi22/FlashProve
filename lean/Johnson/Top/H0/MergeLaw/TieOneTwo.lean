-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/TieOneTwo.lean: the merge's first tie to the table of joints, and the
merge's own share of the second. Theorems with their proofs.

Why. `merge_seatLawsR` (TieLaws.lean) takes five ties between the merge's own words and the table's
as premises. Two of them speak of the promise alone, not of a witness. Here the first is shown at
every filling that says two public items in the table's own tests, and of the second all is paid
that hangs on the merge's text.

Main names:
  `frontR_of_tests`: the table's own tests `ledgerB` and `freeAboveB` at the plan's number of slots
    (Johnson/Desc/First/FillKeeper.lean) give `frontR` (OffRecord.lean).
  `merge_t1`: t1: where "ledger m" and "freeAbove m" are open at border k and the filling's tests
    for them are these: the promise in front, at an unmarked record, gives `frontR`.
  `yes_keeps`: what the merge's yes leaves of what the table's own tests read: the statement, the
    book, the mark, where the chain stands, the open segment's context; and no count of rows waits
    behind it.
  `merge_t2`: t2, by the rule for a quiet row (`onQ_step_held`,
    Johnson/Desc/Sound/PromiseRidesQ.lean). PAID: a mark stays; the book-keeping behind; the open
    rows' lists and the groups' members ride; the book rides. LEFT AS PREMISES: "decodes", "in
    order", the public items behind, what they say beside their Bools, "held", "shown" and "no
    collision" ride: all on the filling's letters; that the row is quiet; and four facts on the two
    places: they stand alike, in one segment, and the plan counts as many trees and messages in
    front of both.

Limits. `merge_t2` does not spend `BehindR`: what the merge MAKES behind (the public items tied to
"merged" and "wo") stands inside the premise on the public items. That the two items are open at the
merge's border is a premise: at a composed filling it is an evaluation. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.OffRecord
import Johnson.Desc.Sound.PromiseRidesQ
import Johnson.Desc.First.FillKeeper

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound (Frame strsOf onQ onQ_step_held)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- The table's own two tests on the ledger give the merge's condition in front. -/
theorem frontR_of_tests (Pm : HeadMergeP) {s : S} (h1 : ledgerB s = true)
    (h2 : freeAboveB Pm.nMsg s = true) : frontR Pm s = true := by
  unfold frontR
  unfold ledgerB S.fork? at h1
  unfold freeAboveB S.fork? at h2
  cases hh : s.here with
  | head a =>
    rw [hh] at h1 h2
    have ho : a.opened = true := by
      by_cases ho : a.opened = true
      · exact ho
      · simp [ho] at h1
    simp only [ho, if_true, Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1 h2
    obtain ⟨⟨l1, l2⟩, l3⟩ := h1
    simp [l1, l2, l3, h2.2]
  | _ => rfl

section
variable {Pp W : Type} {Fr : Frame} (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
  (ps : List Place) (k : ℕ)

/-- **THE MERGE's FIRST TIE, AT ANY FILLING THAT SAYS THE TWO ITEMS SO**: where "ledger m" and
"freeAbove m" are open at border k, and the filling's tests for them are the table's own at the
plan's number of slots: the promise in front, at an unmarked record, gives the merge's condition. -/
theorem merge_t1 (Pm : HeadMergeP) (m : ℕ)
    (hQ1 : Pub.ledger m ∈ (pubSets Mg.more links ps)[k]?.getD [])
    (hQ2 : Pub.freeAbove m ∈ (pubSets Mg.more links ps)[k]?.getD [])
    (hp1 : ∀ a, Mg.pub (.ledger m) a = ledgerB a.2)
    (hp2 : ∀ a, Mg.pub (.freeAbove m) a = freeAboveB Pm.nMsg a.2) (z : Pp) (a : S × Fr.E.Str)
    (ha : onQ Nn Mg links ps (fun s => (z, s)) k a) (hm : ¬ a.1.failed ≠ none) :
    frontR Pm a.1 = true := by
  unfold onQ onAt at ha
  rcases ha.2 with h | ⟨hB, _⟩
  · exact absurd h hm
  · simp only [Bool.and_eq_true] at hB
    have hP := hB.1.2
    unfold pubHeld at hP
    have hall := List.all_eq_true.1 hP
    have e1 := hall _ (List.mem_append_left _ hQ1)
    have e2 := hall _ (List.mem_append_left _ hQ2)
    rw [hp1] at e1
    rw [hp2] at e2
    exact frontR_of_tests Pm e1 e2

/-- What the merge's yes leaves of what the table's own tests read. -/
theorem yes_keeps (Pm : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (hd : headMergeDecide Pm s rs = .ok s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.failed = s.failed ∧ standOf s' = standOf s ∧
      s'.noneWaits = true ∧ s'.link? = s.link? := by
  obtain ⟨a, a', e1, e2, e3, e4, _⟩ := isLocal Pm s rs s' hd
  refine ⟨by rw [e3], by rw [e3], by rw [e3], ?_, by rw [e3]; rfl, ?_⟩
  · have ho : a'.opened = a.opened := by rw [e4]
    unfold standOf S.inLink S.fork?
    rw [e1, e2]
    simp only [ho]
    by_cases hx : a.opened = true
    · simp [hx]
    · simp [hx]
  · unfold S.link?
    rw [e1, e2, e4]

/-- **THE MERGE's SHARE OF ITS SECOND TIE**: by the rule for a quiet row (`onQ_step_held`): PAID
HERE, from the merge's own yes: a mark stays; the book-keeping behind; the open rows' lists and the
groups' members ride; the book rides. LEFT, all on the filling's letters or the plan's numbers:
"decodes", "in order", the public items behind, what they say beside their Bools, "held", "shown"
and "no collision"; and four facts on the two places. -/
theorem merge_t2 (Pm : HeadMergeP) (p p' : Place) (hp : ps[k]? = some p)
    (hp' : ps[k + 1]? = some p') (hq : quietRow (rowOf links p) = true)
    (hst : standAt links p' = standAt links p) (hlk : p'.link = p.link)
    (htr : Nn.treesAt (some p') = Nn.treesAt (some p))
    (hms : Nn.msgsAt (some p') = Nn.msgsAt (some p)) (z : Pp) (a b : S × Fr.E.Str)
    (ha : onQ Nn Mg links ps (fun s => (z, s)) k a)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1)
    (hDec : Mg.decodes (z, a.1) (strsOf Fr a.2) → Mg.decodes (z, b.1) (strsOf Fr b.2))
    (hIn : Mg.inOrder (z, a.1) = true → Mg.inOrder (z, b.1) = true)
    (hPub : pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []) (z, a.1) = true →
      pubHeld Mg (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p))
        (pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links p))
        (z, b.1) = true)
    (hPP : (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q (z, a.1)) →
      ∀ q ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links p),
        Mg.pubP q (z, b.1))
    (hHeld : ∀ x ∈ sampledIn Nn ((openSets links ps (start links))[k]?.getD []),
      Mg.held x.1 x.2 (z, a.1) = true → Mg.held x.1 x.2 (z, b.1) = true)
    (hSN : ∀ x ∈ sampledIn Nn ((openSets links ps (start links))[k]?.getD []),
      Mg.shown x.1 x.2 (strsOf Fr a.2) ∧ Mg.noColl x.1 x.2 (z, a.1) (strsOf Fr a.2) →
      Mg.shown x.1 x.2 (strsOf Fr b.2) ∧ Mg.noColl x.1 x.2 (z, b.1) (strsOf Fr b.2)) :
    onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b := by
  obtain ⟨rs, hd⟩ := hy
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := yes_keeps Pm hd
  refine onQ_step_held Nn Mg links ps (fun s => (z, s)) k p hp hq a b ha
    (fun h => by show b.1.failed ≠ none; rw [k3]; exact h) hDec ?_ ?_ ?_ (fun _ _ => hIn)
    (fun _ _ => hPub) ?_ (fun _ _ => hPP) (fun _ _ => hHeld) (fun _ _ => hSN)
  · intro hm _
    have hs : VerifiableInference.Desc.First.shapeAt links ps[k]? a.1 = true := by
      unfold onQ onAt at ha
      rcases ha.2 with h | ⟨hB, _⟩
      · exact absurd hm h
      · simp only [Bool.and_eq_true] at hB
        exact hB.1.1.1.1.1
    rw [hp] at hs
    rw [hp']
    unfold VerifiableInference.Desc.First.shapeAt at hs ⊢
    simp only [Bool.and_eq_true] at hs ⊢
    refine ⟨⟨by rw [k4, hst]; exact hs.1.1, by rw [k5]; rfl⟩, by rw [k6, hlk]; exact hs.2⟩
  · intro _ _ h
    unfold rowsHeld at h ⊢
    rw [k1]
    exact h
  · intro _ _ h
    unfold membersHeld at h ⊢
    rw [k1, k2]
    exact h
  · intro _ _ h
    rw [hp] at h
    rw [hp']
    unfold bookAt at h ⊢
    rw [k1, k2, htr, hms]
    exact h

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_t1
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_t2
