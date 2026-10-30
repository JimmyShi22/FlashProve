-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LabelsAtRecordOwn.lean: the game's conclusion at the numbering by labels gives
the conclusion at the numbering by the book's places: THE SECOND ARM AT THE RECORD ITSELF, and the
two faces behind our game's relations `QW` | `QWO`. Statements; each proof is a call.

After LabelsToPlaces.lean (`qn_places_of_labels`: both arms, under
«the book of the plain data that the record fixes is in order») and LabelsAtRecord.lean
(`qn_places_at_record`: the first arm, at the record's own book). Here:
  `qn_places_at_recordOwn`: the first fold sends its own mask (t.mask = none) · `BookStep` at the
    record (the book is in order and the record counts as many roots as the book has trees) · a yes
    of the test's decision (for its front) · the conclusion at the labels ⇒ the conclusion at the
    places. By `own_facts` (FirstBookOwn.lean): receiving the mask keeps the book in
    order.
  `QW.places` | `QWO.places`: behind our relations (GameOut.lean | GameOutOwn.lean): at the record
    behind the door in: QN π (NTuple F π ‹z ↦ lo + z | noAt t₁ t₂ ch› …) (t, a.2): what the seam's
    core (core_at, tupleNine_of | tupleTen_of, Johnson/Desc/Sound/SeamFacts.lean)
    takes as its premise on the game. At `QWO` the yes is the relation's own.
Why. Our game promises nothing and concludes at the labels; the word's seam stands at the places.
The two meet where the tree at the place z bears the label firstTree + z. SO THE INVARIANT IS SPENT
BY THE SEAM's PAYER, INSIDE THE TABLE's PROMISE, NOT IN THE GAME.
What it is not. That the book is in order at any record is a premise (a test with code on the
chain's own record; who keeps it: Johnson/Desc/Sound/BookInOrder.lean). A chain whose test opens
trees taken over from another chain has it not. No clause of the rule's premise is paid. No
soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LabelsAtRecord
import Johnson.Desc.K12.Coin.GameBook
import Johnson.Desc.K12.Coin.GameOutOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pin (NTuple)

/-- **The second arm, at the record behind the door in.** -/
theorem qn_places_at_recordOwn (F : Frame) (π : P12) (lo : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (x : T12 × F.E.Str) (hm : x.1.mask = none)
    (hB : BookStep π.nums.firstTree x.1.book x.1.roots) (tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (hy : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide x.1 rs gs = .ok tE)
    (h : QN π (NTuple F π (nuOf π (nlAt π lo) x.1) rad rd) x) :
    QN π (NTuple F π (fun z => lo + z) rad rd) x :=
  qn_places_of_labels F π lo rad rd x
    (fun a rest G0 Ly D hf =>
      (own_facts π x.1 hm hB (Seat.block_front_holds π x.1 tE rs gs hy).2.1 a rest G0 Ly D hf).1) h

/-- **Behind `QW`** (the first arm): the seam's core's premise on the game. -/
theorem QW.places {P S : Type} {F : Frame} {π : P12} {lo : ℕ} {r : Fmt.M1.Stage → ℕ} {rd : ℕ → ℕ}
    {enter : S → Except String T12} {leave : S → T12 → Except String S}
    {a b : (P × S) × F.E.Str} (h : QW F π (nlAt π lo) r rd enter leave a b)
    (hB : ∀ t, enter a.1.2 = .ok t →
      t.mask.isSome = true ∧ BookOrd π.nums.firstTree t.book) :
    ∃ t, enter a.1.2 = .ok t ∧
      QN π (NTuple F π (fun z => lo + z) (fun s => r s.st) rd) (t, a.2) := by
  obtain ⟨t, _, h1, _, hq, _⟩ := h
  exact ⟨t, h1, qn_places_at_record F π lo _ rd (t, a.2) (hB t h1).1 (hB t h1).2 hq⟩

/-- **Behind `QWO`** (the second arm): the yes is the relation's own. -/
theorem QWO.places {P S : Type} {F : Frame} {π : P12} {t₁ t₂ ch : ℕ} {r : Fmt.M1.Stage → ℕ}
    {rd : ℕ → ℕ} {enter : S → Except String T12} {leave : S → T12 → Except String S}
    {a b : (P × S) × F.E.Str} (h : QWO F π t₁ t₂ ch r rd enter leave a b)
    (hB : ∀ t, enter a.1.2 = .ok t →
      t.mask = none ∧ BookStep π.nums.firstTree t.book t.roots) :
    ∃ t, enter a.1.2 = .ok t ∧
      QN π (NTuple F π (noAt t₁ t₂ ch) (fun s => r s.st) rd) (t, a.2) := by
  obtain ⟨t, tE, h1, _, hq, rs, gs, hy⟩ := h
  exact ⟨t, h1, qn_places_at_recordOwn F π (numAt t₁ t₂ ch (.own 0)) _ rd (t, a.2) (hB t h1).1
    (hB t h1).2 tE rs gs hy hq.2⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.qn_places_at_recordOwn
#print axioms VerifiableInference.Desc.K12.Coin.QW.places
#print axioms VerifiableInference.Desc.K12.Coin.QWO.places
