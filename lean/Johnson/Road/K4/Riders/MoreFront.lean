-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/MoreFront.lean: WHAT THE NAMES THAT K4's ROW ASKS THROUGH THE TABLE OF
JOINTS' DOOR GIVE IN FRONT OF K4's SUB-PROTOCOL, AT A MEANING WITH `K4Means`: three premises of K4's
laws come out of the promise. Statements and proofs: the table's test pubFit ("what a row asks is
open in front of it"), the promise's clause on the open public items, the equation.

  `more_front`: a name that the door's filling lets K4's row ask holds of every unmarked state
    inside the promise in front.
  **`left_of_means`**: `lookLeftB` there ("K4.lookLeft": the premise left of `asks_of_means`) ·
    **`bare_of_means`**: `rowsBareB` there ("K4.rowsBare") · **`hroom_of_means`**: room for at least
    one entry of the index masks' ledger there ("pile.room", with one comparison of the public
    parameters' numbers: the premise hroom of `hRow_of_means`).

Limits. THAT THE ROW ASKS THE NAME (hask) IS A TEST ON THE DOOR's FILLING: a premise. pubFit is a
premise. Nothing says here who makes the names. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4Means
import Johnson.Road.K4.K4PromiseFront
import Johnson.Road.K4.Total.RoomFor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Total (roomFor)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning MoreName moreItem pubFit pubRowM pubStartM
  PubRow.plus)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.FillBare (rowsBareB lookLeftB bareName leftName)
open Johnson.Desc.First.Walk.Tied (roomIsB leftIsB rowsBefore)
open VerifiableInference.Desc.Sound (Frame onQ MsgT)

/-- The name "pile.room" at segment m, written out (its authors' part for the names that left the
door defines the same pair under the same name; this file imports no such part). -/
abbrev roomName (m : ℕ) : VerifiableInference.Desc.First.MoreName := (some m, "pile.room")

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- A name that K4's row asks holds in front of K4's sub-protocol. -/
theorem more_front (H : AtK4 links ps k m pl) (hf : pubFit Mg.more links ps = true)
    {nm : MoreName} (hask : nm ∈ (Mg.more.rows links pl).asks) {a : S × Fr.E.Str}
    (ha : onQ D.N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none) :
    Mg.pub (moreItem nm) (Z, a.1) = true := by
  have h1 : moreItem nm ∈ (pubRowM Mg.more links pl).asks := by
    unfold pubRowM PubRow.plus
    exact List.mem_append_right _ (List.mem_map_of_mem hask)
  exact List.all_eq_true.mp (bools_of_onQ D.N Mg Z ha hu).2.1 _
    (List.mem_append_left _
      (asks_open (pubRowM Mg.more links) ps (pubStartM Mg.more) k pl hf H.here _ h1))

theorem isLay_of (H : AtK4 links ps k m pl) (hlinks : D.links = links) :
    isLay D.links m = true := by
  rw [hlinks]
  unfold isLay
  rw [H.sub]
  rfl

/-- **"K4.lookLeft" in front of K4's sub-protocol.** -/
theorem left_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl) (hlinks : D.links = links)
    (hf : pubFit Mg.more links ps = true) (hask : leftName m ∈ (Mg.more.rows links pl).asks) :
    ∀ a : S × Fr.E.Str, onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      lookLeftB a.1 = true := by
  intro a ha hu
  have h := more_front (D := D) H hf hask ha hu
  change Mg.pub (.more (some m) "K4.lookLeft") _ = true at h
  rw [E.lookLeft m _ (isLay_of H hlinks)] at h
  exact h

/-- **"K4.rowsBare" in front of K4's sub-protocol.** -/
theorem bare_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl) (hlinks : D.links = links)
    (hf : pubFit Mg.more links ps = true) (hask : bareName m ∈ (Mg.more.rows links pl).asks) :
    ∀ a : S × Fr.E.Str, onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      rowsBareB a.1 = true := by
  intro a ha hu
  have h := more_front (D := D) H hf hask ha hu
  change Mg.pub (.more (some m) "K4.rowsBare") _ = true at h
  rw [E.rowsBare m _ (isLay_of H hlinks)] at h
  exact h

/-- Just n entries left gives room for n. -/
theorem roomFor_of_leftIs {n : ℕ} {s : S} (h : leftIsB n s = true) : roomFor n s = true := by
  unfold leftIsB at h
  unfold roomFor
  cases hl : Johnson.Desc.First.Walk.Law.ledgerAt s with
  | none => simp [hl] at h
  | some l =>
    simp only [hl, Option.any_some, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨h.1, by simp [h.2]⟩

/-- **"pile.room" in front of K4's sub-protocol gives room for an entry.** -/
theorem hroom_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl)
    (hf : pubFit Mg.more links ps = true) (hask : roomName m ∈ (Mg.more.rows links pl).asks)
    (h1 : 1 ≤ D.free0 - rowsBefore D.fvs m) :
    ∀ a : S × Fr.E.Str, onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      ∃ r, 1 ≤ r ∧ roomFor r a.1 = true := by
  intro a ha hu
  have h := more_front (D := D) H hf hask ha hu
  change Mg.pub (.more (some m) "pile.room") _ = true at h
  rw [E.room] at h
  exact ⟨_, h1, roomFor_of_leftIs h⟩

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.more_front
#print axioms OnBytes.Road.K4.Riders.left_of_means
#print axioms OnBytes.Road.K4.Riders.bare_of_means
#print axioms OnBytes.Road.K4.Riders.hroom_of_means
