-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
Johnson/Desc/ProofFile/Honest/K3/Key/LookupLeavesTheThreeSentences.lean: (K-P2) THE EXCHANGE's CORE, WITHOUT A THREAD. The key
file's table of joints owes three items behind a lookup's own sub-protocol: `FormsObjects`, `WorthPlanes`, `WorthKeys`
(Johnson/Desc/Key/KeyK3Items.lean), said in machine elements, at a table of homes and at mask entries by home. The law of
the lookup's honest side concludes `Left` (Honest/K3/Law/LookLeftOf.lean), said in the field, in the world of a ledger, at
mask entries by slot. Here: FROM `Left` TO THE THREE SENTENCES. General in the face, the course and the readers. Theorems
with proofs.

  `formWorthReadIsItsValue`       a form without entries of virtual rows: its worth in machine elements (`affAt`), read, is
                                  its value in the ledger's world, where the mask entry at each named slot's home reads as
                                  the world's mask at that slot
  `closingReturnsBehindTheHearing`  from the fresh kind of ledger: `planesV` returns at the ledger behind the hearing, with
                                  three claims; so `closedAt` returns the same claims and ledger
  `lookupLeavesFormsObjects`, `lookupLeavesWorthPlanes`, `lookupLeavesWorthKeys`   **the three sentences**

Hypotheses that remain, by name. left: `Left`. masks: `MasksAre`. reads: the mask entry at slot j's home reads as the mask
at j, for every slot below the homes' size. The closing's return (paid by `closingReturnsBehindTheHearing`). scoped…: each
form names slots below the homes' size alone and no entry of a virtual row (Honest/K3/Parts/KeyLeft.lean's `ScopedG`).
planesAre: what the planes come to under a claim's pairs is `planeSum` of the bits, read. keysAre: part by part, alpha less
what the keys come to at the point is the sentence's sum, read; formsAre: the form beside a part's point is the course's.

Who pays. left, and with it what was heard and its points, AT ANY NUMBER OF PARTS OF KEYS (a key file's lookup has twelve):
Honest/K3/Parts/LookLeft.lean (`lookLeft_ofP`, `lookP`), Honest/K3/Parts/LookHeard.lean (`lookHeardP`); at the seated row:
Honest/K3/Key/SeatedWalkAtAnyNumberOfParts.lean. The library's own payers (Honest/K3/Law/LookLeftOf.lean, LookOne.lean,
Top.lean) are at one part. scoped…, formsAre, asMany: Honest/K3/Key/LookupTruthBehindTheHearing.lean. planesAre, keysAre:
Honest/K3/Key/LookupRecordReadsAsTheSentences.lean. `ReadAlike` is the text of the field `same` in the library's own filling
of the table's reader (Johnson/RunOne/KeyFillBaseAt.lean), whose reading of a word has the same body as `OnBytes.Slice.readE`.

Limits. Implications. NO MEMBER. No thread, no state, no sender. That the premises hold of the offline prover's run is not
shown here.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyLeft
import Johnson.Desc.ProofFile.Honest.K3.Law.LookLeftOf
import Johnson.Desc.Key.KeyK3Items
import Johnson.RunOne.Law.TieRead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K3.Key
open OnBytes (E zeroE oneE addE mulE subE Slot Tensor)
open OnBytes.Slice (GE readE readE_add readE_mul readE_zero)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV HeardG PlaneClaim hearV planesV planesG toHeardG)
open VerifiableInference.Desc.Key (affAt hidden Zero closedAt planeSum sumE FormsObjects WorthPlanes WorthKeys)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (ScopedG)

/-- Two machine elements are the same where they read alike. -/
abbrev ReadAlike (a b : E) : Prop := readE a = readE b

/-! ## 1 A form's worth, read -/

/-- **A form's worth in machine elements, read, is its value in the ledger's world.** -/
theorem formWorthReadIsItsValue (ledger : Fork) (home : Array Slot) (maskEntry : Slot → E) (mask : Nat → GE)
    (entry : Nat → Nat → Nat → GE) (form : Aff) (noEntries : form.ents.isEmpty = true)
    (reads : ∀ t ∈ form.slots.toList, readE (maskEntry (home.getD t.1 default)) = mask t.1) :
    readE (affAt ledger home maskEntry form) =
      form.value Reading.gl (ledger.worldOf Reading.gl mask entry) := by
  have he : form.ents.toList = [] := by
    rw [Array.isEmpty_iff.1 noEntries]
  have hs : (form.slots.toList.map fun t => readE t.2 * readE (hidden ledger home maskEntry t.1)).sum =
      (form.slots.toList.map
        (OnBytes.Model.slotValue Reading.gl (ledger.worldOf Reading.gl mask entry))).sum :=
    congrArg List.sum (List.map_congr_left fun t ht => by
      rw [Johnson.RunOne.Law.TieRead.read_hidden, reads t ht]
      rfl)
  unfold affAt Aff.value
  rw [← Array.foldl_toList, Johnson.RunOne.Law.TieRead.read_fold, he, List.map_nil, List.sum_nil, zero_add, hs]
  exact add_comm _ _

/-! ## 2 The closing returns -/

/-- **Behind the hearing the kind's own closing returns**, in both texts, with the same three claims and ledger. -/
theorem closingReturnsBehindTheHearing (face : LFace) {front behind : Fork} {rounds : List Fmt.RoundView} {heard : HeardV}
    (sized : Sized front) (room : front.next + face.slots ≤ front.ns)
    (free : ∀ j, front.next ≤ j → j < front.next + face.slots → ¬ Filled front j)
    (hearing : hearV face front rounds = some (heard, behind)) :
    ∃ claims closed, planesV face heard behind = some (claims, closed) ∧ claims.length = 3 ∧
      closedAt face (toHeardG heard) behind = some (claims, closed) := by
  have sizedBehind : Sized behind := (hearV_later hearing).sized sized
  obtain ⟨claims, closed, hv, h3⟩ := planesV_of_owed face sized room hearing sizedBehind (Later.refl _)
    (leaves_owed face sized free hearing)
  refine ⟨claims, closed, hv, h3, ?_⟩
  unfold closedAt
  rw [planesG_letter face sized hearing [] hv]
  rfl

/-! ## 3 The three sentences -/

section
variable {W : Type} (course : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE)
  {heard : HeardV} {behind closed : Fork} {claims : List PlaneClaim} (home : Array Slot) (maskEntry : Slot → E)
  (mask : Nat → GE)

/-- **`FormsObjects`: every form that the hearing left is worth 0.** -/
theorem lookupLeavesFormsObjects (left : Left course planes keys heard behind) (masks : MasksAre course mask)
    (closing : planesV course.f heard behind = some (claims, closed))
    (closes : closedAt course.f (toHeardG heard) behind = some (claims, closed))
    (reads : ∀ j, j < home.size → readE (maskEntry (home.getD j default)) = mask j)
    (scopedRows : ∀ a ∈ heard.rows.toList, ScopedG home.size a) :
    FormsObjects ReadAlike course.f (toHeardG heard) behind home maskEntry := by
  have later : Later behind closed := by
    unfold planesV at closing
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 closing
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
    exact MaskedSum.row_keeps hy
  refine ⟨claims, closed, closes, fun a ha => ?_⟩
  have ha' : a ∈ heard.rows.toList := ha
  obtain ⟨ne, inn⟩ := scopedRows a ha'
  refine ⟨ne, fun t ht => inn t (Array.mem_toList_iff.2 ht), ?_⟩
  show readE _ = readE zeroE
  rw [formWorthReadIsItsValue closed home maskEntry mask (fun _ _ _ => 0) a ne
    (fun t ht => reads t.1 (inn t ht)), readE_zero]
  exact (left.1 closed mask _ later masks).1 a ha'

/-- **`WorthPlanes`: each of the three claims on the planes holds at the true bits.** -/
theorem lookupLeavesWorthPlanes (left : Left course planes keys heard behind) (masks : MasksAre course mask)
    (sizedBehind : Sized behind)
    (closing : planesV course.f heard behind = some (claims, closed)) (three : claims.length = 3)
    (closes : closedAt course.f (toHeardG heard) behind = some (claims, closed))
    (reads : ∀ j, j < home.size → readE (maskEntry (home.getD j default)) = mask j)
    (scopedLeads : ∀ c ∈ claims, ScopedG home.size c.lead) (bit : Nat → E)
    (planesAre : ∀ c ∈ claims, planes c.pairs = readE (planeSum course.f c.pairs bit)) :
    WorthPlanes ReadAlike course.f (toHeardG heard) behind home maskEntry bit := by
  refine ⟨claims, closed, closes, three, fun c hc => ?_⟩
  obtain ⟨ne, inn⟩ := scopedLeads c hc
  refine ⟨ne, fun t ht => inn t (Array.mem_toList_iff.2 ht), ?_⟩
  show readE _ = readE zeroE
  rw [readE_add, readE_mul, formWorthReadIsItsValue closed home maskEntry mask (fun _ _ _ => 0) c.lead ne
    (fun t ht => reads t.1 (inn t ht)), readE_zero, ← planesAre c hc]
  exact left.2 behind closed closed claims mask _ sizedBehind (Later.refl _) closing (Later.refl _) masks c hc

/-- **`WorthKeys`: part by part, the form beside the key tree's last point is worth the sentence's sum.** -/
theorem lookupLeavesWorthKeys (left : Left course planes keys heard behind) (masks : MasksAre course mask)
    (closing : planesV course.f heard behind = some (claims, closed))
    (closes : closedAt course.f (toHeardG heard) behind = some (claims, closed))
    (reads : ∀ j, j < home.size → readE (maskEntry (home.getD j default)) = mask j)
    (scopedKeys : ∀ k ∈ heard.keys, ScopedG home.size k.2) (key : Nat → Nat → E)
    (asMany : heard.keys.length = course.f.parts.length)
    (formsAre : ∀ x ∈ heard.keys.zipIdx, x.1.2 = course.form (.key x.2 (course.f.parts.getD x.2 0)))
    (keysAre : ∀ x ∈ heard.keys.zipIdx,
      rd course.pts.alpha - keys x.2 (course.pts.keyPt x.2 (course.f.parts.getD x.2 0)) =
        readE (sumE (2 ^ course.f.parts.getD x.2 0) fun k =>
          mulE ((Tensor.eq x.1.1.toList.reverse).entry k) (subE heard.alpha (key x.2 k)))) :
    WorthKeys ReadAlike course.f (toHeardG heard) behind home maskEntry key := by
  have later : Later behind closed := by
    unfold planesV at closing
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 closing
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
    exact MaskedSum.row_keeps hy
  refine ⟨asMany, claims, closed, closes, fun x hx => ?_⟩
  have hx' : x ∈ heard.keys.zipIdx := hx
  have hget : heard.keys[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx'
  have hmem : x.1 ∈ heard.keys := List.mem_of_getElem? hget
  obtain ⟨ne, inn⟩ := scopedKeys x.1 hmem
  refine ⟨ne, fun t ht => inn t (Array.mem_toList_iff.2 ht), ?_⟩
  show readE _ = readE _
  have hlt : x.2 < course.f.parts.length := by
    rw [← asMany]
    exact (List.getElem?_eq_some_iff.1 hget).1
  have hpart : (course.f.parts.getD x.2 0, x.2) ∈ course.f.parts.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    show course.f.parts[x.2]? = some (course.f.parts.getD x.2 0)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl
  rw [formWorthReadIsItsValue closed home maskEntry mask (fun _ _ _ => 0) x.1.2 ne
    (fun t ht => reads t.1 (inn t ht)), formsAre x hx']
  exact ((left.1 closed mask _ later masks).2 _ hpart).trans (keysAre x hx')

end

end ProofFile.Honest.K3.Key

#print axioms ProofFile.Honest.K3.Key.formWorthReadIsItsValue
#print axioms ProofFile.Honest.K3.Key.closingReturnsBehindTheHearing
#print axioms ProofFile.Honest.K3.Key.lookupLeavesFormsObjects
#print axioms ProofFile.Honest.K3.Key.lookupLeavesWorthPlanes
#print axioms ProofFile.Honest.K3.Key.lookupLeavesWorthKeys
