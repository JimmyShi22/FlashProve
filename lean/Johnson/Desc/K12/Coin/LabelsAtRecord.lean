-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LabelsAtRecord.lean: **THE SEAM AT THE LABELS, ITS PREMISE AT THE RECORD
ITSELF** (first arm). One statement with its proof.
LabelsToPlaces.lean asks "the book is in order" of the book of the plain data that the record fixes
(D.book under `Fixes`). Where the first fold's mask has come ahead that book is the record's own
(`book_of_fixes`, FirstBook.lean). So:
  `qn_places_at_record`: the mask has come · `BookOrd π.nums.firstTree t.book` · the game's
    conclusion at the labels ⇒ the conclusion at the places z ↦ lo + z.
Both premises are tests with code on the record behind the door in.
Limits: those of LabelsToPlaces.lean. NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.K12.Coin.LabelsToPlaces
import Johnson.Desc.K12.Coin.FirstBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pin (NTuple)

/-- **At the record behind the door in.** -/
theorem qn_places_at_record (F : Frame) (π : P12) (lo : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (x : T12 × F.E.Str) (hm : x.1.mask.isSome = true)
    (hO : BookOrd π.nums.firstTree x.1.book)
    (h : QN π (NTuple F π (nuOf π (nlAt π lo) x.1) rad rd) x) :
    QN π (NTuple F π (fun z => lo + z) rad rd) x :=
  qn_places_of_labels F π lo rad rd x
    (fun a rest G0 Ly D hf => by rw [book_of_fixes π x.1 hm a rest G0 Ly D hf]; exact hO) h

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.qn_places_at_record
