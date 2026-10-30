-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
E2E/Lookup/Key/LookupDataMeetTheRelationAtTheWrittenKey.lean: (K-values) THE TWO LOOKUPS' DATA MEET THE RELATION AFTER THE
CHALLENGE AT THE MATRIX's OWN DIGITS. For every matrix in range, and machine words that spell its cells, at every shift and every alpha: the three
sentences `KeyMidHyp` (Honest/K3/Parts/KeyMid.lean: the product of the parts' roots · a bit is 0 or 1 · the bits add up to
the keys that are no padding) hold of the library's two readers at the written sizes of the key: the keys read by `keyVec`
off the words, the bits read by `bitVec` off the honest array of the true counts' bits (`planesVal`). So the relation after
the challenge at parts (`DataP.Mid`) holds there. Theorems with proofs; two closed facts by Lean's kernel.

  `planesAtTheWrittenLookups`          the two faces have 40 and 39 real planes; both pass the face's own test and `okK`
  `keyMidHypAtTheFirstWrittenLookup`, `keyMidHypAtTheSecondWrittenLookup`   **`KeyMidHyp`**, at id 1, the matrix's numbers
                                       ⟨kRef, 3076096⟩, `lk0Full` | `lk1Full`
  `lookupDataMidAtTheFirstWrittenLookup`, `…Second…`   **`DataP.Mid`** at the specification's own numbers and `hidK` of the two
                                       readers, at every point: by `mid_key`

By what. `prod`: `mid_written0`, `mid_written1` (E2E/KeyMidAtWritten.lean), to the letter once the planes are 40 and 39.
`bit`: `bitVec_full` (E2E/KeyPlanesRead.lean) with `bit_is_bit` (E2E/KeyPlanes.lean). `count`: `bitVec_full`, `bits_sum`
(E2E/KeyPlanes.lean), `count_read` (E2E/KeyPadding.lean), `keysIn_words`, `card_full`, `runs_full`.

NOT EMPTY. `Flat.InRange` has a member (`inRange_zero`, Johnson/Top/H/KeyMeaning.lean); words that spell a matrix's cells
exist wherever every cell's first coordinate has a machine word.

Limits. THE TWO READERS ARE THE LIBRARY's; THAT THE OFFLINE PROVER's LETTERS `wit`, `jobs0`, `jobs1` AND ITS MESSAGE WITH THE
MULTIPLICITIES READ THESE IS NOT SAID HERE. That the prover runs at matrices in range alone is a premise on its letter
`inRange`, which no file lays. The written sizes alone. No round, no sumcheck, no mask, no coin.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.KeyMidAtWritten
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyMid

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.Lookup.Key
open Finset
open OnBytes.Slice (GF GE toF readE)
open Johnson.Pack (lk0Full lk1Full)
open VerifiableInference.Desc.Key (keyVec bitVec)
open Inst.Model.Layout (kRef)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.Key
open ProofFile.Honest.K3 (Pts)
open ProofFile.Honest.K3.Parts (dataP)
open ProofFile.Honest.K3.Parts.Key

/-- **The two faces at the written sizes**: 40 and 39 real planes; both pass the face's own test and the two conditions
on the public structure. By Lean's kernel. -/
theorem planesAtTheWrittenLookups :
    (faceK 1 ⟨kRef, 3076096⟩ lk0Full).planes = 40 ∧ (faceK 1 ⟨kRef, 3076096⟩ lk1Full).planes = 39 ∧
      (faceK 1 ⟨kRef, 3076096⟩ lk0Full).ok = true ∧ (faceK 1 ⟨kRef, 3076096⟩ lk1Full).ok = true ∧
      okK 1 ⟨kRef, 3076096⟩ lk0Full = true ∧ okK 1 ⟨kRef, 3076096⟩ lk1Full = true := by decide +kernel

section
variable (M : Fin Inst.Model.Layout.hRef → Fin (2 ^ kRef) → GE)
  (hM : VerifiableInference.OnPublicFiles.Flat.InRange M) (mat : ℕ → ℕ → OnBytes.F)
  (hmat : ∀ (y c : ℕ) (hy : y < Inst.Model.Layout.hRef) (hc : c < 2 ^ kRef),
    toF (mat y c) = (M ⟨y, hy⟩ ⟨c, hc⟩).c0)
include hM hmat

/-- **THE THREE SENTENCES AT THE FIRST LOOKUP OF THE WRITTEN KEY.** -/
theorem keyMidHypAtTheFirstWrittenLookup (theta alpha : OnBytes.E) :
    KeyMidHyp 1 ⟨kRef, 3076096⟩ lk0Full (keyVec ⟨kRef, 3076096⟩ lk0Full mat)
      (bitVec keyFull.ranges.x keyFull.codes 0
        (planesVal (fun y c => toF (mat y c)) kRef [lk0Full, lk1Full] (2 ^ 18) 1)) theta alpha := by
  have hp := planesAtTheWrittenLookups.1
  have hb := fun j (hj : j < 64) => (bitVec_full (fun y c => toF (mat y c)) keyFull.ranges.x keyFull.codes
    item_written.1 item_written.2.1 item_written.2.2.1 j hj).1
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]
    exact mid_written0 M hM mat hmat theta alpha
  · intro u hu j hj
    rw [hp] at hj
    have e := hb j (by omega) u hu
    rw [if_pos hj] at e
    have e' : readE (bitVec keyFull.ranges.x keyFull.codes 0
        (planesVal (fun y c => toF (mat y c)) kRef [lk0Full, lk1Full] (2 ^ 18) 1)
        (j + 2 ^ lk0Full.mu * u)) = algebraMap GF GE (bitOf (fun y c => toF (mat y c)) kRef lk0Full u j) := e
    rw [e']
    rcases bit_is_bit (fun y c => toF (mat y c)) kRef lk0Full u j with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rw [h, map_one])
  · rw [hp]
    have hc : (faceK 1 ⟨kRef, 3076096⟩ lk0Full).count = liveCount kRef lk0Full :=
      count_read 1 ⟨kRef, 3076096⟩ lk0Full fun p hp' => List.all_eq_true.1 runs_full.1 p hp'
    rw [hc, ← bits_sum (fun y c => toF (mat y c)) kRef lk0Full (algebraMap GF GE) (W := 40)
      (keysIn_words M hM mat hmat).1 inj₀ (by rw [card_full.1]; norm_num)]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 40 := Finset.mem_range.1 hj
    have e := hb j (by omega) t.val t.isLt
    rw [if_pos hj'] at e
    exact congrArg (fun z => (2 : GE) ^ j * z) e

/-- **THE THREE SENTENCES AT THE SECOND LOOKUP OF THE WRITTEN KEY.** -/
theorem keyMidHypAtTheSecondWrittenLookup (theta alpha : OnBytes.E) :
    KeyMidHyp 1 ⟨kRef, 3076096⟩ lk1Full (keyVec ⟨kRef, 3076096⟩ lk1Full mat)
      (bitVec keyFull.ranges.x keyFull.codes 1
        (planesVal (fun y c => toF (mat y c)) kRef [lk0Full, lk1Full] (2 ^ 18) 1)) theta alpha := by
  have hp := planesAtTheWrittenLookups.2.1
  have hb := fun j (hj : j < 64) => (bitVec_full (fun y c => toF (mat y c)) keyFull.ranges.x keyFull.codes
    item_written.1 item_written.2.1 item_written.2.2.1 j hj).2
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]
    exact mid_written1 M hM mat hmat theta alpha
  · intro u hu j hj
    rw [hp] at hj
    have e := hb j (by omega) u hu
    rw [if_pos hj] at e
    have e' : readE (bitVec keyFull.ranges.x keyFull.codes 1
        (planesVal (fun y c => toF (mat y c)) kRef [lk0Full, lk1Full] (2 ^ 18) 1)
        (j + 2 ^ lk1Full.mu * u)) = algebraMap GF GE (bitOf (fun y c => toF (mat y c)) kRef lk1Full u j) := e
    rw [e']
    rcases bit_is_bit (fun y c => toF (mat y c)) kRef lk1Full u j with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rw [h, map_one])
  · rw [hp]
    have hc : (faceK 1 ⟨kRef, 3076096⟩ lk1Full).count = liveCount kRef lk1Full :=
      count_read 1 ⟨kRef, 3076096⟩ lk1Full fun p hp' => List.all_eq_true.1 runs_full.2.1 p hp'
    rw [hc, ← bits_sum (fun y c => toF (mat y c)) kRef lk1Full (algebraMap GF GE) (W := 39)
      (keysIn_words M hM mat hmat).2 inj₁ (by rw [card_full.2]; norm_num)]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 39 := Finset.mem_range.1 hj
    have e := hb j (by omega) t.val t.isLt
    rw [if_pos hj'] at e
    exact congrArg (fun z => (2 : GE) ^ j * z) e

/-- **THE RELATION AFTER THE CHALLENGE, AT PARTS, AT THE FIRST LOOKUP**, at every point. -/
theorem lookupDataMidAtTheFirstWrittenLookup (points : Pts) :
    (dataP (numsK 1 ⟨kRef, 3076096⟩ lk0Full) (faceK 1 ⟨kRef, 3076096⟩ lk0Full).parts
      (faceK 1 ⟨kRef, 3076096⟩ lk0Full).orders
      (hidK lk0Full (keyVec ⟨kRef, 3076096⟩ lk0Full mat)
        (bitVec keyFull.ranges.x keyFull.codes 0
          (planesVal (fun y c => toF (mat y c)) kRef [lk0Full, lk1Full] (2 ^ 18) 1))) points).Mid :=
  mid_key 1 ⟨kRef, 3076096⟩ lk0Full _ _ points
    (keyMidHypAtTheFirstWrittenLookup M hM mat hmat points.theta points.alpha)
    planesAtTheWrittenLookups.2.2.1 planesAtTheWrittenLookups.2.2.2.2.1

/-- **AT THE SECOND LOOKUP.** -/
theorem lookupDataMidAtTheSecondWrittenLookup (points : Pts) :
    (dataP (numsK 1 ⟨kRef, 3076096⟩ lk1Full) (faceK 1 ⟨kRef, 3076096⟩ lk1Full).parts
      (faceK 1 ⟨kRef, 3076096⟩ lk1Full).orders
      (hidK lk1Full (keyVec ⟨kRef, 3076096⟩ lk1Full mat)
        (bitVec keyFull.ranges.x keyFull.codes 1
          (planesVal (fun y c => toF (mat y c)) kRef [lk0Full, lk1Full] (2 ^ 18) 1))) points).Mid :=
  mid_key 1 ⟨kRef, 3076096⟩ lk1Full _ _ points
    (keyMidHypAtTheSecondWrittenLookup M hM mat hmat points.theta points.alpha)
    planesAtTheWrittenLookups.2.2.2.1 planesAtTheWrittenLookups.2.2.2.2.2

end

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.planesAtTheWrittenLookups
#print axioms AtPublicFiles.Lookup.Key.keyMidHypAtTheFirstWrittenLookup
#print axioms AtPublicFiles.Lookup.Key.keyMidHypAtTheSecondWrittenLookup
#print axioms AtPublicFiles.Lookup.Key.lookupDataMidAtTheFirstWrittenLookup
#print axioms AtPublicFiles.Lookup.Key.lookupDataMidAtTheSecondWrittenLookup
