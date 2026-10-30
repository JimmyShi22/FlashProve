-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameCarryKey.lean: THE PREMISE hKey OF `carryFence_of` | `fence_of_in` |
`fence_of_in_link` (Johnson/Top/H0/Walk/FrameCarryFence.lean), PAID where the proof file's rounds
have data and base is at most the first chain's number of trees. Statements and proofs.
  `key_below`: ProofFile.wholeAt Z = some D · base ≤ D.t₁ ⟹ for every k below base: the first entry of
    `ProofFile.allAt Z` whose key (`ProofFile.keyAt Z`) is k bears the number k itself: so a number below base.
    By `whole_is_data` (Johnson/Top/H0/K2Caller/OrcAtZ.lean), `first_of_data_at` and `key_of_data`
    (Johnson/Top/H0/K2Hears/KeyOfData.lean), called.
  `fence_of_in_data`: `fence_of_in_link` with hKey so paid.
Limits. That `ProofFile.wholeAt Z` has data, and that base is at most D.t₁ at a border, are premises. No
soundness statement.

-/
import Johnson.Top.H0.Walk.FrameCarryFence
import Johnson.Top.H0.K2Caller.OrcAtZ
import Johnson.Top.H0.K2Hears.KeyOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (par9 first_of_data_at key_of_data)
open VerifiableInference.Desc.First.K2Caller

/-- **The first entry of the frame's list with a key below base bears that very number.** -/
theorem key_below (Z : ProofFile.Pub) (D : WholeD) (hW : ProofFile.wholeAt Z = some D) (base : ℕ)
    (hb : base ≤ D.t₁) : ∀ k L, k < base →
      (ProofFile.allAt Z).find? (fun L => ProofFile.keyAt Z L.no == k) = some L → L.no < base := by
  intro k L hk hL
  obtain ⟨N, c, hD⟩ := whole_is_data Z D hW
  have h1 := first_of_data_at hD frS.P.T.a 0 base [] hb k hk
  have h2 : (D.at frS.P.T.a).key₁ k = k := key_of_data hD k (Nat.lt_of_lt_of_le hk hb)
  dsimp only at h1
  rw [h2] at h1
  unfold ProofFile.allAt ProofFile.keyAt at hL
  rw [hW] at hL
  simp only [Option.map_some, Option.getD_some] at hL
  rw [hL] at h1
  have h3 : L.no = k := Option.some.inj h1
  rw [h3]
  exact hk

/-- **hF at a place that stands at a link, from four facts on the state and the file's data.** -/
theorem fence_of_in_data {P : Type} (Z : ProofFile.Pub) (D : WholeD) (hW : ProofFile.wholeAt Z = some D)
    (m base : ℕ) (hb : base ≤ D.t₁) (hp : (ProofFile.pAtK2 Z m).stands = .link)
    (In : P × S → Strs → Prop)
    (hIn : ∀ p s y, In (p, s) y →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Z m)).firstTree s = true ∧
      VerifiableInference.Desc.K12.Door.atFirstFits s = true ∧
      (∀ o ∈ singleRowsOracles s.live.frame.rows, o < s.book.place.size) ∧
      s.book.trees.size ≤ base) :
    ∀ p s y, In (p, s) y → CarryFence Z m base (rest s) :=
  fence_of_in_link Z m base hp In hIn (key_below Z D hW base hb)

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.key_below
#print axioms Johnson.Desc.First.Walk.Tied.fence_of_in_data
