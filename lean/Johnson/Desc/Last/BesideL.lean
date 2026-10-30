-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/BesideL.lean: A TEST ON THE SHARED CHAIN's LAST RECORD LAID BESIDE THE LAST
TABLE's BOOK-KEEPING. One definition, one theorem.

Why. The last table's promise (onL, Johnson/Desc/Last/BordersLast.lean) holds of the shared chain's
last record e only Omega's "no collision" and PL.shape k q e s. What a row's link needs of e beside
(that Omega sits in it as the plan says) is laid into the shape: as besideP does at the shared
table.

  besideL PL X     shape k q e s && X e; nothingLeft as it was.
  onQ₃_beside      the promise at the layer is the promise, with X e = true beside.
USER     Johnson/Flat/Last/RowZeroBeside.lean (row 0 at the layer).
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean).
What is not claimed. That the layer's promise at border 0 is earned: the last chain's door's.
Nothing on soundness.

-/
import Johnson.Desc.Sound.BordersLastQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last

/-- **The layer**: a test on the shared chain's last record, beside the book-keeping. -/
def besideL {S₂ S₃' Q : Type} (PL : PromMeaningL S₂ S₃' Q) (X : S₂ → Bool) :
    PromMeaningL S₂ S₃' Q where
  shape := fun k q e s => PL.shape k q e s && X e
  nothingLeft := PL.nothingLeft

/-- The promise at the layer is the promise, with the test's yes beside. -/
theorem onQ₃_beside {P S₁ S₂ S₃' Wt : Type} {Fr : Frame} (N : NumbersS)
    (Mg : MeaningS S₂ (P × S₁) Wt) (Pm : PromMeaning S₂) (PL : PromMeaningL S₂ S₃' (P × S₁))
    (Oc : P × S₁ → Strs → Prop) (X : S₂ → Bool) (k : ℕ)
    (a : ((P × S₁ × S₂) × S₃') × Fr.E.Str) :
    onQ₃ N Mg Pm (besideL PL X) Oc k a ↔ onQ₃ N Mg Pm PL Oc k a ∧ X a.1.1.2.2 = true := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨h4a, h4b⟩ := Bool.and_eq_true_iff.1 h4
    exact ⟨⟨h1, h2, h3, h4a, h5⟩, h4b⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, hx⟩
    exact ⟨h1, h2, h3, Bool.and_eq_true_iff.2 ⟨h4, hx⟩, h5⟩

end VerifiableInference.OnPublicFiles.Last
