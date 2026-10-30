-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/SharesCover.lean: the kind "lookup" (K3): the windows of
a lookup's three runs of claims, counted from the place's first slot, are together just the lookup's
own stretch of slots. A theorem.

Terms. `InWin p h r j` (Honest/K3/Good/Live/Shares.lean): slot j is in the window of the run r,
counted from p.first. The lookup's own stretch is from p.first on, `Forest.elems h` slots.

What is shown. `stretch_iff`: p.first ≤ j and j < p.first + `Forest.elems h` just where j is in the
window of some run. It is `window_iff` (Honest/K3/Good/Live/Windows.lean) in these words. No
hypothesis.


Limits. Numbers alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Shares
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Windows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc.First.Look (P)

/-- **The three windows together are just the lookup's own stretch.** -/
theorem stretch_iff (p : P) (h : Shape) (j : Nat) :
    (p.first ≤ j ∧ j < p.first + OnBytes.Model.Forest.elems h) ↔ ∃ r, InWin p h r j := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨r, hr⟩ := (window_iff h (j - p.first)).1 (by omega)
    exact ⟨r, j - p.first, hr, by omega⟩
  · rintro ⟨r, j', hj', rfl⟩
    have := (window_iff h j').2 ⟨r, hj'⟩
    omega

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.stretch_iff
