-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OwnOfKeeps.lean

Limits. One small statement on two definitions of ours. It says nothing of any thread, and nothing
of any clause but `riderOwn`. Nothing on soundness, on completeness or on any other property.
No property is claimed.

What is here, and why. `k4_behind_all` (Law/ElevenHead.lean) asks hRd: what rides at the border in
front of the member of the layers' own rounds (kind K4) rides at the border behind, FROM THE
MEMBER's CLAUSE OF keeps ALONE: neither the step nor the thread is in hand. A clause that begins
at the border behind is asked there and not in front: so hRd can hold only if such a clause
follows from `K4KeepsM`. The clause on the reading own? (`riderOwn`, Law/LaysOwn.lean) begins just
there. It follows: `K4Keeps` holds the sentence in its own text.

  `riderOwn_of_keepsM`: from K4KeepsM s s', the clause's sentence at s', at every lo, hi, border
      and input.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LaysOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (First.S)

/-- **The clause on own? follows from the member's clause of keeps alone.** -/
theorem riderOwn_of_keepsM {W : Type} {s s' : First.S} (h : K4KeepsM s s') (lo hi c : Nat) (w : W) :
    (riderOwn (W := W) lo hi).prop c w s' := by
  obtain ⟨⟨-, _, _, o, -, -, ho, -⟩, -⟩ := h
  exact ⟨o, ho⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.riderOwn_of_keepsM
