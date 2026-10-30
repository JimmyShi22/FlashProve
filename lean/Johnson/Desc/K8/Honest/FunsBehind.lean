-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/FunsBehind.lean: THE SMALLNESS TEST: THE DRAW's MEMBER LEAVES THE SENTENCE
"THE CALLER's LIST OF TABLES IS THE RECORD's OWN". One theorem; no definition; none of the
library's goals.

  `funs_behind_keeps`   `K8Keeps` s s' (Johnson/Desc/K8/Honest/Keeps.lean) · ∃ tl, s.tl? = some tl ∧
                   s.funs? = some tl.funs ⊢ the same sentence of s'
WHAT IT IS FOR. In front of a draw the library has that sentence (`k8FunsAre`,
Johnson/P1K8R/FunsAtSeat.lean); the library's law on the run "small" wants it behind.
HOW. `putTl_funs` (Johnson/Desc/First/K8/LawFunsStay.lean) and `K8Keeps.tl`.
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. NO TACTIC THAT SEARCHES.
Limits. On two states alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.Keeps
import Johnson.Desc.First.K8.LawFunsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (putTl_funs)

/-- The draw's member leaves the sentence. -/
theorem funs_behind_keeps {s s' : S} (hk : K8Keeps s s')
    (h : ∃ tl, s.tl? = some tl ∧ s.funs? = some tl.funs) :
    ∃ tl, s'.tl? = some tl ∧ s'.funs? = some tl.funs := by
  obtain ⟨tl₀, h0, hf0⟩ := h
  obtain ⟨tl, cf, first, h1, h2⟩ := hk.tl
  obtain rfl : tl₀ = tl := Option.some.inj (h0.symm.trans h1)
  refine ⟨_, h2, ?_⟩
  rw [hk.leaves S.funs? putTl_funs]
  exact hf0

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.funs_behind_keeps
