-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/TruthAtState.lean: THE OUTPUT HEAD'S OWN ROUNDS, THE HONEST PROVER'S SIDE:
FROM "WHAT LIES HIDDEN IS Tables.lean'S VALUES" TO "THE ROUNDS AT THE STATE s ARE AT THE TRUTH OF
THE CELLS" (Johnson/Desc/Kinds/Law/K06ClosedTruth.lean: TruthK6N).
WHAT IT IS NOT. It packs: one call and one tuple. CONDITIONAL: EVERY PART IS A PREMISE: that the
verifier's letters at the state are g; that the cells meet the equations (Holds, HonestHead);
canonical writing; the rounds' shape; the hearing's return; five sizes and zt's; and HidesTables. No
prover, no round, no coin. Nothing on whether the verifier accepts, on soundness, on completeness or
on what a proof hides. Mathlib and Johnson/Desc/Kinds/Law/ are in the closure of its imports.
CALLED: truthHeard_of_tables (TruthOfTables.lean).

-/
import Mathlib
import Johnson.Desc.K6.Honest.TruthOfTables

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open Norm (lt lPd)
open VerifiableInference.Desc.First (S)

/-- **TruthK6N AT THE STATE.** The letters of all that follows hg are g's, through the class
Given. -/
theorem truthK6N_of_hides (h : OnBytes.Model.Head.Shape) (iU3 work : Nat) (s : S) (c : NCells)
    (mask : Nat → E) (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork) (g : Given)
    (hg : given (parOf h work) (seatAt h iU3) s = .ok g) (hH : (dataOf c).Holds)
    (hC : HonestHead c.toCells) (hcan : Canonical rs) (hsh : ShapedNZ rs rounds)
    (hh : hear ((seatAt h iU3).ledger s) rs = some (H, G, [])) (sPV : H.1.pV.size = lt)
    (sS : H.1.squares.r.size = lPd + lt) (sP : H.1.products.r.size = lt)
    (sN : H.2.1.normed.r.size = lt) (sL : H.2.2.logits.r.size = lt + lPd)
    (hzt : (FinalNorm.zt).size = lt) (A : Honest.HidesTables c mask H G) :
    TruthK6N h iU3 work s c mask rs H G := by
  obtain ⟨a, b⟩ := Honest.truthHeard_of_tables c mask hh A sPV sS sP sN sL hzt
  exact ⟨g, hg, hH, hC, hcan, hsh, a, b⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.truthK6N_of_hides
