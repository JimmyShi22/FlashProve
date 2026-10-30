-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PoweredOfYes.lean: THE SMALLNESS TEST: THE RECORD THAT THE LIST OF CLAIMS
"K8.equations" (`equations`, Johnson/Desc/First/TailClaims/Equations.lean) RETURNS HOLDS THE POWERS
OF THE LEDGER's BATCHING ELEMENT: `Powered tl' F.theta` (OnBytes/Tie/Pv/Tail/EndClosed.lean). One
statement and its proof. On the list's text alone: no block, no prover. A lemma; none of the
library's goals.

  **`powered_of_yes`**   equations front tl funs F = .ok (tl', F1, cls) gives `Powered tl' F.theta`:
      among its fields: tl'.vt and tl'.vp are the first tau powers of F.theta; tl'.rowX[mu] the
      first mS powers of F.theta ^ stepF
By: eq_parts (Johnson/Desc/First/TailClaims/EquationsCover.lean) · tame_keys, tame_counts
(EquationsTame.lean) · eqTail_total (EquationsTotal.lean) · eqWeights_spec (EquationsForms.lean).
Limits. From a yes alone. Nothing on the ledger that is returned.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.TailClaims.EquationsForms
import Johnson.Desc.First.TailClaims.EquationsCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port (Powered)

/-- **What the list's return holds of the batching element.** -/
theorem powered_of_yes {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    Powered tl' F.theta := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h1, h2, h3, -⟩ := eq_parts h
  obtain ⟨o1, -⟩ := tame_keys tl _ _ _ _ h1
  obtain ⟨o2, -⟩ := tame_counts tla _ _ _ _ h2
  obtain ⟨tl1, hW, -, -, etl, -, -⟩ := eqTail_total Reading.gl
    (⟨fun _ => 0, fun _ _ _ => 0⟩ : World Cb.Gl.E) F before tlb tl' funs front s2 _ h3
  obtain ⟨hP1, -, -⟩ := eqWeights_spec tlb tl1 front s2 s2 hW
  have eth : s2.1.theta = F.theta := o2.theta.trans o1.theta
  rw [← eth, etl]
  exact ⟨hP1.vp, hP1.vt, hP1.rowX, hP1.loX, hP1.eqFirst, hP1.shape⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.powered_of_yes
