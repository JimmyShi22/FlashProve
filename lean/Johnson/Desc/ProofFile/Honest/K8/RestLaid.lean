-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/RestLaid.lean: THE SMALLNESS TEST: TWO OF THE CLAUSES OF `K8Rest`
(Johnson/Desc/ProofFile/Honest/K8/TestsSplit.lean: the guards of the verifier's three tests behind
the adding that are not among the kind's share) AT DATA WHOSE KEPT SLOTS ARE THE LEDGER's OWN SLICE:
as the run "K8.lsTail" lays them. Lemmas on the verifier's own text; none of the library's goals.

  **`slots_laid`**   "the window is what was kept" (`selfSlots`) holds there outright: a thing is
                   compared with itself.
                   Johnson/Desc/ProofFile/Honest/K8/RestOf.lean proves that clause from an equation
                   on the kept slots; this form is for a caller that has the data as a structure
                   with that field laid
  **`size_laid`**   "as many kept slots as the window has" holds there if the window ends inside the
                   ledger's coefficients on slots
Limits. Two clauses of fourteen. That the window ends inside the ledger's coefficients is a premise.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TestsSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.TailClaims

/-- **The window is what was kept.** -/
theorem slots_laid (tl : HTailF2) (F : Fork) :
    selfSlots { tl with lsTail := F.LS.extract tl.slotA tl.slotB } F = true := by
  unfold selfSlots
  exact beq_self_eq_true _

/-- **As many kept slots as the window has.** -/
theorem size_laid (tl : HTailF2) (F : Fork) (h : tl.slotB ≤ F.LS.size) :
    ((F.LS.extract tl.slotA tl.slotB).size == tl.slotB - tl.slotA) = true := by
  rw [Array.size_extract, Nat.min_eq_left h]
  exact beq_self_eq_true _

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.slots_laid
#print axioms ProofFile.Honest.K8.size_laid
