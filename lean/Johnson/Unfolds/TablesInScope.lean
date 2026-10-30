-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/TablesInScope.lean: the premise of Johnson/Unfolds/TablesHeld.lean and
TablesAtLayout.lean, "the strict scan returns on `policyFile v`", IS MET AT ALL PUBLIC FILES IN THE
GOALS' SCOPE, the stored full-size example's among them; and the three comparisons in that form.
  `scan_met`: in scope the scan of `Z.pol` returns (`scan_returns_in_scope`,
    Johnson/Goal/Numbers/PlanWrittenRow.lean).
  `scan_met_full`: so at `storedPublicFiles` (`VerifierAndGoals.inScope_full`, Johnson/Goal/Files/ScopeExample.lean).
  `scan_at_policy`: in scope `Z.pol` is `policyFile (freeLinesOf pp)` (`Hd.policy_of_scope`,
    Johnson/Goal/Meaning/ScopeCore.lean): a scan of `Z.pol` is a scan of that.
  **`steps_in_scope`**: in scope, at what the scan of `Z.pol` returns and at every layout that
    `Layer.layout` returns of it: the comparisons of the tables SILU, FS and of the rotary table
    return, and the shape has routed experts.
  `expected_in_scope`, `exp_step_in_scope`: the four expected digests; the fourth comparison, at
    what `expTable 12 8` returns.
Limits. That the layout returns is a premise. That the attention's plans hold `expTable 12 8`'s
value is not said here. At `secondHashFunction` alone. Calls alone.

-/
import Johnson.Unfolds.TablesAtLayout
import Johnson.Goal.Numbers.PlanWrittenRow
import Johnson.Goal.Files.ScopeExample

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Unfolds
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Road
open OnBytes.Model.Layer (Lay layout ropeOf)
open OnBytes.Model.Verify (layerShape)
open VerifiableInference.PlanWritten
open VerifierAndGoals (policyFile freeLinesOf)

/-- In scope the strict scan of the parameter file returns. -/
theorem scan_met {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) :
    ∃ P, polScan Z.pol = .ok P := by
  obtain ⟨P, hP, -⟩ := scan_returns_in_scope hZ
  exact ⟨P, hP⟩

/-- So at the stored full-size example's parameter file. -/
theorem scan_met_full : ∃ P, polScan VerifierAndGoals.storedPublicFiles.pol = .ok P := scan_met VerifierAndGoals.inScope_full

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
  (hR : VerifierAndGoals.readFiles Z = .ok pp) {P : PolScan} (hs : polScan Z.pol = .ok P)
include hZ hR hs

theorem scan_at_policy : polScan (policyFile (freeLinesOf pp)) = .ok P := by
  rw [← Hd.policy_of_scope hZ hR]
  exact hs

theorem expected_in_scope :
    P.tableExpected .silu = some Silu.D ∧ P.tableExpected .sigmoid = some Fs.D ∧
      P.tableExpected .rope = some Rope.D ∧ P.tableExpected .exp = some Exp.D :=
  expected_of_scan (scan_at_policy hZ hR hs)

theorem exp_step_in_scope (Tt : Array Nat) (ht : OnBytes.Attention.expTable 12 8 = some Tt) :
    tableHeldO secondHashFunction P .exp Tt = .ok () :=
  exp_held (scan_at_policy hZ hR hs) Tt ht

/-- **The three comparisons, in scope.** -/
theorem steps_in_scope {y : Lay} (hy : layout (layerShape P) P.polCalls = .ok y) :
    tableHeldO secondHashFunction P .silu y.silu = .ok () ∧ y.h.p3 = true ∧
      tableHeldO secondHashFunction P .sigmoid y.fs = .ok () ∧
      ∃ rope, ropeOf y.h = .ok rope ∧ tableHeldO secondHashFunction P .rope rope = .ok () :=
  have s := scan_at_policy hZ hR hs
  ⟨silu_step s hy, (tables_at_scan s hy).1, fs_step s hy, rope_step s hy⟩

end

end Johnson.Unfolds

#print axioms Johnson.Unfolds.scan_met
#print axioms Johnson.Unfolds.scan_met_full
#print axioms Johnson.Unfolds.scan_at_policy
#print axioms Johnson.Unfolds.expected_in_scope
#print axioms Johnson.Unfolds.exp_step_in_scope
#print axioms Johnson.Unfolds.steps_in_scope
