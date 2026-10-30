-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Ledger.lean: what the ledger shows under a slot into which one scalar has
just
been laid. Theorems with their proofs, on the pure functions Fork.hide, Fork.hideRun and Fork.shown
(OnBytes/Model/Hide.lean).

Main names: `hide_inv`, `hideRun_one`, `shown_hideRun_one`, `short_ledger`.

Limits: `shown_hideRun_one` asks that the array of shown values reaches the slot: Fork.hide tests
the
marks' length alone, and `short_ledger` shows that the premise cannot be dropped. Nothing on
soundness or on hiding.

-/
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open OnBytes.Model (Fork)

/-- One scalar laid: what `hide` does. -/
theorem hide_inv {F G : Fork} {j : Nat} {v b : E} (h : F.hide j v b = some G) :
    j < F.ns ∧ F.gotF.size = F.ns ∧
      G = { F with gotF := F.gotF.set! j true, vp := F.vp.set! j v, mf := F.mf.set! j b } := by
  unfold Fork.hide at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    simp only [Option.some.injEq] at h
    exact ⟨hc.1.1, hc.1.2, h.symm⟩
  · exact absurd h (by simp)

theorem hideRun_one {F G : Fork} {j : Nat} {v b : E} (h : F.hideRun j #[v] b = some G) : F.hide j v
    b = some G := by
  unfold Fork.hideRun at h
  cases hh : F.hide j v b with
  | none => simp [Fork.hideStep, hh] at h
  | some H =>
    simp [Fork.hideStep, hh] at h
    rw [h]

/-- **Where the array of shown values reaches the slot, the ledger behind shows there just the
scalar that was laid.** -/
theorem shown_hideRun_one {F G : Fork} {j : Nat} {v b : E} (h : F.hideRun j #[v] b = some G) (hv : j
    < F.vp.size) :
    G.shown j = some v := by
  obtain ⟨h1, h2, rfl⟩ := hide_inv (hideRun_one h)
  have hg : j < F.gotF.size := by omega
  simp [Fork.shown, h1, hg, hv]

/-- **A ledger that is not well made**: one slot, one mark, but no room in the array of shown
values: `hideRun` says yes, lays
nothing there, and the ledger behind shows 0, not the scalar 1 that was laid. So
`shown_hideRun_one`'s premise cannot be dropped. -/
theorem short_ledger (F : Fork) :
    (({ F with ns := 1, gotF := #[false], vp := #[] } : Fork).hideRun 0 #[oneE] oneE).bind (·.shown
        0) = some zeroE := by
  simp [Fork.hideRun, Fork.hideStep, Fork.hide, Fork.shown]

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.shown_hideRun_one
#print axioms VerifiableInference.Desc.First.MergeLaw.short_ledger
