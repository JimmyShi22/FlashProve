-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/DeadTest.lean: THE SMALLNESS TEST: "SOME COLUMN OF THE DRAWN MATRIX IS ALL 0"
AS A TEST WITH CODE ON WHAT THE ROUND THAT DRAWS THE MATRIX SHOWS, AND THE BOUND OF
Johnson/Desc/K8/Honest/DeadGate.lean FOR THAT TEST. Definitions, statements and proofs. Lemmas; none
of the library's goals. No block, no state of the chain, no prover. Nothing on completeness,
soundness or hiding.

  `deadB s a`   of a list a of entries: some column's tau entries are all 0, read at the verifier's
      own index ((the columns in front + c) * tau + u), with the verifier's fallback 0
  `deadT s ds`   of what a stretch of rounds shows: it is one round, and `deadB` says yes of its
      list of entries
  `dead_iff`   at the list of a typed matrix `deadB` says yes just if some column of the matrix is
      all 0
  **`dead_gate_test`**   at typed challenges (Run.ck .two), d a round whose list of draws is [.trits
      (columns * tau)]: the measure (Iop.prRho, uniform on that one round's messages) of the
      messages at which `deadT s` says yes of what is shown is at most columns / 2 ^ tau
By: `dead_gate` · listOf_get (OnBytes/Tie/Pv/Tail/Draw.lean) · matOf, drawn_trits
(OnBytes/Tie/Pv/Tail/CarryRng.lean).
Limits. Those of DeadGate.lean. `deadB` is a test's text: it is run nowhere here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.DeadGate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Slice
open OnBytes.Maker (RDT uLT drawnT)
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open scoped ENNReal

/-- Some column's tau entries of the list are all 0. -/
def deadB (s : Size) (a : Array Int) : Bool :=
  decide (∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u : Fin s.tau,
    a.getD ((firstCol s μ + c.val) * s.tau + u.val) 0 = 0)

/-- The same of what a stretch of rounds shows. -/
def deadT (s : Size) : List Fmt.Drawn → Bool
  | [dr] => deadB s dr.trits.toArray
  | _ => false

theorem dead_iff {s : Size} (β : Dr s) :
    deadB s (listOf β) = true ↔ ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0 := by
  unfold deadB
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨μ, c, h⟩
    exact ⟨μ, c, fun u => by rw [← listOf_get β μ c u]; exact h u⟩
  · rintro ⟨μ, c, h⟩
    exact ⟨μ, c, fun u => by rw [listOf_get β μ c u]; exact h u⟩

/-- **The local bound for the test with code.** -/
theorem dead_gate_test (s : Size) (d : RDT)
    (h : Fmt.dsOf d.entry d.kind = [.trits (s.columns * s.tau)]) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
        deadT s (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤
      (s.columns : ℝ≥0∞) / 2 ^ s.tau := by
  have h' : OnlyTrits (⟨d.entry, d.kind, [], none, []⟩ : _root_.Run.PQ.RD)
      (s.columns * s.tau) := h
  refine (Prob.pr_mono _ fun ρ hρ => ?_).trans (dead_gate s d h)
  obtain ⟨a, u⟩ := ρ
  have hv := drawn_trits s _ h' (Iop.GChal.old (b := d.entry.work) a)
  refine ⟨_, rfl, matOf s _ h' (Iop.GChal.old (b := d.entry.work) a), hv, ?_⟩
  refine (dead_iff _).1 ?_
  rw [← hv]
  exact hρ

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.dead_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.dead_gate_test
