-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/DeadGate.lean: THE SMALLNESS TEST: "SOME COLUMN OF THE DRAWN MATRIX IS ALL 0"
AS A BOUND ON THE LIBRARY's MEASURE OVER THE MESSAGES OF THE ONE ROUND THAT DRAWS THE MATRIX
(Iop.prRho over Iop.Rho (uLT C [d])), AT TYPED CHALLENGES. A lemma; none of the library's goals. No
block, no state of the chain, no prover. Nothing on completeness, soundness or hiding.

s: the typed side's sizes. d: the data of a round that draws the matrix's entries and nothing else:
its list of draws is [.trits (columns * tau)] (the text of OnlyTrits,
OnBytes/Tie/Pv/Tail/CarryRng.lean). The kit: typed challenges (Run.ck .two, Run/PlanDrawsQ.lean).
  `dead_same`   whether a typed matrix has a column that is all 0 is read off its list of entries
  **`dead_gate`**   the measure of the round's messages that show the list of entries of a typed
      matrix with a column that is all 0 is at most columns / 2 ^ tau
By: `dead_chance` (Johnson/Desc/K8/Honest/DeadChance.lean) · `prRho_one_le` (CountToRho.lean) ·
matOf, matOf_inj, drawn_trits (CarryRng.lean) · listOf_get (OnBytes/Tie/Pv/Tail/Draw.lean) ·
card_vals_all (OnBytes/Slice/Rates.lean) · card_dr (Cb/Pv/Tail/Size.lean).
Limits. One round. The event is a sentence with "there is a typed matrix whose list is shown", no
test with code. The uniform law on that round's messages: that the messages of any run have it is
not said. That s is the size of any place of a description is not said. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.DeadChance
import Johnson.Desc.K8.Honest.CountToRho
import OnBytes.Tie.Pv.Tail.CarryRng
import OnBytes.Slice.Rates
import Cb.Pv.Tail.Size
import Run.PlanDrawsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Slice
open OnBytes.Maker (RDT uLT drawnT)
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open scoped ENNReal

/-- A column that is all 0 is read off the list of entries. -/
theorem dead_same {s : Size} {β β' : Dr s} (h : listOf β' = listOf β)
    (hd : ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) :
    ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β' μ u c).val = 0 := by
  obtain ⟨μ, c, hz⟩ := hd
  refine ⟨μ, c, fun u => ?_⟩
  rw [← listOf_get β' μ c u, h, listOf_get β μ c u]
  exact hz u

/-- **The local bound at the round that draws the matrix.** -/
theorem dead_gate (s : Size) (d : RDT)
    (h : Fmt.dsOf d.entry d.kind = [.trits (s.columns * s.tau)]) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
        ∃ dr, drawnT (_root_.Run.ck .two) [d] ρ = [dr] ∧ ∃ β : Dr s,
          dr.trits.toArray = listOf β ∧
            ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0} ≤
      (s.columns : ℝ≥0∞) / 2 ^ s.tau := by
  have h' : OnlyTrits (⟨d.entry, d.kind, [], none, []⟩ : _root_.Run.PQ.RD)
      (s.columns * s.tau) := h
  have hcnt : Prob.cnt (fun v : _root_.Run.Vals .two (Fmt.dsOf d.entry d.kind) =>
      ∃ β : Dr s, (_root_.Run.drawnOf .two d.entry d.kind v).trits.toArray = listOf β ∧
        ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) ≤
      Prob.cnt (fun β : Dr s => ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) := by
    have h1 := Prob.cnt_comp_le (matOf s _ h') (w := 1)
      (fun β => Prob.cnt_le_one fun a b ha hb => matOf_inj s _ h' (ha.trans hb.symm))
      (fun β : Dr s => ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0)
    rw [Nat.mul_one] at h1
    refine (Prob.cnt_mono fun v hv => ?_).trans h1
    obtain ⟨β, e, hd⟩ := hv
    exact dead_same ((drawn_trits s _ h' v).symm.trans e) hd
  have hN : Nat.card (_root_.Run.Vals .two (Fmt.dsOf d.entry d.kind)) = Fintype.card (Dr s) := by
    rw [card_vals_all, h, card_dr]
    simp [nVals]
  refine (prRho_one_le (_root_.Run.ck .two) d _ _ hcnt).trans ?_
  have hd := (Prob.pr_unif_le_iff (C := Dr s) _ _).1 (dead_chance s)
  show _ / ((Nat.card (_root_.Run.Vals .two (Fmt.dsOf d.entry d.kind)) : ℕ) : ℝ≥0∞) ≤ _
  rw [hN]
  exact ENNReal.div_le_of_le_mul hd

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.dead_same
#print axioms VerifiableInference.Desc.First.K8.Honest.dead_gate
