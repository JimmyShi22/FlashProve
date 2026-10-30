-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/DeadBlocks.lean: THE SMALLNESS TEST: THE BOUND OF Johnson/Desc/K8/Honest/DeadTest.lean
("some column of the drawn matrix is all 0") AT THE KIT WHOSE CHALLENGES ARE STRINGS OF HASH BLOCKS
(Run.ckP .two, Run/PlanPull.lean): THE SAME NUMBER AS AT TYPED CHALLENGES. Lemmas; none of the
library's goals. No block, no state of the chain, no prover. Nothing on completeness, soundness or
hiding. An assembly: no new argument.

  `exAll_trits`   a round that draws entries of a matrix and nothing else has the exponent 0: the
      factor for the sampler's bias is 1 there
  `dead_vals`   at most as many typed values show a list at which `deadT` says yes as there are
      typed matrices with a column that is all 0
  **`dead_gate_blocks`**   s the typed side's sizes, d a round's data whose list of draws is [.trits
      (columns * tau)], its entry's positions of at most 64 bits: the measure (Iop.prRho, uniform on
      that one round's messages at Run.ckP .two) of the messages at which `deadT s` says yes of what
      is shown is at most columns / 2 ^ tau
By: `prRho_test_le` (Johnson/Desc/K8/Honest/CountToRho.lean) · `dead_iff`, `dead_chance` ·
`ratio_div` (Johnson/P1K8R/UnitsBlocks.lean) · matOf, matOf_inj, drawn_trits
(OnBytes/Tie/Pv/Tail/CarryRng.lean) · bsRound_good_ex (OnBytes/Slice/RatesEx.lean) · card_vals_all
(OnBytes/Slice/Rates.lean) · card_dr (Cb/Pv/Tail/Size.lean).
Limits. One round. The uniform law on that round's strings of blocks is named, not derived. That s
is the size of any place of a description is not said. No number is evaluated.

-/
import Johnson.Desc.K8.Honest.DeadTest
import Johnson.P1K8R.UnitsBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Slice
open OnBytes.Maker (RDT uLT drawnT)
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open VerifiableInference.Desc.First.K8.Honest
open Iop
open scoped ENNReal

/-- A round that draws entries of a matrix alone has the exponent 0. -/
theorem exAll_trits (e : Fmt.Entry) (k : Fmt.Kind) (n : ℕ) (h : Fmt.dsOf e k = [.trits n]) :
    _root_.Run.exAll (Fmt.dsOf e k) = 0 := by
  rw [h]
  rfl

/-- The typed values at which the test speaks. -/
theorem dead_vals (s : Size) (e : Fmt.Entry) (k : Fmt.Kind)
    (h : Fmt.dsOf e k = [.trits (s.columns * s.tau)]) :
    Prob.cnt (fun v : _root_.Run.Vals .two (Fmt.dsOf e k) =>
      deadT s [_root_.Run.drawnOf .two e k v] = true) ≤
      Prob.cnt (fun β : Dr s => ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) := by
  have h' : OnlyTrits (⟨e, k, [], none, []⟩ : _root_.Run.PQ.RD) (s.columns * s.tau) := h
  have h1 := Prob.cnt_comp_le (matOf s _ h') (w := 1)
    (fun β => Prob.cnt_le_one fun a b ha hb => matOf_inj s _ h' (ha.trans hb.symm))
    (fun β : Dr s => ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0)
  rw [Nat.mul_one] at h1
  refine (Prob.cnt_mono fun v hv => ?_).trans h1
  refine (dead_iff _).1 ?_
  rw [← drawn_trits s _ h' v]
  exact hv

/-- **At strings of hash blocks.** -/
theorem dead_gate_blocks (s : Size) (d : RDT)
    (h : Fmt.dsOf d.entry d.kind = [.trits (s.columns * s.tau)]) (hlog : d.entry.logN ≤ 64) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
        deadT s (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
      (s.columns : ℝ≥0∞) / 2 ^ s.tau := by
  haveI : Nonempty (Dr s) := ⟨fun _ _ _ => (false, false)⟩
  have hg := bsRound_good_ex d.entry d.kind hlog
  have hcnt : Prob.cnt (fun u : (_root_.Run.ckP .two).Ch d.entry d.kind =>
      deadT s [(_root_.Run.ckP .two).dr d.entry d.kind u] = true) ≤
      Prob.cnt (fun β : Dr s => ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) *
        (_root_.Run.bsRound .two d.entry d.kind).w :=
    (Prob.cnt_comp_le (_root_.Run.bsRound .two d.entry d.kind).φ hg.fib
      (fun v => deadT s [_root_.Run.drawnOf .two d.entry d.kind v] = true)).trans
      (Nat.mul_le_mul_right _ (dead_vals s d.entry d.kind h))
  refine (prRho_test_le (_root_.Run.ckP .two) d (deadT s) _ hcnt).trans ?_
  have hr := hg.ratio
  rw [exAll_trits _ _ _ h, pow_zero] at hr
  have hN : Nat.card (_root_.Run.Vals .two (Fmt.dsOf d.entry d.kind)) = Fintype.card (Dr s) := by
    rw [card_vals_all, h, card_dr]
    simp [nVals]
  rw [hN] at hr
  have hB : Nat.card ((_root_.Run.ckP .two).Ch d.entry d.kind) =
      Fintype.card (Fin (_root_.Run.bsRound .two d.entry d.kind).b → Dig 256) :=
    Nat.card_eq_fintype_card
  have hB0 : Fintype.card (Fin (_root_.Run.bsRound .two d.entry d.kind).b → Dig 256) ≠ 0 :=
    (Fintype.card_pos_iff.2 ⟨fun _ _ => false⟩).ne'
  rw [hB, Nat.cast_mul]
  refine (ratio_div _ _ _ _ _ hr (by exact_mod_cast hB0) (ENNReal.natCast_ne_top _)
    (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)).trans ?_
  rw [one_mul]
  exact ENNReal.div_le_of_le_mul ((Prob.pr_unif_le_iff (C := Dr s) _ _).1 (dead_chance s))

end P1K8

#print axioms P1K8.exAll_trits
#print axioms P1K8.dead_vals
#print axioms P1K8.dead_gate_blocks
