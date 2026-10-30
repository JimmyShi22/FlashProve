-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/WindowLawBound.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: proofs of
four statements of Johnson/Desc/K8/Honest/WindowLaw.lean: how often the program `leaves` finds a
combination outside its window.

  `card_entries`    the number of all combinations, at the typed side's sizes
  `card_typed`      a round that draws the matrix's entries alone has as many typed values as there
                     are typed matrices
  `price_none`      at such a round, without work, the factor for the sampler's bias is 1 and the
                     divisor for the work is 1: a share stays what it was
  `pr_leaves_le`    `Spec.pr_leaves_le`: over a uniform typed matrix: by the library's
                     `Prob.pr_win_le` (Prob/Window.lean)
  `leaves_below`    `Spec.leaves_below`: by `below_round_div_ex` (OnBytes/Slice/RatesEx.lean), as
                     `rng_below` counts the same round for soundness
  `pass_no_work`    in a round without work every written verifier message passes the test of work
  `pr_written_le`   `Spec.pr_written_le`: over a uniform written verifier message: a message's own
                     sequence is that of its typed matrix (`drawn_view`,
                     OnBytes/Tie/Pv/Tail/CarryRng.lean), and at most w messages give one matrix
                     (`chalTo_fib`, OnBytes/Slice/Draws.lean)
  `term_le`         `Spec.term_le`: by the library's `Prob.ref_entry`
WHERE THREE OF THE PROOFS COME FROM: Johnson/Desc/First/K8/RoundsWritten.lean, which counts the same
round for soundness: `price_none` is its `price_eq`, `card_typed` a step of its `typed_le`, and the
proof of `leaves_below` that of its `rng_below`; written again here, since that file imports much
more.
The measure and the limits are those of Johnson/Desc/K8/Honest/WindowLaw.lean's head. Of these: that
the cells pass `cellsSmall` is a premise; `leaves_below` and `pr_written_le` ask a round that draws
the matrix's entries alone, without work, and whose entry in the plan states positions of at most 64
bits: the library's lemmas ask the last; such a round draws no position.
Words. Typed, and w: that head. A written verifier message: `RoundBelow`
(OnBytes/Slice/ManyErr.lean). Work: lean/GLOSSARY.md.
Lemmas; none of the library's goals.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.WindowLawProofs
import OnBytes.Slice.RatesEx
import Prob.Bias

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail OnBytes.Slice Iop
open OnBytes.Model (lbz)
open scoped ENNReal

/-- The number of all combinations, at the typed side's sizes. -/
theorem card_entries (s : Size) :
    Fintype.card (Σ μ : Fin s.NM, Fin (s.m μ) × Fin s.tau) = (∑ μ : Fin s.NM, s.m μ) * s.tau := by
  rw [Fintype.card_sigma, Finset.sum_mul]
  exact Finset.sum_congr rfl fun μ _ => by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- A round that draws the matrix's entries alone has as many typed values as there are typed
matrices. -/
theorem card_typed (s : Size) (d : Run.PQ.RD) (hd : OnlyTrits d (s.columns * s.tau)) :
    Nat.card (Run.Vals .two (Fmt.dsOf d.entry d.kind)) = Fintype.card (Dr s) := by
  rw [card_vals_all, hd, card_dr]
  simp [nVals]

/-- At a round that draws the matrix's entries alone, without work, the factor for the sampler's
bias and the divisor for the work are 1: a share stays what it was. -/
theorem price_none (d : Run.PQ.RD) {n : ℕ} (hd : OnlyTrits d n) (hw : d.entry.work = 0)
    (c : ℝ≥0∞) :
    kapSl 128 ^ Run.exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work) = c := by
  have e : Run.exAll (Fmt.dsOf d.entry d.kind) = 0 := by
    rw [hd]
    rfl
  rw [e, hw, pow_zero, pow_zero, one_mul, div_one]

theorem pr_leaves_le : Spec.pr_leaves_le := by
  intro p s cell n₂ h hn0 hn hb
  have hset : {β : Dr s | (leaves p cell (listOf β)).isSome = true} = {β | winAt cell β} :=
    Set.ext fun β => leaves_iff p s cell β h
  have hb' : ∀ (μ : Fin s.NM) (i : Fin (s.m μ)) (c : Fin (s.k μ)), |cellsOf cell μ i c| ≤ 128 := by
    intro μ i c
    have hμ : μ.val < p.ks.length := h.fits.nm ▸ μ.isLt
    exact (cellsSmall_iff p cell).1 hb μ.val hμ i.val (by rw [← h.m μ.val hμ]; exact i.isLt) c.val
      (by rw [← h.fits.k μ.val hμ]; exact c.isLt)
  rw [hset]
  have key := Prob.pr_win_le (Mx := Fin s.NM) (U := Fin s.tau) (I := fun μ => Fin (s.m μ))
    (J := fun μ => Fin (s.k μ)) (cellsOf cell) 128 ((2 : ℤ) ^ lbz) n₂ hb' (by norm_num) hn0
    (fun μ => by rw [Fintype.card_fin]; exact hn μ) (by positivity)
  rw [card_entries] at key
  exact key

theorem leaves_below : Spec.leaves_below := by
  intro p s cell n₂ d h hn0 hn hb hd hw hlog
  have h1 := (Prob.pr_unif_le_iff (C := Dr s)
    (fun β => (leaves p cell (listOf β)).isSome = true) (windowBound s n₂)).1
    (pr_leaves_le p s cell n₂ h hn0 hn hb)
  have b := below_round_div_ex d hlog _ (windowBound s n₂) (by rw [card_typed s d hd]; exact h1)
  rw [price_none d hd hw] at b
  exact b

/-- In a round without work every written verifier message passes the test of work. -/
theorem pass_no_work (d : Run.PQ.RD) (hw : d.entry.work = 0) (c : (wRound d).Chal) :
    GChal.pass (b := d.entry.work) c = true := by
  unfold GChal.pass
  exact decide_eq_true fun i => absurd i.isLt (by omega)

theorem pr_written_le : Spec.pr_written_le := by
  intro p s cell n₂ d h hn0 hn hb hd hw hlog
  have hB := leaves_below p s cell n₂ d h hn0 hn hb hd hw hlog
  have hfib : ∀ β : Dr s,
      Prob.cnt (fun c : (wRound d).Chal => matOf s d hd (valsOf d c) = β) ≤
        (Run.bsRound .two d.entry d.kind).w := by
    intro β
    refine le_trans (Prob.cnt_mono fun c hc => ?_)
      (chalTo_fib d (matOf s d hd) (matOf_inj s d hd) hlog β)
    unfold chalTo
    rw [if_pos (pass_no_work d hw c), hc]
  have hcnt := Prob.cnt_comp_le (fun c : (wRound d).Chal => matOf s d hd (valsOf d c)) hfib
    fun β => (leaves p cell (listOf β)).isSome = true
  have hEq : (fun c : (wRound d).Chal => (leaves p cell (writtenEntries d c)).isSome = true) =
      fun c => (leaves p cell (listOf (matOf s d hd (valsOf d c)))).isSome = true :=
    funext fun c => by
      unfold writtenEntries
      rw [drawn_view s d hd c]
  rw [Prob.pr_unif_le_iff (C := (wRound d).Chal)
    (fun c => (leaves p cell (writtenEntries d c)).isSome = true), hEq]
  exact le_trans (by exact_mod_cast hcnt) hB

theorem term_le : Spec.term_le := by
  intro n₂ h0 hn
  have hl : lbz = 17 := rfl
  have hn' : (n₂ : ℝ) ≤ 2 ^ 13 := by exact_mod_cast hn
  have h0' : (0 : ℝ) < n₂ := by exact_mod_cast h0
  have hx : (128 : ℝ) ≤ (((2 : ℤ) ^ lbz : ℤ) : ℝ) ^ 2 / (n₂ * ((128 : ℤ) : ℝ) ^ 2) := by
    rw [hl, le_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  have he := Real.exp_le_exp.2 (neg_le_neg hx)
  unfold windowTerm
  exact le_trans (by linarith) Prob.ref_entry

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.card_typed
#print axioms VerifiableInference.Desc.First.K8.Honest.price_none
#print axioms VerifiableInference.Desc.First.K8.Honest.pr_leaves_le
#print axioms VerifiableInference.Desc.First.K8.Honest.leaves_below
#print axioms VerifiableInference.Desc.First.K8.Honest.pr_written_le
#print axioms VerifiableInference.Desc.First.K8.Honest.term_le
