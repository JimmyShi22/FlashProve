-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/WindowLawEach.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: how often a
combination leaves its window, MATRIX BY MATRIX, each matrix at its own number of columns; and how a
bound over typed matrices is carried to a written round. Statements and proofs. LEMMAS ON ONE EVENT
AT WHICH AN HONEST PROVER CANNOT GO ON; NONE OF THE LIBRARY's GOALS.

  `winOf cell μ β`     the library's window event in matrix μ alone
  `termAt k`           one combination's term at k columns; 0 at no column
  `pr_leaves_sum`      the program finds a combination outside its window with at most the sum, over
                        the matrices, of the probabilities of `winOf`
  `pr_winOf_le`        for one matrix: at most (its rows of cells) * tau * `termAt` (its columns),
                        if the cells pass `cellsSmall`: by the library's `Prob.pr_window_le`; where
                        the matrix has a column the proof follows that of the library's
                        `Prob.pr_win_le` (Prob/Window.lean) step by step
  `written_of_typed`   A NUMBER THAT BOUNDS THIS ONE EVENT OVER A UNIFORM TYPED MATRIX BOUNDS IT
                        OVER A UNIFORM WRITTEN VERIFIER MESSAGE of a round that draws the matrix's
                        entries alone, without work: the event at the sequence that the message
                        itself gives
The measure is that of Johnson/Desc/K8/Honest/WindowLaw.lean: uniform typed matrices and uniform
written verifier messages, never a count of drawn sequences.
Limits. That the place's numbers are the typed side's (`FitsRows`) and that the cells pass
`cellsSmall` are premises of `pr_leaves_sum` (the first) and `pr_winOf_le` (both); `pr_winOf_le`
asks the second of all matrices and spends it at its own. `cellsSmall` asks every entry of the shape
of every matrix of the place's list: the matrices that hold the bits of a lookup's multiplicities,
and the cells that no other claim reads, among them. `written_of_typed` asks neither; beside the two
conditions on the round in the list above it asks that the round's entry in the plan states
positions of at most 64 bits.
`pr_leaves_sum` and `pr_winOf_le` are not joined here, and no number is given for `termAt`. One
round of one request: no sum over segments or requests. That a proof file's chain has such a written
round at the kind's place is not said here.
Words. Typed: Johnson/Desc/K8/Honest/WindowLaw.lean's head. A written verifier message:
`RoundBelow` (OnBytes/Slice/ManyErr.lean). Work: lean/GLOSSARY.md.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.WindowLawBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail OnBytes.Slice Iop
open OnBytes.Model (lbz)
open scoped ENNReal

/-- The library's window event in matrix μ alone. -/
def winOf {s : Size} (cell : CellsAt) (μ : Fin s.NM) (β : Dr s) : Prop :=
  ∃ y : Fin (s.m μ) × Fin s.tau,
    ¬ (-((2 : ℤ) ^ lbz) ≤ Prob.comb (cellsOf cell μ y.1) (β μ y.2) ∧
      Prob.comb (cellsOf cell μ y.1) (β μ y.2) < (2 : ℤ) ^ lbz)

/-- One combination's term at k columns; 0 at no column. -/
noncomputable def termAt (k : ℕ) : ℝ≥0∞ := if k = 0 then 0 else ENNReal.ofReal (windowTerm k)

theorem pr_leaves_sum (p : Par) (s : Size) (cell : CellsAt) (h : FitsRows p s) :
    Prob.pr (Prob.unif (Dr s)) {β | (leaves p cell (listOf β)).isSome = true} ≤
      ∑ μ : Fin s.NM, Prob.pr (Prob.unif (Dr s)) {β | winOf cell μ β} := by
  have hset : {β : Dr s | (leaves p cell (listOf β)).isSome = true} =
      {β | ∃ μ : Fin s.NM, winOf cell μ β} := by
    ext β
    rw [Set.mem_setOf_eq, leaves_iff p s cell β h]
    constructor
    · rintro ⟨⟨μ, y⟩, hx⟩
      exact ⟨μ, y, hx⟩
    · rintro ⟨μ, y, hx⟩
      exact ⟨⟨μ, y⟩, hx⟩
  rw [hset]
  exact Prob.pr_exists_le _ _

theorem pr_winOf_le (p : Par) (s : Size) (cell : CellsAt) (h : FitsRows p s)
    (hb : cellsSmall p cell = true) (μ : Fin s.NM) :
    Prob.pr (Prob.unif (Dr s)) {β | winOf cell μ β} ≤
      ((s.m μ * s.tau : ℕ) : ℝ≥0∞) * termAt (s.k μ) := by
  have hμ : μ.val < p.ks.length := h.fits.nm ▸ μ.isLt
  have hb' : ∀ (i : Fin (s.m μ)) (c : Fin (s.k μ)), |cellsOf cell μ i c| ≤ 128 := fun i c =>
    (cellsSmall_iff p cell).1 hb μ.val hμ i.val (by rw [← h.m μ.val hμ]; exact i.isLt) c.val
      (by rw [← h.fits.k μ.val hμ]; exact c.isLt)
  have hcard : ((s.m μ * s.tau : ℕ) : ℝ≥0∞) = (Fintype.card (Fin (s.m μ) × Fin s.tau) : ℝ≥0∞) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [hcard]
  refine Prob.pr_exists_le_mul _ _ _ fun y => ?_
  by_cases hk : s.k μ = 0
  · haveI : IsEmpty (Fin (s.k μ)) := by rw [hk]; infer_instance
    refine le_trans (le_of_eq (Prob.pr_eq_zero_of_forall_not_mem _ fun β _ hβ => hβ ?_)) (zero_le _)
    have h0 : Prob.comb (cellsOf cell μ y.1) (β μ y.2) = 0 := by
      unfold Prob.comb
      exact Finset.sum_eq_zero fun c _ => (IsEmpty.false c).elim
    rw [h0]
    exact ⟨by simp, by positivity⟩
  · have hk0 : (0 : ℝ) < (s.k μ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hm1 : (Prob.unif (Dr s)).map (fun Ξ => Ξ μ) =
        Prob.unif (Fin s.tau → Fin (s.k μ) → Prob.Coef) :=
      Prob.map_eval_unif_pi (A := fun ν : Fin s.NM => Fin s.tau → Fin (s.k ν) → Prob.Coef) μ
    have hm2 : (Prob.unif (Fin s.tau → Fin (s.k μ) → Prob.Coef)).map (fun Ξ => Ξ y.2) =
        Prob.unif (Fin (s.k μ) → Prob.Coef) :=
      Prob.map_eval_unif_pi (A := fun _ : Fin s.tau => Fin (s.k μ) → Prob.Coef) y.2
    have hV : ((∑ c, cellsOf cell μ y.1 c ^ 2 : ℤ) : ℝ) ≤ (s.k μ : ℝ) * ((128 : ℤ) : ℝ) ^ 2 := by
      have := Prob.sum_sq_le (cellsOf cell μ y.1) 128 (hb' y.1)
      rwa [Fintype.card_fin] at this
    have key := Prob.pr_window_le (cellsOf cell μ y.1) ((s.k μ : ℝ) * ((128 : ℤ) : ℝ) ^ 2)
      ((2 : ℤ) ^ lbz) (by positivity) (by positivity) hV
    rw [← hm2, Prob.pr_map, ← hm1, Prob.pr_map] at key
    unfold termAt
    rw [if_neg hk]
    exact key

/-- A number that bounds the event "the program finds a combination outside its window" over a
uniform typed matrix bounds it over a uniform written verifier message of a round that draws the
matrix's entries alone, without work, and whose entry in the plan states positions of at most 64
bits. -/
theorem written_of_typed (p : Par) (s : Size) (cell : CellsAt) (d : Run.PQ.RD) (ε : ℝ≥0∞)
    (hd : OnlyTrits d (s.columns * s.tau)) (hw : d.entry.work = 0) (hlog : d.entry.logN ≤ 64)
    (hε : Prob.pr (Prob.unif (Dr s)) {β | (leaves p cell (listOf β)).isSome = true} ≤ ε) :
    Prob.pr (Prob.unif (wRound d).Chal) {c | (leaves p cell (writtenEntries d c)).isSome = true} ≤
      ε := by
  have h1 := (Prob.pr_unif_le_iff (C := Dr s)
    (fun β => (leaves p cell (listOf β)).isSome = true) ε).1 hε
  have hB := below_round_div_ex d hlog _ ε (by rw [card_typed s d hd]; exact h1)
  rw [price_none d hd hw] at hB
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

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.pr_leaves_sum
#print axioms VerifiableInference.Desc.First.K8.Honest.pr_winOf_le
#print axioms VerifiableInference.Desc.First.K8.Honest.written_of_typed
