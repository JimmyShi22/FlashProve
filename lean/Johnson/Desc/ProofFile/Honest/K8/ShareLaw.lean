-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
A measure of the set at which the part's OWN SECOND STOP speaks: no bound on falls. Each of its five
laws on a measure bears a premise on the hidden cells (cellsSmall); the other nine are arithmetic on
written numbers. A caller names the premise on the cells.
Johnson/Desc/ProofFile/Honest/K8/ShareLaw.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: THE
SHARE THAT THE PART STATES FOR ITS SECOND STOP (Honest/K8/Part.lean: `windowShare`) HOLDS, FOR CELLS
THAT PASS `cellsSmall`, OVER UNIFORM WRITTEN VERIFIER MESSAGES OF ONE ROUND. Statements and proofs.
LEMMAS ON ONE STOP OF ONE PART, UNDER A PREMISE ON THE CELLS; NONE OF THE LIBRARY's GOALS, AND NO
STATEMENT OF COMPLETENESS.

  `oddsValue`         a stated share as a number: num / den. MIND den = 0
  `windowShare_den`   the den of the part's stated share is not 0
  `oddsValue_plus`    the sum of two shares has the sum of the two values, if no den is 0
  `le_two_pow_bitsFor`   n is at most 2 ^ bitsFor n
  `bits_le`           ONE MATRIX: (rows of cells) * tau * (one combination's term at its columns) is
                       at most 1 of 2 ^ windowBits, WHERE THE SUBTRACTION IN windowBits DOES NOT CUT
                       OFF. It rests on 1.4426 * log 2 < 1
  `winOf_le_bits`     one matrix: the window event's probability is at most 1 of 2 ^ windowBits:
                       where the subtraction cuts off that is 1 of 1
  `share_holds`       **over a uniform typed matrix the program `leaves` finds a combination outside
                       its window with probability at most the value of `windowShare p`**
  `share_written`     **the same over a uniform written verifier message** of a round that draws the
                       matrix's entries alone, without work
  `stop_written`      **the same of the part's second stop itself**, asked behind its round at the
                       challenge that the message gives
  `stop_at_round`     **the same at the kind's own declared round**: there the cells' test is the
                       one premise that is left
The measure and the limits are those of Johnson/Desc/K8/Honest/WindowLaw.lean: uniform typed
matrices and uniform written messages, never a count of drawn sequences; one round of one request;
that the cells pass `cellsSmall` is a premise, asked at every entry of the shape of every matrix of
the place's list. No statement here has a premise on the rest of the prover.
One round, one place, one fixed front: the sum over the 25 places and over requests is the
spender's. hb (the cells pass cellsSmall) is a premise in all five laws on a measure: nothing here
pays it. A caller is to have it from a law on the real input's trace, and not to lay it as a premise
of its own. Where windowBits' subtraction cuts off, the bound is 1 and says nothing.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.PartLaw
import Johnson.Desc.K8.Honest.WindowLawEach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail OnBytes.Slice Iop
open OnBytes.Model (lbz)
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest
open scoped ENNReal

/-- A stated share as a number. MIND den = 0: there the value is 0 at num = 0 and infinite else, and
`Odds.plus` with a share of den 0 has den 0: so a sum of shares has the sum of the values only where
no den is 0 (`oddsValue_plus`). -/
noncomputable def oddsValue (o : Odds) : ℝ≥0∞ := (o.num : ℝ≥0∞) / (o.den : ℝ≥0∞)

theorem oddsValue_plus (a b : Odds) (ha : a.den ≠ 0) (hb : b.den ≠ 0) :
    oddsValue (a.plus b) = oddsValue a + oddsValue b := by
  have ha' : (a.den : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have hb' : (b.den : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  unfold oddsValue Odds.plus
  push_cast
  rw [ENNReal.add_div, ENNReal.mul_div_mul_right _ _ hb' (ENNReal.natCast_ne_top _),
    mul_comm (b.num : ℝ≥0∞), ENNReal.mul_div_mul_left _ _ ha' (ENNReal.natCast_ne_top _)]

theorem le_two_pow_bitsFor (n : ℕ) : n ≤ 2 ^ bitsFor n := by
  unfold bitsFor
  split
  · next h => simpa using h
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- The format's first number for a matrix of k columns. -/
def bitsTop (k : ℕ) : ℕ := 14426 * (2 ^ lbz) ^ 2 / (10000 * k * 128 ^ 2)

theorem windowBits_eq (m k tau : ℕ) :
    windowBits m k tau = bitsTop k - 1 - bitsFor m - bitsFor tau := rfl

/-- exp (-x) is at most 1 of 2 ^ (the format's first number), x the exponent at k columns. -/
theorem exp_le_bitsTop (k : ℕ) (hk : 0 < k) :
    Real.exp (-((((2 : ℤ) ^ lbz : ℤ) : ℝ) ^ 2 / (k * ((128 : ℤ) : ℝ) ^ 2))) ≤
      ((2 : ℝ) ^ bitsTop k)⁻¹ := by
  have hl : lbz = 17 := rfl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : ((bitsTop k : ℕ) : ℝ) ≤ (14426 * (2 ^ 17) ^ 2 : ℝ) / (10000 * k * 128 ^ 2) := by
    have := Nat.cast_div_le (α := ℝ) (m := 14426 * (2 ^ lbz) ^ 2) (n := 10000 * k * 128 ^ 2)
    rw [hl] at this
    unfold bitsTop
    rw [hl]
    push_cast at this ⊢
    exact le_trans this (le_of_eq (by norm_num))
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : (((2 : ℤ) ^ lbz : ℤ) : ℝ) ^ 2 / (k * ((128 : ℤ) : ℝ) ^ 2) =
      ((2 : ℝ) ^ 17) ^ 2 / (k * 128 ^ 2) := by
    rw [hl]
    norm_num
  have hx : ((bitsTop k : ℕ) : ℝ) * Real.log 2 ≤
      (((2 : ℤ) ^ lbz : ℤ) : ℝ) ^ 2 / (k * ((128 : ℤ) : ℝ) ^ 2) := by
    rw [hcast]
    calc ((bitsTop k : ℕ) : ℝ) * Real.log 2
        ≤ (14426 * (2 ^ 17) ^ 2 : ℝ) / (10000 * k * 128 ^ 2) * 0.6931471808 :=
          mul_le_mul hy hlog.le hlog0.le (by positivity)
      _ ≤ ((2 : ℝ) ^ 17) ^ 2 / (k * 128 ^ 2) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have h2 : ((2 : ℝ) ^ bitsTop k)⁻¹ = Real.exp (-(((bitsTop k : ℕ) : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, mul_comm, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  rw [h2]
  exact Real.exp_le_exp.2 (neg_le_neg hx)

/-- One matrix, where the subtraction in `windowBits` does not cut off. -/
theorem bits_le (m k tau : ℕ) (hy : 1 + bitsFor m + bitsFor tau ≤ bitsTop k) :
    ((m * tau : ℕ) : ℝ) * windowTerm k ≤ ((2 : ℝ) ^ windowBits m k tau)⁻¹ := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp [bitsTop] at hy
    · exact h
  have hm : (m : ℝ) ≤ 2 ^ bitsFor m := by exact_mod_cast le_two_pow_bitsFor m
  have ht : (tau : ℝ) ≤ 2 ^ bitsFor tau := by exact_mod_cast le_two_pow_bitsFor tau
  have he := exp_le_bitsTop k hk
  have hsplit : bitsTop k = windowBits m k tau + (1 + bitsFor m + bitsFor tau) := by
    rw [windowBits_eq]
    omega
  have h2 : (2 : ℝ) ^ bitsTop k =
      2 ^ windowBits m k tau * (2 * 2 ^ bitsFor m * 2 ^ bitsFor tau) := by
    rw [hsplit, pow_add, pow_add, pow_add, pow_one]
  unfold windowTerm
  rw [Nat.cast_mul]
  calc (m : ℝ) * tau * (2 * Real.exp (-((((2 : ℤ) ^ lbz : ℤ) : ℝ) ^ 2 / (k * ((128 : ℤ) : ℝ) ^ 2))))
      ≤ 2 ^ bitsFor m * 2 ^ bitsFor tau * (2 * ((2 : ℝ) ^ bitsTop k)⁻¹) := by
        gcongr
    _ = ((2 : ℝ) ^ windowBits m k tau)⁻¹ := by
        rw [h2]
        field_simp

/-- The value of one matrix's stated share. -/
theorem oddsValue_one (b : ℕ) : oddsValue ⟨1, 2 ^ b⟩ = ((2 : ℝ≥0∞) ^ b)⁻¹ := by
  unfold oddsValue
  push_cast
  rw [one_div]

/-- One matrix: the window event's probability is at most 1 of 2 ^ windowBits. -/
theorem winOf_le_bits (p : Par) (s : Size) (cell : CellsAt) (h : FitsRows p s)
    (hb : cellsSmall p cell = true) (μ : Fin s.NM) :
    Prob.pr (Prob.unif (Dr s)) {β | winOf cell μ β} ≤
      ((2 : ℝ≥0∞) ^ windowBits (s.m μ) (s.k μ) s.tau)⁻¹ := by
  by_cases hy : 1 + bitsFor (s.m μ) + bitsFor s.tau ≤ bitsTop (s.k μ)
  · have hk : s.k μ ≠ 0 := by
      intro h0
      rw [h0] at hy
      simp [bitsTop] at hy
    refine le_trans (pr_winOf_le p s cell h hb μ) ?_
    unfold termAt
    rw [if_neg hk]
    have hr := bits_le (s.m μ) (s.k μ) s.tau hy
    have h0 : (0 : ℝ) ≤ ((s.m μ * s.tau : ℕ) : ℝ) := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul h0]
    refine le_trans (ENNReal.ofReal_le_ofReal hr) (le_of_eq ?_)
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
    norm_num
  · have h0 : windowBits (s.m μ) (s.k μ) s.tau = 0 := by
      rw [windowBits_eq]
      omega
    rw [h0, pow_zero, inv_one]
    exact Prob.pr_le_one _ _

/-- The stated shares of a list of matrices, added up: the sum of their values; and no den is 0. -/
theorem oddsValue_foldl (tau : ℕ) : ∀ (L : List (ℕ × ℕ)) (a : Odds), a.den ≠ 0 →
    (L.foldl (fun s x => s.plus ⟨1, 2 ^ windowBits x.1 x.2 tau⟩) a).den ≠ 0 ∧
    oddsValue (L.foldl (fun s x => s.plus ⟨1, 2 ^ windowBits x.1 x.2 tau⟩) a) =
      oddsValue a + (L.map fun x => ((2 : ℝ≥0∞) ^ windowBits x.1 x.2 tau)⁻¹).sum
  | [], a, ha => ⟨ha, by simp⟩
  | x :: L, a, ha => by
    have hx : (2 ^ windowBits x.1 x.2 tau : ℕ) ≠ 0 := by positivity
    have hden : (a.plus ⟨1, 2 ^ windowBits x.1 x.2 tau⟩).den ≠ 0 := Nat.mul_ne_zero ha hx
    obtain ⟨h1, h2⟩ := oddsValue_foldl tau L _ hden
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, oddsValue_plus a _ ha hx, oddsValue_one, List.map_cons, List.sum_cons,
      add_assoc]

/-- A sum over the numbers below the second list's length against the sum over the two lists laid
side by side. -/
theorem sum_le_zip (R : ℕ → ℕ → ℝ≥0∞) : ∀ (ms ks : List ℕ) (f : ℕ → ℝ≥0∞),
    (∀ μ, μ < ms.length → μ < ks.length → f μ ≤ R (ms.getD μ 0) (ks.getD μ 0)) →
    (∀ μ, ms.length ≤ μ → f μ = 0) →
    ∑ μ ∈ Finset.range ks.length, f μ ≤ ((ms.zip ks).map fun x => R x.1 x.2).sum
  | [], ks, f, _, h0 => by
    rw [Finset.sum_eq_zero fun μ _ => h0 μ (Nat.zero_le _)]
    exact zero_le _
  | _ :: _, [], _, _, _ => by simp
  | m :: ms, k :: ks, f, h1, h0 => by
    rw [List.length_cons, Finset.sum_range_succ', List.zip_cons_cons, List.map_cons, List.sum_cons,
      add_comm]
    refine add_le_add (by simpa using h1 0 (by simp) (by simp)) ?_
    refine sum_le_zip R ms ks (fun μ => f (μ + 1)) (fun μ a b => ?_) fun μ a => ?_
    · simpa using h1 (μ + 1) (by simpa using a) (by simpa using b)
    · exact h0 (μ + 1) (by simpa using a)

/-- The den of the part's stated share is not 0. -/
theorem windowShare_den (p : Par) : (windowShare p).den ≠ 0 :=
  (oddsValue_foldl p.tau (p.ms.zip p.ks) ⟨0, 1⟩ (by norm_num)).1

/-- **For cells that pass `cellsSmall` the stated share holds over a uniform typed matrix.** -/
theorem share_holds (p : Par) (s : Size) (cell : CellsAt) (h : FitsRows p s)
    (hb : cellsSmall p cell = true) :
    Prob.pr (Prob.unif (Dr s)) {β | (leaves p cell (listOf β)).isSome = true} ≤
      oddsValue (windowShare p) := by
  refine le_trans (pr_leaves_sum p s cell h) ?_
  have hval := (oddsValue_foldl p.tau (p.ms.zip p.ks) ⟨0, 1⟩ (by norm_num)).2
  have h01 : oddsValue ⟨0, 1⟩ = 0 := by simp [oddsValue]
  unfold windowShare
  rw [hval, h01, zero_add]
  let f : ℕ → ℝ≥0∞ := fun μ =>
    if hμ : μ < s.NM then Prob.pr (Prob.unif (Dr s)) {β | winOf cell ⟨μ, hμ⟩ β} else 0
  have hsum : ∑ μ : Fin s.NM, Prob.pr (Prob.unif (Dr s)) {β | winOf cell μ β} =
      ∑ μ ∈ Finset.range p.ks.length, f μ := by
    rw [← h.fits.nm, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun μ _ => by simp [f]
  rw [hsum]
  refine sum_le_zip (fun m k => ((2 : ℝ≥0∞) ^ windowBits m k p.tau)⁻¹) p.ms p.ks f
    (fun μ _ hk => ?_) fun μ hm => ?_
  · have hμ : μ < s.NM := h.fits.nm.symm ▸ hk
    have := winOf_le_bits p s cell h hb ⟨μ, hμ⟩
    simp only [f, hμ, dif_pos]
    rw [← h.m μ hk, ← h.fits.k μ hk, ← h.fits.tau]
    exact this
  · by_cases hμ : μ < s.NM
    · have hk : μ < p.ks.length := h.fits.nm ▸ hμ
      have hm0 : s.m μ = 0 := by rw [h.m μ hk, List.getD_eq_default _ _ hm]
      simp only [f, hμ, dif_pos]
      refine le_antisymm (le_trans (pr_winOf_le p s cell h hb ⟨μ, hμ⟩) ?_) (zero_le _)
      simp [hm0]
    · simp [f, hμ]

/-- **For cells that pass `cellsSmall` the stated share holds over a uniform written verifier
message** of a round that draws the matrix's entries alone, without work. -/
theorem share_written (p : Par) (s : Size) (cell : CellsAt) (d : Run.PQ.RD) (h : FitsRows p s)
    (hb : cellsSmall p cell = true) (hd : OnlyTrits d (s.columns * s.tau))
    (hw : d.entry.work = 0) (hlog : d.entry.logN ≤ 64) :
    Prob.pr (Prob.unif (wRound d).Chal) {c | (leaves p cell (writtenEntries d c)).isSome = true} ≤
      oddsValue (windowShare p) :=
  written_of_typed p s cell d _ hd hw hlog (share_holds p s cell h hb)

/-- **The same of the part's second stop itself, for cells that pass `cellsSmall`**: asked behind
its round, at whatever challenges stand in front, at the challenge that the written message gives.
-/
theorem stop_written (p : Par) (s : Size) (v : SmallAsk) (d : Run.PQ.RD) (front : List Fmt.Drawn)
    (h : FitsRows p s) (hb : cellsSmall p v.cell = true) (hd : OnlyTrits d (s.columns * s.tau))
    (hw : d.entry.work = 0) (hlog : d.entry.logN ≤ 64) :
    Prob.pr (Prob.unif (wRound d).Chal)
        {c | (smallHid p v front
          [(Run.ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)]).isSome = true} ≤
      oddsValue (windowShare p) := by
  refine le_trans (le_of_eq ?_) (share_written p s v.cell d h hb hd hw hlog)
  congr 1
  ext c
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, smallHid_isSome]
  constructor
  · rintro ⟨x, hx, hl⟩
    obtain rfl := Option.some.inj hx
    exact hl
  · intro hl
    exact ⟨_, rfl, hl⟩

/-- **At the kind's own declared round**, as the written round of the library's maps: that the cells
pass `cellsSmall` is the one premise left. -/
theorem stop_at_round (p : Par) (v : SmallAsk) (front : List Fmt.Drawn)
    (hb : cellsSmall p v.cell = true) :
    Prob.pr (Prob.unif (wRound (VerifiableInference.Desc.First.K8.rd p)).Chal)
        {c | (smallHid p v front
          [(Run.ckP .two).dr (VerifiableInference.Desc.First.K8.rd p).entry
            (VerifiableInference.Desc.First.K8.rd p).kind
            (GChal.old (b := (VerifiableInference.Desc.First.K8.rd p).entry.work) c)]).isSome =
              true} ≤
      oddsValue (windowShare p) :=
  stop_written p (sizeOfPar p) v (VerifiableInference.Desc.First.K8.rd p) front
    (fitsRows_sizeOfPar p) hb
    (VerifiableInference.Desc.First.K8.onlyTrits (fitsRows_sizeOfPar p).fits) rfl
    (Nat.zero_le _)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.oddsValue_plus
#print axioms ProofFile.Honest.K8.oddsValue_foldl
#print axioms ProofFile.Honest.K8.windowShare_den
#print axioms ProofFile.Honest.K8.bits_le
#print axioms ProofFile.Honest.K8.winOf_le_bits
#print axioms ProofFile.Honest.K8.stop_at_round
#print axioms ProofFile.Honest.K8.share_holds
#print axioms ProofFile.Honest.K8.share_written
#print axioms ProofFile.Honest.K8.stop_written
#print axioms ProofFile.Honest.K8.oddsValue
#print axioms ProofFile.Honest.K8.le_two_pow_bitsFor
#print axioms ProofFile.Honest.K8.bitsTop
#print axioms ProofFile.Honest.K8.windowBits_eq
#print axioms ProofFile.Honest.K8.exp_le_bitsTop
#print axioms ProofFile.Honest.K8.oddsValue_one
#print axioms ProofFile.Honest.K8.sum_le_zip
