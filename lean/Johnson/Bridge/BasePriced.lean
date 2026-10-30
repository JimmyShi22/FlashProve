-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/BasePriced.lean: the two error counts of a base case, at a last stage in numbers
(`LastPlace`, Johnson/Bridge/BaseCodesAt.lean), are at most 2^-128 of their written rounds' verifier
messages: from a test on natural numbers, without the planner.

The file imports Johnson/Bridge/BaseCodesAt.lean, which rests on files adapted from
ArkLib and Mathlib (lean/LIMITS.md,
L15). The statements of this file are arithmetic and use nothing of these.
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

OnBytes/Slice/HeldRound.lean goes from the planner's yes on a round to the clause `RoundBelow`
(OnBytes/Slice/ManyErr.lean). Here the same clause is had from one comparison of natural numbers.
Definitions, statements and proofs.

Main names:
  `below_of_rat`, `below_of_num`: in a written round with N typed values that draws D elements, Z of
    them other than 0, with W bits of work: if count · 2^193 + 3 (D + Z) N ≤ N · 2^(W + 65), then
    the count, times the sampler's number, is at most 2^-128 of the round's written verifier
    messages. The second term pays for the sampler's bias. Asked besides: the entry's logN is at
    most 64, Z ≤ D, and W ≤ 62 in a round that draws elements.
  `LastPlace.priced`: that comparison at the two rounds of a base case.
  `LastPlace.below_lambda`, `LastPlace.below_base`: so the clause holds of both counts.
  `LastPlace.below_rLambda`, `LastPlace.below_rBase`: the same at written rounds that are the
    format's own «BASE lambda» and «BASE» (`Fmt.M1.rLambda`, `Fmt.M1.rBase`).

Limits: of the 128 bits of the second round, `work` are proof of work: a share is a count among all
strings of hash blocks and test bits; nothing on what that is worth against a prover who tries many
times. That a count bounds a prover's chance is not said here (OnBytes/Slice/Base.lean). That the
planner's own price of a round is at least this count is not said. Nothing on a plan or a file.

-/
import Johnson.Bridge.BaseCodesAt
import OnBytes.Slice.HeldRound
import OnBytes.Slice.ManyErr
import OnBytes.Slice.RatesTail
import OnBytes.Slice.HeldCounts
import OnBytes.Slice.RoundsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb Iop Prob _root_.Run
open scoped ENNReal

/-- Arithmetic, at letters. -/
theorem num_aux (c N K P B : ℚ) (hN : 0 < N) (hP : 0 < P) (h : c * P + 3 * K * N ≤ N * B) :
    c / N + 3 * P⁻¹ * K ≤ B * P⁻¹ := by
  have hNP : 0 < N * P := mul_pos hN hP
  have h1 : c / N + 3 * P⁻¹ * K = (c * P + 3 * K * N) / (N * P) := by
    field_simp
  have h2 : B * P⁻¹ = (N * B) / (N * P) := by
    field_simp
  rw [h1, h2]
  exact div_le_div_of_nonneg_right h hNP.le

/-- Powers of two, at letters: A = 2^65, Q = 2^128. -/
theorem pow_aux (A Q C : ℚ) (hA : A ≠ 0) (hQ : Q ≠ 0) : C / Q = C * A * (A * Q)⁻¹ := by
  field_simp

/-- The comparison of natural numbers, read in the rational numbers in the form that
`OnBytes.Slice.held_num` asks. -/
theorem rat_aux (count N D Z W : ℕ) (hN0 : 0 < N)
    (h : count * 2 ^ 193 + 3 * (D + Z) * N ≤ N * 2 ^ (W + 65)) :
    (count : ℚ) / N + (if D = 0 then 0 else (3 * (2 : ℚ) ^ (-193 : ℤ)) * ((D + Z : ℕ) : ℚ)) ≤
      (2 : ℚ) ^ ((W : ℤ) - ((128 : ℕ) : ℤ)) := by
  have hNq : (0 : ℚ) < N := Nat.cast_pos.2 hN0
  have hq : (count : ℚ) * (2 : ℚ) ^ 193 + 3 * ((D + Z : ℕ) : ℚ) * N ≤ N * (2 : ℚ) ^ (W + 65) := by
    have h' := (Nat.cast_le (α := ℚ)).2 h
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h'
  clear h
  have hP : (0 : ℚ) < (2 : ℚ) ^ 193 := pow_pos (by norm_num) _
  have hu : (2 : ℚ) ^ (-193 : ℤ) = ((2 : ℚ) ^ 193)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  have hs : (2 : ℚ) ^ ((W : ℤ) - ((128 : ℕ) : ℤ)) = (2 : ℚ) ^ (W + 65) * ((2 : ℚ) ^ 193)⁻¹ := by
    have e1 : (2 : ℚ) ^ 193 = (2 : ℚ) ^ 65 * (2 : ℚ) ^ 128 := by norm_num
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_natCast, pow_add, e1]
    exact pow_aux _ _ _ (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  have hX := num_aux (count : ℚ) N ((D + Z : ℕ) : ℚ) ((2 : ℚ) ^ 193) ((2 : ℚ) ^ (W + 65)) hNq hP hq
  rw [hs, hu]
  refine le_trans (add_le_add le_rfl ?_) hX
  have hK : (0 : ℚ) ≤ 3 * ((2 : ℚ) ^ 193)⁻¹ * ((D + Z : ℕ) : ℚ) :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hP.le)) (Nat.cast_nonneg _)
  split
  · exact hK
  · exact le_rfl

/-- The clause on a round's count, from a rational number c: the count is at most c times the number
of the round's typed values, and c, with 3 · 2^-193 for each drawn element (twice for one other than
0), is at most 2^(work - 128). The proof is that of `OnBytes.Slice.held_round`, with c in the place
of the planner's number. -/
theorem below_of_rat (d : PQ.RD) (hlog : d.entry.logN ≤ 64)
    (hnz : d.entry.drawNZ ≤ d.entry.drawE)
    (hw : d.entry.drawE ≠ 0 → d.entry.work + 66 ≤ 128) (count : ℕ) (c : ℚ) (hc0 : 0 ≤ c)
    (hcQ : (count : ℚ) ≤ c * (nVals (Fmt.dsOf d.entry d.kind) : ℚ))
    (H : c + (if d.entry.drawE = 0 then 0 else (3 * (2 : ℚ) ^ (-193 : ℤ)) *
      ((d.entry.drawE + d.entry.drawNZ : ℕ) : ℚ)) ≤
      (2 : ℚ) ^ ((d.entry.work : ℤ) - ((128 : ℕ) : ℤ))) :
    RoundBelow count d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hnum := held_num c (3 * (2 : ℚ) ^ (-193 : ℤ)) d.entry.drawE d.entry.drawNZ d.entry.work 128
    hc0 le_rfl hw H
  have hnumR : (((1 + (2 : ℚ) ^ (-128 : ℤ) : ℚ)) : ℝ) ^ (3 * d.entry.drawE) *
      ((c : ℝ) / 2 ^ d.entry.work) ≤ (2⁻¹ : ℝ) ^ 128 := by
    have h := (Rat.cast_le (K := ℝ)).2 hnum
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_inv, Rat.cast_ofNat] using h
  have hc0R : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc0
  have hcR : (count : ℝ) ≤ (c : ℝ) * (nVals (Fmt.dsOf d.entry d.kind) : ℝ) := by
    exact_mod_cast hcQ
  have hcount : (count : ℝ≥0∞) ≤ ENNReal.ofReal (c : ℝ) *
      (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) := by
    rw [card_vals_all, ← ENNReal.ofReal_natCast (nVals _), ← ENNReal.ofReal_mul hc0R,
      ← ENNReal.ofReal_natCast count]
    exact ENNReal.ofReal_le_ofReal hcR
  show ((count * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
    (2 : ℝ≥0∞)⁻¹ ^ 128 * (Fintype.card (wRound d).Chal : ℝ≥0∞)
  refine (below_round_div_ex d hlog count _ hcount).trans (mul_le_mul' ?_ le_rfl)
  rw [exAll_dsOf, Nat.sub_add_cancel hnz, kapSl_ofReal]
  have h2 : (2 : ℝ≥0∞) ^ d.entry.work = ENNReal.ofReal ((2 : ℝ) ^ d.entry.work) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have h3 : (2 : ℝ≥0∞)⁻¹ ^ 128 = ENNReal.ofReal ((2⁻¹ : ℝ) ^ 128) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [h2, h3, ← ENNReal.ofReal_div_of_pos (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hnumR

/-- **The clause on a round's count, from one comparison of natural numbers.** -/
theorem below_of_num (d : PQ.RD) (hlog : d.entry.logN ≤ 64)
    (hnz : d.entry.drawNZ ≤ d.entry.drawE)
    (hw : d.entry.drawE ≠ 0 → d.entry.work + 66 ≤ 128) (count N : ℕ)
    (hN : nVals (Fmt.dsOf d.entry d.kind) = N) (hN0 : 0 < N)
    (h : count * 2 ^ 193 + 3 * (d.entry.drawE + d.entry.drawNZ) * N ≤
      N * 2 ^ (d.entry.work + 65)) :
    RoundBelow count d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  refine below_of_rat d hlog hnz hw count ((count : ℚ) / N)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_
    (rat_aux count N d.entry.drawE d.entry.drawNZ d.entry.work hN0 h)
  rw [hN, div_mul_cancel₀ _ hNq]

namespace LastPlace
variable (x : LastPlace)

/-- The comparison of `below_of_num` at the two rounds of a base case: the first draws one element,
without work; the second draws t positions, with the place's bits of work. -/
def priced : Bool :=
  decide ((x.exc + x.lst) * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65)) &&
    decide ((2 ^ x.s.C.a - x.e - 1) ^ x.s.t * 2 ^ 193 + 3 * (0 + 0) * (2 ^ x.s.C.a) ^ x.s.t ≤
      (2 ^ x.s.C.a) ^ x.s.t * 2 ^ (x.work + 65))

variable {x}

theorem priced_lambda (h : x.priced = true) :
    (x.exc + x.lst) * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65) := by
  unfold priced at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 h).1

theorem priced_base (h : x.priced = true) :
    (2 ^ x.s.C.a - x.e - 1) ^ x.s.t * 2 ^ 193 + 3 * (0 + 0) * (2 ^ x.s.C.a) ^ x.s.t ≤
      (2 ^ x.s.C.a) ^ x.s.t * 2 ^ (x.work + 65) := by
  unfold priced at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 h).2

/-- A round that draws one element, without work. At letters: q in the place of the field's size. -/
theorem below_one (count q : ℕ) (hq0 : 0 < q)
    (h : count * 2 ^ 193 + 3 * (1 + 0) * q ≤ q * 2 ^ (0 + 65)) (d : PQ.RD)
    (hlog : d.entry.logN ≤ 64) (hE : d.entry.drawE = 1) (hZ : d.entry.drawNZ = 0)
    (hW : d.entry.work = 0) (hN : nVals (Fmt.dsOf d.entry d.kind) = q) :
    RoundBelow count d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  refine below_of_num d hlog (by rw [hE, hZ]; exact Nat.zero_le _) (fun _ => by rw [hW]; decide)
    _ _ hN hq0 ?_
  simp only [hE, hZ, hW]
  exact h

/-- A round that draws positions alone. At letters: N in the place of the number of lists. -/
theorem below_pos (count N W : ℕ) (hN0 : 0 < N)
    (h : count * 2 ^ 193 + 3 * (0 + 0) * N ≤ N * 2 ^ (W + 65)) (d : PQ.RD)
    (hlog : d.entry.logN ≤ 64) (hE : d.entry.drawE = 0) (hZ : d.entry.drawNZ = 0)
    (hW : d.entry.work = W) (hN : nVals (Fmt.dsOf d.entry d.kind) = N) :
    RoundBelow count d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  refine below_of_num d hlog (by rw [hE, hZ]) (fun h0 => absurd hE h0) _ _ hN hN0 ?_
  simp only [hE, hZ, hW]
  exact h

/-- **The first round's count**: the exceptional points of a line and the list of pairs. -/
theorem below_lambda (h : x.priced = true) (d : PQ.RD) (hlog : d.entry.logN ≤ 64)
    (hE : d.entry.drawE = 1) (hZ : d.entry.drawNZ = 0) (hW : d.entry.work = 0)
    (hN : nVals (Fmt.dsOf d.entry d.kind) = Fintype.card GE) :
    RoundBelow (x.exc + x.lst) d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_one _ (Cb.Gl.p ^ 3) (Cb.Gl.gl_card.2.1 ▸ card_GE_pos) (priced_lambda h) d hlog hE hZ hW
    (hN.trans Cb.Gl.gl_card.2.1)

/-- **The second round's count**: the lists of positions that miss every place where two words
differ. -/
theorem below_base (h : x.priced = true) (d : PQ.RD) (hlog : d.entry.logN ≤ 64)
    (hE : d.entry.drawE = 0) (hZ : d.entry.drawNZ = 0) (hW : d.entry.work = x.work)
    (hN : nVals (Fmt.dsOf d.entry d.kind) = (2 ^ x.s.C.a) ^ x.s.t) :
    RoundBelow ((2 ^ x.s.C.a - x.e - 1) ^ x.s.t) d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  below_pos _ _ x.work (pow_pos (Nat.two_pow_pos _) _) (priced_base h) d hlog hE hZ hW hN

/-! ### At the format's own two rounds -/

/-- The first count, at a written round that is the format's «BASE lambda». -/
theorem below_rLambda (h : x.priced = true) {d : PQ.RD} (hd : IsRd d Fmt.M1.rLambda) :
    RoundBelow (x.exc + x.lst) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hds : Fmt.dsOf Fmt.M1.rLambda.entry Fmt.M1.rLambda.kind = [.elem, .trits 0] := by decide
  exact below_lambda h d ((congrArg Fmt.Entry.logN hd.entry).le.trans (Nat.zero_le 64))
    (congrArg Fmt.Entry.drawE hd.entry) (congrArg Fmt.Entry.drawNZ hd.entry)
    (congrArg Fmt.Entry.work hd.entry) (by rw [hd.dsOf, hds]; exact nVals_elem)

/-- The second count, at a written round that is the format's «BASE» at the place's stage and bits
of work. -/
theorem below_rBase (h : x.priced = true) (ha : x.s.C.a ≤ 64) {d : PQ.RD} {tree : ℕ}
    (hd : IsRd d (Fmt.M1.rBase x.work x.s.st tree)) :
    RoundBelow ((2 ^ x.s.C.a - x.e - 1) ^ x.s.t) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hE : d.entry.drawE = 0 := congrArg Fmt.Entry.drawE hd.entry
  have hZ : d.entry.drawNZ = 0 := congrArg Fmt.Entry.drawNZ hd.entry
  have hT : d.entry.trits = 0 := congrArg Fmt.Entry.trits hd.entry
  have hL : d.entry.logN = x.s.C.a := congrArg Fmt.Entry.logN hd.entry
  have hP : d.entry.poss = x.s.t := congrArg Fmt.Entry.poss hd.entry
  have hk : d.kind = .positions := hd.kind
  refine below_base h d (hL.le.trans ha) hE hZ (congrArg Fmt.Entry.work hd.entry) ?_
  rw [nVals_positions hE hZ hT (by rw [hk]; decide) (by rw [hk]; decide), hL, hP]

end LastPlace

end Johnson.Bridge

#print axioms Johnson.Bridge.below_of_num
#print axioms Johnson.Bridge.LastPlace.below_lambda
#print axioms Johnson.Bridge.LastPlace.below_base
#print axioms Johnson.Bridge.LastPlace.below_rLambda
#print axioms Johnson.Bridge.LastPlace.below_rBase
