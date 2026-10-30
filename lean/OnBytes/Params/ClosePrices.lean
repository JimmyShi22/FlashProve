-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/ClosePrices.lean: what the planner's prices of closeness rounds enclose over the real
numbers, and that a closeness term under the rule `johnson` covers the proof library's count over
the number of elements of the field.

The planner prices a closeness round by terms `mcaError s x rows` (OnBytes/Params/Distance.lean):
the count of the code's `Proximity` x, times the rows where the setting has that factor and the
source is not `.third`, over q, the number of elements of the extension field. `mcaShare` is that
expression at a real number cnt for the count, and `mcaError` encloses it where the count encloses
cnt (`enclR_mcaError`); for one row or more it is at least cnt / q (`le_mcaShare`). The error of
round j of a fold is the main code's term, the group's list size times 2 / q, and, while mask rows
are folded, twice the mask code's term: `foldShare`, `enclR_foldRoundError`. The error of the first
round of a test's last step is the main code's term, the list size times 1 / q, and, of a group with
mask rows, the mask code's term: `baseShare`, `enclR_baseError`. These four laws hold at every
analysis and every source. Then, one term at a time: a term covers B / q for every B that is at most
what its count encloses (`mca_covers`). With OnBytes/Params/GroupJohnson.lean and
OnBytes/Params/LibraryJohnson.lean, under their conditions (the source `.johnson`, the count not
marked bad, m as printed, k > 0, a radius e that is at most 1 less the agreement, times the length),
B can be the library's `Cb.bchksBound n k e`: for the main code of a group under the rule `johnson`
(`mca_covers_main`), for its mask code, read as its repetition, with the list size added
(`mca_covers_mask`), and for a table with integers at the one-time test's distance
(`mca_covers_once`).

Main definitions: `mcaShare`, `foldShare`, `baseShare`.
Main theorems: `enclR_mcaError`, `le_mcaShare`, `enclR_fieldError`, `enclR_foldRoundError`,
`enclR_baseError`, `mca_covers`, `mca_covers_main`, `mca_covers_mask`, `mca_covers_once`.
What is not claimed: that any of these numbers bounds a prover's chance in a round. By which
expression a proof bounds the error of a fold's round or of a last step's: no lemma of the library
on these rounds is compared here; the laws say what the planner's prices enclose, and cover the
library's count term by term. What the head of OnBytes/Params/LibraryJohnson.lean does not claim,
above all on the mask code's repetition. Nothing on the group's list size, which is a factor in both
prices (OnBytes/Params/GroupPrices.lean goes on to it). Nothing on the rounds of the test on a table
and of a link (`tableFoldError`), but for the one term in `mca_covers_once`. Nothing on rounds that
draw positions. That rows is 1 or more, and that a price is not marked bad, are hypotheses. For
proofs only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.LibraryJohnson

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- The number that `mcaError` encloses, at a count that encloses cnt. -/
noncomputable def mcaShare (s : Setting) (x : Proximity) (rows : ℕ) (cnt : ℝ) : ℝ :=
  (if (s.rowsFactor && x.source != .third) = true then cnt * (rows : ℝ) else cnt) / (s.cardE : ℝ)

/-- **The closeness error at a count that encloses cnt**, over the real numbers. -/
theorem enclR_mcaError (s : Setting) (x : Proximity) (rows : ℕ) {cnt : ℝ}
    (hx : EnclR x.count cnt) : EnclR (mcaError s x rows) (mcaShare s x rows cnt) := by
  unfold mcaError mcaShare
  dsimp only
  split
  · exact enclR_div (enclR_mul hx (enclR_ofNat rows)) (enclR_ofNat _)
  · exact enclR_div hx (enclR_ofNat _)

/-- For one row or more the number is at least cnt / q, if cnt is not negative. -/
theorem le_mcaShare (s : Setting) (x : Proximity) {rows : ℕ} {cnt : ℝ} (h0 : 0 ≤ cnt)
    (hr : 1 ≤ rows) : cnt / (s.cardE : ℝ) ≤ mcaShare s x rows cnt := by
  unfold mcaShare
  have hq : (0 : ℝ) ≤ (s.cardE : ℝ) := Nat.cast_nonneg _
  have hr' : (1 : ℝ) ≤ (rows : ℝ) := by exact_mod_cast hr
  split
  · exact div_le_div_of_nonneg_right (by nlinarith) hq
  · exact le_rfl

/-- `fieldError` encloses degree / q, over the real numbers. -/
theorem enclR_fieldError (s : Setting) (degree : ℕ) :
    EnclR (fieldError s degree) ((degree : ℝ) / (s.cardE : ℝ)) := enclR_ratio _ _

/-- The number that the error of round j of a fold encloses, at counts that enclose cM and cK. -/
noncomputable def foldShare (s : Setting) (g : GroupSize) (a : Analysis) (j : ℕ) (cM cK : ℝ) : ℝ :=
  mcaShare s a.mainAt (2 ^ (g.k - j) * g.slots) cM +
      (a.list : ℝ) * (((2 : ℕ) : ℝ) / (s.cardE : ℝ)) +
    (if (g.hasMask && decide (j ≤ g.h)) = true then
      ((2 : ℕ) : ℝ) * mcaShare s a.maskAt (2 ^ (g.h - j)) cK else 0)

/-- **The error of round j of a fold**, over the real numbers. -/
theorem enclR_foldRoundError (s : Setting) (g : GroupSize) (a : Analysis) (j : ℕ) {cM cK : ℝ}
    (hM : EnclR a.mainAt.count cM) (hK : EnclR a.maskAt.count cK) :
    EnclR (foldRoundError s g a j) (foldShare s g a j cM cK) := by
  unfold foldRoundError foldShare
  dsimp only
  have h1 := enclR_add (enclR_mcaError s a.mainAt (2 ^ (g.k - j) * g.slots) hM)
    (enclR_mul (enclR_ofNat a.list) (enclR_fieldError s 2))
  split
  · exact enclR_add h1 (enclR_mul (enclR_ofWord 2) (enclR_mcaError s a.maskAt (2 ^ (g.h - j)) hK))
  · rw [add_zero]
    exact h1

/-- The number that the error of the first round of a test's last step encloses. -/
noncomputable def baseShare (s : Setting) (g : GroupSize) (a : Analysis) (cM cK : ℝ) : ℝ :=
  mcaShare s a.mainAt g.slots cM + (a.list : ℝ) * (((1 : ℕ) : ℝ) / (s.cardE : ℝ)) +
    (if g.hasMask = true then mcaShare s a.maskAt 1 cK else 0)

/-- **The error of the first round of a test's last step**, over the real numbers. -/
theorem enclR_baseError (s : Setting) (g : GroupSize) (a : Analysis) {cM cK : ℝ}
    (hM : EnclR a.mainAt.count cM) (hK : EnclR a.maskAt.count cK) :
    EnclR (baseError s g a) (baseShare s g a cM cK) := by
  unfold baseError baseShare
  dsimp only
  have h1 := enclR_add (enclR_mcaError s a.mainAt g.slots hM)
    (enclR_mul (enclR_ofNat a.list) (enclR_fieldError s 1))
  split
  · exact enclR_add h1 (enclR_mcaError s a.maskAt 1 hK)
  · rw [add_zero]
    exact h1

/-- **A closeness term covers a number B over q**, if B is at most what the count encloses, for one
row or more, where the term is not marked bad. -/
theorem mca_covers (s : Setting) (x : Proximity) {rows : ℕ} {cnt B : ℝ} (hx : EnclR x.count cnt)
    (hB : B ≤ cnt) (h0 : 0 ≤ cnt) (hr : 1 ≤ rows) (g : (mcaError s x rows).bad = false) :
    B / (s.cardE : ℝ) ≤ (((mcaError s x rows).error.val : ℚ) : ℝ) :=
  (div_le_div_of_nonneg_right hB (Nat.cast_nonneg _)).trans
    ((le_mcaShare s x h0 hr).trans (le_errorR (enclR_mcaError s x rows hx) g))

/-- **The main code's closeness term in a group under the rule `johnson` covers the library's count
over q.** -/
theorem mca_covers_main {s : Setting} {g : GroupSize} {e rows : ℕ}
    (hs : (analysisOfM s g).mainAt.source = .johnson)
    (hg : (analysisOfM s g).mainAt.count.bad = false) (hp : s.printed = true)
    (hk : 0 < (wordOf g.main).k)
    (he : (e : ℝ) ≤ (1 - groupAgree s g) * ((wordOf g.main).n : ℝ)) (hr : 1 ≤ rows)
    (gm : (mcaError s (analysisOfM s g).mainAt rows).bad = false) :
    Cb.bchksBound (wordOf g.main).n (wordOf g.main).k e / (s.cardE : ℝ) ≤
      (((mcaError s (analysisOfM s g).mainAt rows).error.val : ℚ) : ℝ) := by
  obtain ⟨_, _, h2, h3, h4⟩ := analysisOfM_main hs hg
  exact mca_covers s _ h2 (bchksBound_le_countAt h3 hk (h4 hp) he) (enclR_nonneg h2 hg) hr gm

/-- **The like for the mask code**, as its repetition: the library's count and the mask code's list
size more, over q. -/
theorem mca_covers_mask {s : Setting} {g : GroupSize} {e rows : ℕ} (hh : g.hasMask = true)
    (hs : (analysisOfM s g).maskAt.source = .johnson)
    (hg : (analysisOfM s g).maskAt.count.bad = false) (hp : s.printed = true)
    (hk : 0 < (repeated g.mask g.main.logN).k)
    (he : (e : ℝ) ≤ (1 - groupAgree s g) * ((repeated g.mask g.main.logN).n : ℝ)) (hr : 1 ≤ rows)
    (gm : (mcaError s (analysisOfM s g).maskAt rows).bad = false) :
    (Cb.bchksBound (repeated g.mask g.main.logN).n (repeated g.mask g.main.logN).k e +
        ((analysisOfM s g).maskAt.list : ℝ)) / (s.cardE : ℝ) ≤
      (((mcaError s (analysisOfM s g).maskAt rows).error.val : ℚ) : ℝ) := by
  obtain ⟨_, _, h2, h3, h4⟩ := analysisOfM_mask hh hs hg
  exact mca_covers s _ h2 (add_le_add (bchksBound_le_countAt h3 hk (h4 hp) he) le_rfl)
    (enclR_nonneg h2 hg) hr gm

/-- **The like for a table with integers, at the one-time test's distance.** -/
theorem mca_covers_once {s : Setting} {T : TableSize} {e rows : ℕ} (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) (hg : (tableAnalysis s T).once.count.bad = false)
    (hk : 0 < (wordOf T.code).k)
    (he : (e : ℝ) ≤
      (1 - (wordOf T.code).agreeAt T.distances.mOnce true) * ((wordOf T.code).n : ℝ))
    (hr : 1 ≤ rows) (gm : (mcaError s (tableAnalysis s T).once rows).bad = false) :
    Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e / (s.cardE : ℝ) ≤
      (((mcaError s (tableAnalysis s T).once rows).error.val : ℚ) : ℝ) := by
  have e1 := (tableAnalysis_fromM (s := s) hM).1
  rw [hp] at e1
  rw [e1] at hg gm ⊢
  have h2 := enclR_johnson_count (wordOf T.code) T.distances.mOnce true
  exact mca_covers s _ h2 (bchksBound_le_countAt (johnson_count_good hg).1 hk le_rfl he)
    (enclR_nonneg h2 hg) hr gm

end OnBytes.Params

#print axioms OnBytes.Params.mca_covers
#print axioms OnBytes.Params.mca_covers_main
#print axioms OnBytes.Params.mca_covers_mask
#print axioms OnBytes.Params.mca_covers_once
#print axioms OnBytes.Params.enclR_mcaError
#print axioms OnBytes.Params.le_mcaShare
#print axioms OnBytes.Params.enclR_foldRoundError
#print axioms OnBytes.Params.enclR_baseError
