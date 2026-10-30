-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/BearsBelow.lean: the errors that the rule at the kit asks a piece to bear
(Johnson/Desc/Sound/RuleAtKit.lean: ErrBears C need ds 0 err), laid as a row by a function, and
below 2^-128 a round. The general part: no kind of block is named.

What the file holds.
  errOf C need ds n   the row: need n, need (n + 1), and so on: a function of ds and need.
  errOf_bears      that row bears need.
  bears_mono       a row that is nowhere smaller bears too.
  RoundOk          a number is below a bound's share of one round's written challenges.
  errOf_below      the row is below a bound where each round's number is.
  below_of_nat     x * 2 ^ 128 <= N gives x <= 2^-128 * N in the extended reals.
  blocks_small     a round's sampler reads few blocks: b * 2 <= 2 ^ 128, where logN is at most 64
                   and the entry's three counts of draws are at most 2 ^ 60.
  kit_below        n * kitF .two d is below 2^-128 of d's written challenges, where
                   n * 2 ^ 129 <= p ^ 3 - 1.
Who calls it. Johnson/Desc/Kinds/Law/K06Bears.lean, at C := Run.ckP .two and
need := fun j => kitK ds j * (priceAt p j * kitFs .two ds j).

What it does not give. No rule is named: that a rule's list is no longer than its ceiling is the
caller's. No sum over the rounds. Nothing on soundness. No statement has a "there is".

-/
import Iop.ErrCap
import Johnson.Desc.Sound.RuleAtKit
import Johnson.Desc.Sound.RuleKitBearsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Bears

open VerifiableInference.Desc.Sound (ErrBears kitK kitFs kitF kitBears)
open TypedOracleCompiler.Run.PQ (uL RD)
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open scoped ENNReal

/-- **The row of errors**: need n, need (n + 1), … -/
def errOf (C : CK) (need : ℕ → ℕ) : (ds : List RD) → ℕ → Err (uL C ds)
  | [], _ => ()
  | _ :: ds, n => (need n, errOf C need ds (n + 1))

theorem errOf_bears (C : CK) (need : ℕ → ℕ) :
    ∀ (ds : List RD) (n : ℕ), ErrBears C need ds n (errOf C need ds n)
  | [], _ => trivial
  | _ :: ds, n => ⟨le_refl _, errOf_bears C need ds (n + 1)⟩

/-- **A row that is nowhere smaller bears too.** -/
theorem bears_mono (C : CK) (need : ℕ → ℕ) :
    ∀ (ds : List RD) (n : ℕ) (ε ε' : Err (uL C ds)), Err.le ε ε' → ErrBears C need ds n ε →
      ErrBears C need ds n ε'
  | [], _, _, _, _, _ => trivial
  | _ :: ds, n, (_, ε), (_, ε'), h, hb =>
    ⟨le_trans hb.1 h.1, bears_mono C need ds (n + 1) ε ε' h.2 hb.2⟩

/-- A number is below ε of the round's written challenges. -/
def RoundOk (C : CK) (ε : ℝ≥0∞) (x : ℕ) (d : RD) : Prop :=
  Err.Below (s := uL C [d]) (x, ()) ε

theorem errOf_below (C : CK) (need : ℕ → ℕ) (ε : ℝ≥0∞) :
    ∀ (ds : List RD) (n : ℕ), (∀ i d, ds[i]? = some d → RoundOk C ε (need (n + i)) d) →
      Err.Below (errOf C need ds n) ε
  | [], _, _ => trivial
  | d :: ds, n, h =>
    ⟨(h 0 d rfl).1, errOf_below C need ε ds (n + 1) fun i e he => by
      have := h (i + 1) e he
      rwa [show n + (i + 1) = n + 1 + i by omega] at this⟩

theorem below_of_nat (x N : ℕ) (h : x * 2 ^ 128 ≤ N) :
    (x : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 * (N : ℝ≥0∞) := by
  have h0 : ((2 : ℝ≥0∞) ^ 128) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : ((2 : ℝ≥0∞) ^ 128) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [← ENNReal.inv_pow, mul_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht)]
  exact_mod_cast h

/-- A round's sampler reads few blocks. -/
theorem blocks_small (e : Fmt.Entry) (k : Fmt.Kind) (hlog : e.logN ≤ 64) (hp : e.poss ≤ 2 ^ 60)
    (hE : e.drawE ≤ 2 ^ 60) (hnz : e.drawNZ ≤ e.drawE) (ht : e.trits ≤ 2 ^ 60) :
    (_root_.Run.bsRound .two e k).b * 2 ≤ 2 ^ 128 := by
  rw [(_root_.Run.planDraws_law .two e k hlog).2]
  unfold Fmt.blocksFor Fmt.wordsAtMost
  have a : (2 : ℕ) ^ 60 = 1152921504606846976 := by norm_num
  have b : (2 : ℕ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  rw [a] at hp hE ht
  rw [b]
  split <;> omega

/-- **n * kitF is below 2^-128 of the round's written challenges**: kitBears
(Johnson/Desc/Sound/RuleKitBearsProofs.lean), in the words of Err.Below. -/
theorem kit_below (d : RD) (n : ℕ) (hlog : d.entry.logN ≤ 64)
    (hb : (_root_.Run.bsRound .two d.entry d.kind).b * 2 ≤ 2 ^ 128)
    (hn : n * 2 ^ 129 ≤ Fmt.Fld.two.p ^ 3 - 1) :
    RoundOk (_root_.Run.ckP .two) ((2 : ℝ≥0∞)⁻¹ ^ 128) (n * kitF .two d) d :=
  ⟨below_of_nat _ _ (kitBears .two d n hlog hb hn), trivial⟩

end VerifiableInference.Desc.Kinds.Head.Law.Bears

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Bears.kit_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Bears.blocks_small
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Bears.errOf_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Bears.bears_mono
