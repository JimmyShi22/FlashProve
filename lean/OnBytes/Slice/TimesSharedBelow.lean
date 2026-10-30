-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/TimesSharedBelow.lean: a bound on the error counts of a batch protocol whose shared
rounds' counts are multiplied by the number of slots, from two numbers: one for the local rounds,
one for the shared rounds.

The library's law on a batch's verifier messages holds with the shared rounds' error counts
multiplied by the number N of slots (`Err.timesShared`, Iop/BatchSound.lean), and
OnBytes/Slice/ReplyClause.lean pays that factor. The compiler's conclusion asks one number that is
at least every count as a share of its round's verifier messages (`Err.Below`, Iop/InteractiveOracleProof.lean). This
file gets that number from two: if every local round's count is at most c and every shared round's
at most c' (`BelowBy`; counts as shares of their rounds' verifier messages, here and below), the
multiplied list is below the larger of c and N c'. So a local round does not pay the factor.

Main definition: `BelowBy`.
Main theorems.
 `below_timesShared`   the multiplied list is below max c (N c').
 `belowBy_of_below`    a list that is below c is below c in both kinds of rounds.
 `below_timesShared_one`   with one number c and at least one slot: below N c.
 `batchAt_reply_two`   `batchAt_reply` (OnBytes/Slice/ReplyClause.lean) with the two numbers.

Not claimed. Nothing on which rounds of a written protocol are shared, and no number: c, c' and N
are variables. That a shared round can be had without the factor is not shown. N times a count may
pass the number of the round's verifier messages: then the bound is above 1 and says nothing. With
one number and no slot the bound N c is false of a local round with a count above 0, so
`below_timesShared_one` asks a slot.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.ReplyClause

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch
open scoped ENNReal

/-- Every error count of a local round is, as a share of the round's verifier messages, at most c,
and every error count of a shared round at most c'. -/
def BelowBy : {s : Shape} → RoundSplits s → Err s → ℝ≥0∞ → ℝ≥0∞ → Prop
  | [], _, _, _, _ => True
  | r :: _, (a, A), (e, ε), c, c' =>
    (e : ℝ≥0∞) ≤ (match a.kind with | .lo => c | .sh => c') * (Fintype.card r.Chal : ℝ≥0∞) ∧
      BelowBy A ε c c'

/-- The two-number bound. With the shared rounds' counts multiplied by N, every count is at most
the larger of c and N c'. -/
theorem below_timesShared (N : ℕ) :
    ∀ {s : Shape} (A : RoundSplits s) (ε : Err s) (c c' : ℝ≥0∞), BelowBy A ε c c' →
      Err.Below (Err.timesShared N A ε) (max c ((N : ℝ≥0∞) * c'))
  | [], _, _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), c, c', h => by
      refine ⟨?_, below_timesShared N A ε c c' h.2⟩
      have h1 : (e : ℝ≥0∞) ≤
          (match a.kind with | .lo => c | .sh => c') * (Fintype.card r.Chal : ℝ≥0∞) := h.1
      show (((match a.kind with | .lo => e | .sh => N * e) : ℕ) : ℝ≥0∞) ≤
        max c ((N : ℝ≥0∞) * c') * (Fintype.card r.Chal : ℝ≥0∞)
      revert h1
      cases a.kind with
      | lo =>
        intro h1
        exact h1.trans (mul_le_mul' (le_max_left _ _) le_rfl)
      | sh =>
        intro h1
        calc ((N * e : ℕ) : ℝ≥0∞) = (N : ℝ≥0∞) * (e : ℝ≥0∞) := by push_cast; rfl
          _ ≤ (N : ℝ≥0∞) * (c' * (Fintype.card r.Chal : ℝ≥0∞)) :=
            mul_le_mul' le_rfl h1
          _ = (N : ℝ≥0∞) * c' * (Fintype.card r.Chal : ℝ≥0∞) := (mul_assoc _ _ _).symm
          _ ≤ max c ((N : ℝ≥0∞) * c') * (Fintype.card r.Chal : ℝ≥0∞) :=
            mul_le_mul' (le_max_right _ _) le_rfl

/-- A list that is below c is below c in both kinds of rounds. -/
theorem belowBy_of_below :
    ∀ {s : Shape} (A : RoundSplits s) (ε : Err s) (c : ℝ≥0∞), Err.Below ε c → BelowBy A ε c c
  | [], _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), c, h => by
      refine ⟨?_, belowBy_of_below A ε c h.2⟩
      have h1 : (e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞) := h.1
      cases a.kind <;> exact h1

/-- With one number and at least one slot: the multiplied list is below N c. -/
theorem below_timesShared_one {N : ℕ} (hN : 1 ≤ N) {s : Shape} (A : RoundSplits s) (ε : Err s)
    (c : ℝ≥0∞) (h : Err.Below ε c) : Err.Below (Err.timesShared N A ε) ((N : ℝ≥0∞) * c) := by
  have h2 := below_timesShared N A ε c c (belowBy_of_below A ε c h)
  have hc : c ≤ (N : ℝ≥0∞) * c := by
    calc c = 1 * c := (one_mul c).symm
      _ ≤ (N : ℝ≥0∞) * c := mul_le_mul' (by exact_mod_cast hN) le_rfl
  rwa [max_eq_right hc] at h2

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- `batchAt_reply` with the two numbers: the compiler's conclusion at the larger of c and N c',
if every local round's count is at most c and every shared round's at most c'. -/
theorem batchAt_reply_two {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (c c' : ℝ≥0∞) (ε : Err Z.Q.loc.shape)
    (hlate : L.late = none) (h : ReplyLost Z.Q.loc ε L.early Lg)
    (hb : BelowBy Z.Q.ann ε c c') (hZ : Z.OK) (hN : L.maxBatchSize = 2 ^ W.depthReq) :
    BatchAt Z R Lg (max c ((L.maxBatchSize : ℝ≥0∞) * c')) :=
  batchAt_reply Z R Lg _ ε hlate h (below_timesShared L.maxBatchSize Z.Q.ann ε c c' hb) hZ hN

end OnBytes.Slice
