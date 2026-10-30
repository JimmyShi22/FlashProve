-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Bears.lean: written counts that bear given typed errors (the library's
BearsT), written out.

Main names:
  `bearErr`: round by round: the typed count times the sampler's own bound on how many strings of
    hash blocks give one
    value. `bears_self`. `bearErr_list`: the same as a list.
  `HeldTN`, `bear_below`: from two comparisons of natural numbers a round, the written counts are
    shares of at most 2^-k
    of their rounds' challenges, with the sampler's bias and the gain from the test bits counted
      (the library's
    Maps.HeldN and below_pow, for the kit's carry; below_round_div, share_le, rate_pow).
  `Cb.errList`: the errors of a block as a list.

Limits: no count is shown to be small here.
Sources: OnBytes/Tie/Pv/Lookup/Forest/FoPeelKitT.lean; OnBytes/Flat/CarrySNum.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelKitT
import OnBytes.Flat.CarrySNum
import Blocks.MergeStage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop

/-- the errors of a block as a list -/
def errList : {s : Shape} → Err s → List ℕ
  | [], _ => []
  | _ :: _, (e, ε) => e :: errList ε

end Cb

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open scoped ENNReal

/-- The written counts. Where there are more written rounds than typed ones the count 0 is laid: it
is a filler (HeldTN and
BearsT say nothing there), not «no error»; behind own_meets the lengths agree. -/
def bearErr : (ds : List RDT) → (s' : Shape) → Err s' → Err (uLT (ckP .two) ds)
  | [], _, _ => ()
  | d :: ds, _ :: s', ε => (ε.1 * (bsRound .two d.entry d.kind).w, bearErr ds s' ε.2)
  | _ :: ds, [], _ => (0, bearErr ds [] ())

theorem bears_self : ∀ (ds : List RDT) (s' : Shape) (ε : Err s'), BearsT ds s' ε (bearErr ds s' ε)
  | [], [], _ => trivial
  | [], _ :: _, _ => trivial
  | _ :: _, [], _ => trivial
  | _ :: ds, _ :: s', ε => ⟨le_rfl, bears_self ds s' ε.2⟩

theorem bearErr_list : ∀ (ds : List RDT) (s' : Shape) (ε : Err s'), ds.length = s'.length →
    errList (bearErr ds s' ε) =
      List.zipWith (· * ·) (errList ε) (ds.map fun d => (bsRound .two d.entry d.kind).w)
  | [], [], _, _ => rfl
  | d :: ds, _ :: s', ε, h =>
    congrArg (ε.1 * (bsRound .two d.entry d.kind).w :: ·) (bearErr_list ds s' ε.2 (by simpa using h))
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- At each round two comparisons of natural numbers (the library's Maps.HeldN, for the kit's
carry): the typed count e is a
share of at most n / D of the round's typed values; n / D, with the sampler's bias and the gain from
the test bits, is at most
2^-k. -/
def HeldTN (k : ℕ) : (ds : List RDT) → (s' : Shape) → Err s' → Prop
  | [], _, _ => True
  | d :: ds, _ :: s', ε =>
    (d.entry.logN ≤ 64 ∧ ∃ n D : ℕ, 0 < D ∧ ε.1 * D ≤ n * nVals (Fmt.dsOf d.entry d.kind) ∧
      (2 ^ 128 + 1) ^ (bsRound .two d.entry d.kind).b * n * 2 ^ k ≤
        (2 ^ 128) ^ (bsRound .two d.entry d.kind).b * D * 2 ^ d.entry.work) ∧ HeldTN k ds s' ε.2
  | _ :: ds, [], _ => HeldTN k ds [] ()

/-- **Then the written counts are shares of at most 2^-k of their rounds' challenges.** -/
theorem bear_below {k : ℕ} : ∀ (ds : List RDT) (s' : Shape) (ε : Err s'), HeldTN k ds s' ε →
    Err.Below (bearErr ds s' ε) ((2 : ℝ≥0∞)⁻¹ ^ k)
  | [], _, _, _ => trivial
  | d :: ds, _ :: s', ε, ⟨⟨hl, n, D, hD, h1, h2⟩, h3⟩ =>
    ⟨(below_round_div (toRD d) hl ε.1 ((n : ℝ≥0∞) / (D : ℝ≥0∞))
        (share_le ε.1 n D _ hD (by rw [card_vals_all]; exact h1))).trans
      (mul_le_mul' (rate_pow _ n D _ k hD h2) le_rfl), bear_below ds s' ε.2 h3⟩
  | _ :: ds, [], _, h => ⟨by rw [Nat.cast_zero]; exact zero_le _, bear_below ds [] () h⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.bear_below
#print axioms VerifiableInference.Desc.First.Att.P.bears_self
#print axioms VerifiableInference.Desc.First.Att.P.bearErr_list
