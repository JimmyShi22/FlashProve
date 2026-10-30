-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySNum.lean: the written counts of a stretch are shares of at most 2^-k, from
comparisons of natural numbers, one round at a time.

OnBytes/Flat/CarrySMaps.lean has `Maps.below_err` from `Maps.Held εs`, which speaks of shares as
extended reals. Here the same is had at εs = 2^-k from two comparisons of natural numbers at each
round that is read: the typed count e is a share of at most n / D of the round's typed values, whose
number is `nVals` (OnBytes/Slice/Rates.lean); and n / D, with the sampler's bias (1 + 2^-128 for
each of the round's hash blocks) and the gain from the round's test bits, is at most 2^-k
(`rate_pow`, OnBytes/Slice/RatesNum.lean). At numerals both can be evaluated.

Main names:
  `Maps.HeldN k`: at each step: there are n and D > 0 with e · D ≤ n · nVals and
    (2^128 + 1)^b · n · 2^k ≤ (2^128)^b · D · 2^work.
  `Maps.held_of_nat`: then `Maps.Held (2^-k)`. `Maps.below_pow`: so the written counts are shares of
    at most 2^-k.
  `HeldN.app`, `heldN_skips`.

Limits: no count is shown to be small here. No protocol occurs here.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.CarrySMaps
import OnBytes.Slice.RatesNum

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob Run OnBytes.Maker OnBytes.Slice
open scoped ENNReal

namespace Maps

/-- At each step two comparisons of natural numbers. -/
def HeldN (k : ℕ) : {ds : List RDT} → {s' : Shape} → Maps ds s' → Err s' → Prop
  | _, _, .nil, _ => True
  | _, _, .step (d := d) _ rest, (e, ε) =>
      (∃ n D : ℕ, 0 < D ∧ e * D ≤ n * nVals (Fmt.dsOf d.entry d.kind) ∧
        (2 ^ 128 + 1) ^ (bsRound .two d.entry d.kind).b * n * 2 ^ k ≤
          (2 ^ 128) ^ (bsRound .two d.entry d.kind).b * D * 2 ^ d.entry.work) ∧
      rest.HeldN k ε
  | _, _, .skip _ rest, ε => rest.HeldN k ε

theorem held_of_nat {k : ℕ} : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s') (ε : Err s'),
    M.HeldN k ε → M.Held ((2 : ℝ≥0∞)⁻¹ ^ k) ε
  | _, _, .nil, _, _ => trivial
  | _, _, .step (d := d) _ rest, (e, ε), h => by
      obtain ⟨⟨n, D, hD, h1, h2⟩, h3⟩ := h
      refine ⟨⟨(n : ℝ≥0∞) / (D : ℝ≥0∞), share_le e n D _ hD ?_, rate_pow _ n D _ k hD h2⟩,
        held_of_nat rest ε h3⟩
      rw [card_vals_all]
      exact h1
  | _, _, .skip _ rest, ε, h => held_of_nat rest ε h

/-- The written counts are shares of at most 2^-k. -/
theorem below_pow {k : ℕ} {ds : List RDT} {s' : Shape} (M : Maps ds s') (hM : M.OK) (ε : Err s')
    (h : M.HeldN k ε) : Err.Below (M.err ε) ((2 : ℝ≥0∞)⁻¹ ^ k) :=
  below_err M hM ε (held_of_nat M ε h)

theorem HeldN.app {k : ℕ} : ∀ {ds es : List RDT} {s' t' : Shape} {M : Maps ds s'}
    {N : Maps es t'} {ε : Err s'} {δ : Err t'}, M.HeldN k ε → N.HeldN k δ →
    (M.app N).HeldN k (Err.app ε δ)
  | _, _, _, _, .nil, _, _, _, _, hN => hN
  | _, _, _, _, .step _ rest, _, (_, _), _, hM, hN => ⟨hM.1, HeldN.app (M := rest) hM.2 hN⟩
  | _, _, _, _, .skip _ rest, _, _, _, hM, hN => HeldN.app (M := rest) hM hN

theorem heldN_skips (k : ℕ) : ∀ ds : List RDT, (skips ds).HeldN k ()
  | [] => trivial
  | _ :: ds => heldN_skips k ds

end Maps

end OnBytes.Flat

#print axioms OnBytes.Flat.Maps.held_of_nat
#print axioms OnBytes.Flat.Maps.below_pow
#print axioms OnBytes.Flat.Maps.HeldN.app
#print axioms OnBytes.Flat.Maps.heldN_skips
