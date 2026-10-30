-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleKitMore.lean: THREE MORE FACTS ON THE KIT OF HASH BLOCKS, beside
Johnson/Desc/Sound/RuleKit.lean. A SHEET: three propositions written as `def … : Prop`. NOTHING IS
PROVED IN THIS FILE.

What is said. `KitShareCard`: `KitShare` with the number of written challenges as the number of
members of the very type over which `CoordMeasure` counts (`Iop.GChal work ((Run.ckP f).Ch e k)`).
`KapIs`: the factor `Iop.kapSl 128` is 1 + 2^-128. `KitBelow`: EVERY WORD OF EVERY ELEMENT THAT A
ROUND DRAWS AT THIS KIT IS BELOW THE PRIME: for all written challenges, with no premise: it holds by
the type of the draws' values. So a test on the view that asks the canonical writing of DRAWN
elements holds of every transcript at this kit.

Limits. (1) `KitBelow` speaks of what a round draws, NOT of what the prover sends: a sent word at or
above the prime is a member of the transcript's type. (2) Those of RuleKit.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open TypedOracleCompiler.Run.PQ (RD)
open scoped ENNReal

/-- **`KitShare` against the number of written challenges, as a type's number of members.** -/
def KitShareCard : Prop :=
  ∀ (f : Fmt.Fld) (d : RD), d.entry.logN ≤ 64 →
    (kitF f d : ℝ≥0∞) * ((f.p ^ 3 - 1 : ℕ) : ℝ≥0∞) ≤
      _root_.Iop.kapSl 128 ^ (_root_.Run.bsRound f d.entry d.kind).b *
        (Fintype.card (_root_.Iop.GChal d.entry.work
          ((_root_.Run.ckP f).Ch d.entry d.kind)) : ℝ≥0∞)

/-- The factor of one block. -/
def KapIs : Prop := _root_.Iop.kapSl 128 = 1 + ((2 : ℝ≥0∞) ^ 128)⁻¹

/-- **Every drawn word is below the prime.** -/
def KitBelow : Prop :=
  ∀ (f : Fmt.Fld) (d : RD)
    (c : _root_.Iop.GChal d.entry.work ((_root_.Run.ckP f).Ch d.entry d.kind)) (x : Fmt.Ext),
    x ∈ elemsAt (_root_.Run.ckP f) d c →
      x.1.toNat < f.p ∧ x.2.1.toNat < f.p ∧ x.2.2.toNat < f.p


end VerifiableInference.Desc.Sound
