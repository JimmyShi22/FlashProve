-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleKitBears.lean: WHEN A ROUND's ERROR AT 128 BITS BEARS THE KIT's NUMBER. A
SHEET: two propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

What is said. `KitBears`: at `Run.ckP f`, at a round d whose entry has logN ≤ 64 and whose sampler
reads b blocks with b * 2 ≤ 2 ^ 128: for every number m with m * 2 ^ 129 ≤ p ^ 3 - 1: m * `kitF f d`
* 2 ^ 128 is at most the number of written challenges. READ m AS k * ceil (how many elements the
round draws, times the rule's ceiling): then the number that `ErrBears` asks of the round's error
(Johnson/Desc/Sound/RuleErr.lean) is at most the 2 ^ 128-th part of the written challenges. So at
errors capped there "the errors bear the kit's numbers" is A TEST ON THE PLAN AND THE CEILINGS: k *
ceil * 2 ^ 129 ≤ p ^ 3 - 1. `KitBearsAt`: the same at every number e of binary digits in the place
of 128: m * 2 ^ (e + 1) ≤ p ^ 3 - 1 gives m * `kitF f d` * 2 ^ e at most the number of written
challenges.

On what it rests: `KitShareCard` (Johnson/Desc/Sound/RuleKitMore.lean) and the library's
`Iop.kapSl_pow_le` (Iop/DrawKap.lean): (1 + 2^-128) ^ b ≤ 2.

Limits. (1) One binary digit is given away (2 ^ 129, not 2 ^ 128): the factor 2 stands for the bias
of b blocks. (2) No plan is looked at: the largest k * ceil of the release's plans is told by no
theorem here. (3) Those of RuleKit.lean: above all: nothing is gained from proof of work.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleKitMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open TypedOracleCompiler.Run.PQ (RD)

/-- **The 2 ^ e-th part of the written challenges bears m times the kit's number.** -/
def KitBearsAt : Prop :=
  ∀ (f : Fmt.Fld) (d : RD) (m e : ℕ), d.entry.logN ≤ 64 →
    (_root_.Run.bsRound f d.entry d.kind).b * 2 ≤ 2 ^ 128 →
    m * 2 ^ (e + 1) ≤ f.p ^ 3 - 1 →
    m * kitF f d * 2 ^ e ≤
      Fintype.card (_root_.Iop.GChal d.entry.work ((_root_.Run.ckP f).Ch d.entry d.kind))

/-- The case e = 128. -/
def KitBears : Prop :=
  ∀ (f : Fmt.Fld) (d : RD) (m : ℕ), d.entry.logN ≤ 64 →
    (_root_.Run.bsRound f d.entry d.kind).b * 2 ≤ 2 ^ 128 →
    m * 2 ^ 129 ≤ f.p ^ 3 - 1 →
    m * kitF f d * 2 ^ 128 ≤
      Fintype.card (_root_.Iop.GChal d.entry.work ((_root_.Run.ckP f).Ch d.entry d.kind))


end VerifiableInference.Desc.Sound
