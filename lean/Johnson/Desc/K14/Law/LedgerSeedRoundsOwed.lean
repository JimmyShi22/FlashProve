-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSeedRoundsOwed.lean: ONE STATEMENT THAT IS OWED FOR K14's LAW, AS A
PROPOSITION BY def: NO PROOF HERE. The laws of the shared chain's two sendings (blocks 2 and 5 of
the kind's eight) ask of the first written round of the sending's piece that its entry is K1's entry
of the round of the seeds at the sending's parameters, and that its kind is "seeds". The maker's
pieces bear written rounds that go along the block's declared rounds (RoundIs, Along:
Johnson/Desc/Sound/Stretch.lean). OWED: the two equations at both sendings, and how many trees the
first round sends, from that.

  SeedRoundsOwed   where two written rounds go along b2's | b5's declared rounds: the first one's
                   entry, kind and number of trees
What is not claimed. That it holds.
(It is proved in Johnson/Desc/K14/Law/LedgerSeedRounds.lean: seedRounds.)
Nothing on soundness.

-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.Sound.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (RoundIs Along)
open VerifiableInference.Desc.K1 (seedEntry)

/-- OWED: the first written round of each of the two sendings. -/
def SeedRoundsOwed : Prop :=
  ∀ (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (sentU : Array OracleNotice),
    blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] → withU Q.S = some sentU →
    ∀ (num : Fmt.TreeSource → ℕ) (d₁ d₂ : RDT),
      (Along (RoundIs num) b2.rounds [d₁, d₂] →
        d₁.entry = seedEntry (parK1 Q 2 "o_u and the first mask" sentU) ∧ d₁.kind = .seeds ∧
          d₁.trees.length = (parK1 Q 2 "o_u and the first mask" sentU).trees.length) ∧
      (Along (RoundIs num) b5.rounds [d₁, d₂] →
        d₁.entry = seedEntry (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ∧
          d₁.kind = .seeds ∧
          d₁.trees.length = (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).trees.length)

end Desc.K14.Law
