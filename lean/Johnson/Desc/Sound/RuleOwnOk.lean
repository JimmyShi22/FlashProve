-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleOwnOk.lean: `OwnOfRule` (Johnson/Desc/Sound/RuleOwn.lean) WITH A PLACE FOR A
TEST ON THE VIEW. A SHEET: one proposition written as `def … : Prop`. NOTHING IS PROVED IN THIS
FILE.

Why. A law over field VALUES is false at a transcript in which an element is written otherwise than
in its one canonical writing (a word at or above the prime). The verifier refuses such a view ONCE,
IN FRONT OF ALL BLOCKS (Johnson/Desc/Block.lean: `viewWordsBelowPrime`, asked of the whole view in `runCore`).
The rule of composition takes its pieces at the blocks `below b` (Johnson/Desc/Sound/ChainRule.lean:
b with that test of its own rounds in front: a device of the proof; `FoldBelow`: their fold is the
fold of the blocks b with `viewWordsBelowPrime` in front): so a law may spend the test. `OwnOfRule` had no place
for it.

What is said. `OwnOfRuleOk`: one letter more, ok : List Fmt.RoundView → Prop, a property of the stretch's
rounds as the written reading shows them. The promise and the law may take `ok` of these rounds as a
premise. THE PRICE, A NEW PREMISE (view): wherever the piece gives a record behind, `ok` holds of
its rounds. At ok := fun _ => True this is `OwnOfRule`.

Limits. (1) (view) IS A PREMISE: shown here for no piece. WHO CAN PAY IT, at ok := "every word of
the stretch's rounds, sent and drawn, is below the prime": A PIECE THAT HOLDS `below b`, as every
piece of a description does (Johnson/Desc/Sound/DescThree.lean: `OfDesc`): there the block's own
step asks it. A piece that holds a bare b cannot: the typed transcript holds raw words, and b's step
tests no sent word against the prime. For the elements that a round DRAWS at the kit of hash blocks
it holds of every transcript (Johnson/Desc/Sound/RuleAtKit.lean: `KitView`). (2) Those of
RuleOwn.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open OnBytes (E)
open TypedOracleCompiler.Run.PQ (uL rvSL RD)
open _root_.Run.PQ (CK SgX PlainOf)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

/-- **`OwnOfRule` where promise and law may spend a test on the view.** -/
def OwnOfRuleOk : Prop :=
  ∀ (S Cl W ι D : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) (comp : W → D)
    (dec : S × F.E.Str → D) (rule : S × F.E.Str → D → List Fmt.RoundView → List E) (ceil k f : ℕ → ℕ)
    (ok : List Fmt.RoundView → Prop),
    (∀ a d g, on a → (rule a d g).length ≤ ceil (g.length - 1)) →
    (∀ j d, (toRDs p.ds)[j]? = some d → CoordMeasure C d (k j) (f j)) →
    ErrBears C (fun j => k j * (ceil j * f j)) (toRDs p.ds) 0 p.err →
    (∀ a τ b w, on a → p.ior.red.out a τ = some b → relAt means Out b w → comp w = dec a) →
    (∀ a τ b, on a → p.ior.red.out a τ = some b → ok (rvSL C (toRDs p.ds) τ)) →
    (∀ a τ b, on a → ok (rvSL C (toRDs p.ds) τ) →
      NoBad (rule a (dec a)) (rvSL C (toRDs p.ds) τ) → p.ior.red.out a τ = some b → on' b) →
    (∀ a τ b w, on a → ok (rvSL C (toRDs p.ds) τ) →
      NoBad (rule a (comp w)) (rvSL C (toRDs p.ds) τ) →
      p.ior.red.out a τ = some b → relAt means Out b w → relAt means In a (p.ext a τ w)) →
    p.Own on on' means In Out


end VerifiableInference.Desc.Sound
