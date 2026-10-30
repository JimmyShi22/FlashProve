-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleKit.lean: THE MEASURE OF A ROUND's DRAW AT THE KIT OF HASH BLOCKS: the row
"`CoordMeasure` at the kit of the release" (Johnson/Desc/Sound/RuleErr.lean, Limits (1)). A SHEET:
four definitions and two propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

The kit. `Run.ckP f` (Run/PlanPull.lean): a round's challenge is a string of b hash blocks of 256
bits; what the round draws is the format's own function of these blocks (`Run.planDraws_tie`,
Run/PlanDraws.lean: `Fmt.drawRound` on the words read off the blocks' bytes). A WRITTEN challenge is
such a string with the round's proof-of-work bits (`Iop.GChal`).

What is said. `KitMeasure`: at every field f and every round d whose entry has logN ≤ 64,
`CoordMeasure (Run.ckP f) d k F` holds at k := `nElems`, the number of elements among the round's
draws, and F := `kitF f d` = 2 ^ work * (w * `others`): w: the bound on the fibres of the round's
block sampler (`Run.bsRound`); `others`: the largest number of values that all of the round's draws
but one element can take together. `KitShare`: WHAT THAT NUMBER IS WORTH: F * (p ^ 3 - 1) is at most
(1 + 2^-128) ^ b times the number of written challenges (Johnson/Desc/Sound/RuleKitMore.lean:
`KapIs`: the factor; `KitShareCard`: that number as the type's number of members): so a rule with a
ceiling of n elements is met at one place of the draw by at most the share n / (p ^ 3 - 1) of the
written challenges, times that factor.

On what it rests: the library's `Run.planDraws_law` (the sampler's fibres and their ratio), called,
not typed anew; the count over the values of the draws is by induction on the list of draws.

Limits. (1) ELEMENTS ALONE, as in RuleErr.lean. (2) NOTHING IS GAINED FROM PROOF OF WORK HERE: all
values of the proof-of-work bits are counted, so the share is that of the field; what grinding costs
or gains is the law of the reading of the whole file. (3) logN ≤ 64 is a premise on the entry: a
test on the plan. (4) p ^ 3 - 1, not p ^ 3: an
element that must not be 0 has one value fewer; one number serves both sorts. (5) That the programs'
drawing is `Fmt.drawRound` is no matter of this file. (6) Nothing on soundness of any verifier: a
count.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleErr
import Run.PlanPull

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes (E)
open TypedOracleCompiler.Run.PQ (RD)
open _root_.Run.PQ (CK)
open _root_.Prob (cnt)
open scoped ENNReal

/-- Does the draw give an element of the field? -/
def isElem : Fmt.Draw → Bool
  | .elem => true
  | .elemNZ => true
  | _ => false

/-- How many elements a list of draws gives. -/
def nElems : List Fmt.Draw → ℕ
  | [] => 0
  | d :: ds => (if isElem d then 1 else 0) + nElems ds

/-- The largest number of values that all draws of the list but one element take together; 0 where
the list has no element. -/
def others (f : Fmt.Fld) : List Fmt.Draw → ℕ
  | [] => 0
  | d :: ds =>
    if isElem d then
      max (Nat.card (_root_.Run.Vals f ds)) (Nat.card (_root_.Run.DVal f d) * others f ds)
    else Nat.card (_root_.Run.DVal f d) * others f ds

/-- The round's second number: how many written challenges draw a given element at a given place, at
most. -/
def kitF (f : Fmt.Fld) (d : RD) : ℕ :=
  2 ^ d.entry.work *
    ((_root_.Run.bsRound f d.entry d.kind).w * others f (Fmt.dsOf d.entry d.kind))

/-- **The measure of a round's draw at the kit of hash blocks.** -/
def KitMeasure : Prop :=
  ∀ (f : Fmt.Fld) (d : RD), d.entry.logN ≤ 64 →
    CoordMeasure (_root_.Run.ckP f) d (nElems (Fmt.dsOf d.entry d.kind)) (kitF f d)

/-- **What the number is worth**: against the number of written challenges, 2 ^ work times the
number of strings of b blocks. -/
def KitShare : Prop :=
  ∀ (f : Fmt.Fld) (d : RD), d.entry.logN ≤ 64 →
    (kitF f d : ℝ≥0∞) * ((f.p ^ 3 - 1 : ℕ) : ℝ≥0∞) ≤
      _root_.Iop.kapSl 128 ^ (_root_.Run.bsRound f d.entry d.kind).b *
        ((2 ^ d.entry.work *
          Fintype.card (Fin (_root_.Run.bsRound f d.entry d.kind).b → _root_.Iop.Dig 256) : ℕ) :
            ℝ≥0∞)


end VerifiableInference.Desc.Sound
