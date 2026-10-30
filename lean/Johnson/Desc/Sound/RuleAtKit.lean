-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleAtKit.lean: THE RULE OF BAD ELEMENTS AT THE KIT OF HASH BLOCKS: `OwnOfRule`
(Johnson/Desc/Sound/RuleOwn.lean) with its premise on the measures PAID and with a test on the DRAWN
elements' writing to spend for nothing. A SHEET: three definitions and three propositions written as
`def … : Prop`. NOTHING IS PROVED IN THIS FILE.

What is said. `DrawnBelow f t`: every word of every element that a round of t has drawn is below f's
prime. `KitView`: at `Run.ckP f` that holds of EVERY transcript's rounds as the written reading
shows them: no premise. `KitViewOkE`: the same at the release's field in the words of the field's
own test (`OnBytes.okE`). `OwnOfRuleAtKit`: at a piece over `Run.ckP f`: a rule at the witness's
pinned components, its ceiling, EVERY ROUND's ENTRY WITH logN ≤ 64, errors that bear the kit's own
numbers (`kitK`, `kitFs`: Johnson/Desc/Sound/RuleKit.lean's at the round number j), the pin, the
promise and the law, BOTH OF WHICH MAY SPEND `DrawnBelow`: then the block's own law at the table.
Against `OwnOfRule`: no premise `CoordMeasure`; against `OwnOfRuleOk`
(Johnson/Desc/Sound/RuleOwnOk.lean): no premise (view).

Limits. (1) THE DRAWN ALONE: of what the prover SENDS `DrawnBelow` says nothing. A law that needs
the canonical writing of sent values goes by `OwnOfRuleOk`, whose premise (view) a piece that holds
`below b` (Johnson/Desc/Sound/ChainRule.lean) can pay: that gives more than `DrawnBelow`.
(2) logN ≤ 64 is a test on the plan's entries.
(3) Those of RuleOwn.lean and RuleKit.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleOwnOk
import Johnson.Desc.Sound.RuleKit
import OnBytes.Field.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open OnBytes (E)
open TypedOracleCompiler.Run.PQ (uL rvSL RD)
open _root_.Run.PQ (CK SgX PlainOf)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

/-- Every word of every element that a round of t has drawn is below f's prime. -/
def DrawnBelow (f : Fmt.Fld) (t : List Fmt.RoundView) : Prop :=
  ∀ r, r ∈ t → ∀ x, x ∈ r.drawn.elems →
    x.1.toNat < f.p ∧ x.2.1.toNat < f.p ∧ x.2.2.toNat < f.p

/-- How many elements the round number j draws; 0 where there is no such round. -/
def kitK (ds : List RD) (j : ℕ) : ℕ :=
  match ds[j]? with
  | some d => nElems (Fmt.dsOf d.entry d.kind)
  | none => 0

/-- `kitF` at the round number j; 0 where there is no such round. -/
def kitFs (f : Fmt.Fld) (ds : List RD) (j : ℕ) : ℕ :=
  match ds[j]? with
  | some d => kitF f d
  | none => 0

/-- **At the kit of hash blocks every drawn word is below the prime**, at every transcript. -/
def KitView : Prop :=
  ∀ (f : Fmt.Fld) (ds : List RD) (τ : Iop.Tr (uL (_root_.Run.ckP f) ds)),
    DrawnBelow f (rvSL (_root_.Run.ckP f) ds τ)

/-- The same at the release's field, in the words of the field's own test. -/
def KitViewOkE : Prop :=
  ∀ (ds : List RD) (τ : Iop.Tr (uL (_root_.Run.ckP .two) ds)) (r : Fmt.RoundView),
    r ∈ rvSL (_root_.Run.ckP .two) ds τ → ∀ x, x ∈ r.drawn.elems → OnBytes.okE (E.ofTriple x) = true

/-- **The rule at the kit**: no premise on the measures, none on the view. -/
def OwnOfRuleAtKit : Prop :=
  ∀ (S Cl W ι D : Type) (fld : Fmt.Fld) (F : Frame) (p : Piece (_root_.Run.ckP fld) F S Cl W)
    (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) (comp : W → D)
    (dec : S × F.E.Str → D) (rule : S × F.E.Str → D → List Fmt.RoundView → List E) (ceil : ℕ → ℕ),
    (∀ a d g, on a → (rule a d g).length ≤ ceil (g.length - 1)) →
    (∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64) →
    ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j * (ceil j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err →
    (∀ a τ b w, on a → p.ior.red.out a τ = some b → relAt means Out b w → comp w = dec a) →
    (∀ a τ b, on a → DrawnBelow fld (rvSL (_root_.Run.ckP fld) (toRDs p.ds) τ) →
      NoBad (rule a (dec a)) (rvSL (_root_.Run.ckP fld) (toRDs p.ds) τ) →
      p.ior.red.out a τ = some b → on' b) →
    (∀ a τ b w, on a → DrawnBelow fld (rvSL (_root_.Run.ckP fld) (toRDs p.ds) τ) →
      NoBad (rule a (comp w)) (rvSL (_root_.Run.ckP fld) (toRDs p.ds) τ) →
      p.ior.red.out a τ = some b → relAt means Out b w → relAt means In a (p.ext a τ w)) →
    p.Own on on' means In Out


end VerifiableInference.Desc.Sound
