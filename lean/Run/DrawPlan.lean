-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawPlan.lean: the block samplers of a whole protocol by the format's drawing, and, under the
hypotheses below, their bias: 1 + 2^-128 for each block of 256 bits, in both fields.
(Section 6 of the format page, docs/format/FORMAT.md, as Fmt/Rules6.lean renders it; written against
an edition of the page that is not the one that ships.)

This file is about how the verifier messages of all rounds of an interactive protocol are made from
blocks of 256 bits. Definitions, statements (each a `Prop` in `Run.Spec`) and proofs.
A block sampler (`Iop.BS`, Iop/Draw.lean) is a function from b blocks to the values, with a bound
on its fibres. Under its law `BS.Good s κ` one value of a finite type of values takes at most κ
times its even share of all tuples of b blocks: κ bounds the bias.
From Run/DrawPage.lean: `bsOf f ds`, the block sampler of one round from the list ds of its draws,
over the field f, one of the format's two; `Spec.drawPage_bs`, its bias for draws that are `Lawful`
(proved in Run/DrawPageProofs.lean). (`Fmt.Draw`, Fmt/Rules6.lean: one draw of a round, as data:
element, element not 0, position, matrix entries or seal.) From Iop/Draw.lean: `Shape.Draws`, one
block sampler for each round of a shape.
`kapSl 128` (Iop/DrawOf.lean) is 1 + 2^-128.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `PlanFor f s`: for each round of the shape s: the list of its draws, in the order in which the
    protocol names them (R6.2), and a bijection from the values of these draws (`DVal`,
    Run/DrawPage.lean) to the round's own type of verifier messages. A round without a verifier
    message can have the empty list: no block.
  `drawsOf f s P`: the block samplers.
  `PlanFor.Lawful f s P`: every position has at most 64 bits.
  `blocksOf f s P`: the numbers of blocks, round by round: ⌈K / 4⌉, K the most words of the round's
    draws (R6.11).
  `Spec.drawPlan_good`: `PlanFor.Lawful f s P` ⇒ `Shape.Draws.Good (kapSl 128) s (drawsOf f s P)`:
    every round with b blocks obeys the law of a block sampler with (1 + 2^-128)^b.
  `Spec.drawPlan_samplers`: so, under the same hypothesis, for every bound a on the blocks of a
    round and c on the blocks of all rounds: the samplers of Iop/Pull.lean obey their law with
    (1 + 2^-128)^a and (1 + 2^-128)^c: the largest round error grows by at most the first factor,
    the weight of a set of whole verifier randomness by at most the second. The law is
    `Samplers.Good`; this file states the law alone, and what follows from it is stated in
    `LH.Nums.pull` (Iop/Pull.lean) and `Iop.Spec.pullPropsB` (Iop/BatchPull.lean).
  `Spec.drawPlan_blocks`: the blocks of round i, the largest number and the sum are those of
    `blocksOf`.

Nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs. All definitions compute.

Limits: this file says nothing on the least factor (it is smaller in both fields). It says nothing
on the additive form (a statistical distance for each draw).
The bits of a work test and the chain's next value stand in blocks of their own, are exactly
uniform, and are no part of these samplers.
This file does not say which draws a given protocol's rounds have, nor the bijections: the
protocol's data.
What the bijection asks of a protocol: every round's type of verifier messages must be, up to a
bijection, a product of the format's five kinds of values (elements of the extension field, such
elements other than 0, numbers below a power of two, pairs of bits, words); a round whose challenge
set is an abstract type has to be instantiated so before a `PlanFor` exists.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.DrawPageProofs

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

/-- For each round: the list of its draws, and a bijection from their values to the round's verifier
messages. -/
def PlanFor (f : _root_.Fmt.Fld) : Shape → Type
  | [] => Unit
  | r :: s => (Σ ds : List _root_.Fmt.Draw, Vals f ds ≃ r.Chal) × PlanFor f s

/-- The block samplers: for each round `bsOf` of its draws, carried along the bijection. -/
def drawsOf (f : _root_.Fmt.Fld) : (s : Shape) → PlanFor f s → s.Draws 256
  | [], _ => ()
  | _ :: s, (x, P) => ((bsOf f x.1).map x.2, drawsOf f s P)

/-- Every position has at most 64 bits: each draw `Fmt.Draw.pos k` of each round has k ≤ 64. -/
def PlanFor.Lawful (f : _root_.Fmt.Fld) : (s : Shape) → PlanFor f s → Prop
  | [], _ => True
  | _ :: s, (x, P) => (∀ d ∈ x.1, Run.Lawful d) ∧ PlanFor.Lawful f s P

/-- the numbers of blocks, round by round -/
def blocksOf (f : _root_.Fmt.Fld) : (s : Shape) → PlanFor f s → List ℕ
  | [], _ => []
  | _ :: s, (x, P) => _root_.Fmt.blocksFor (_root_.Fmt.mostAll x.1) :: blocksOf f s P

namespace Spec

/-- The bias of a protocol's drawing. -/
def drawPlan_good : Prop :=
  ∀ (f : _root_.Fmt.Fld) (s : Shape) (P : PlanFor f s),
    PlanFor.Lawful f s P → Shape.Draws.Good (kapSl 128) s (drawsOf f s P)

/-- What it does to the bounds: the law `Samplers.Good` (Iop/Pull.lean), with two factors. -/
def drawPlan_samplers : Prop :=
  ∀ (f : _root_.Fmt.Fld) (s : Shape) (P : PlanFor f s), PlanFor.Lawful f s P →
    ∀ a c : ℕ, (∀ b ∈ blocksOf f s P, b ≤ a) → (blocksOf f s P).sum ≤ c →
      (Samplers.ofDraws s (drawsOf f s P)).Good (kapSl 128 ^ a) (kapSl 128 ^ c)

def drawPlan_blocks : Prop :=
  ∀ (f : _root_.Fmt.Fld) (s : Shape) (P : PlanFor f s),
    (∀ i, Shape.Draws.bAt s (drawsOf f s P) i = (blocksOf f s P).getD i 0) ∧
    Shape.Draws.totB s (drawsOf f s P) = (blocksOf f s P).sum ∧
    ∀ a, Shape.Draws.maxB s (drawsOf f s P) ≤ a ↔ ∀ b ∈ blocksOf f s P, b ≤ a

end Spec

theorem drawPlan_good : Spec.drawPlan_good := by
  intro f s
  induction s with
  | nil => exact fun _ _ => trivial
  | cons r s ih =>
    rintro ⟨x, P⟩ ⟨h1, h2⟩
    exact ⟨BS.map_good x.2 (drawPage_bs f x.1 h1).1, ih P h2⟩

theorem drawPlan_blocks : Spec.drawPlan_blocks := by
  intro f s
  induction s with
  | nil =>
    exact fun _ =>
      ⟨fun _ => rfl, rfl,
        fun a => ⟨fun _ b hb => absurd hb List.not_mem_nil, fun _ => Nat.zero_le a⟩⟩
  | cons r s ih =>
    rintro ⟨x, P⟩
    obtain ⟨i1, i2, i3⟩ := ih P
    refine ⟨fun i => ?_, ?_, fun a => ?_⟩
    · cases i with
      | zero => rfl
      | succ i => exact i1 i
    · show _root_.Fmt.blocksFor (_root_.Fmt.mostAll x.1) + Shape.Draws.totB s (drawsOf f s P) =
        (_root_.Fmt.blocksFor (_root_.Fmt.mostAll x.1) :: blocksOf f s P).sum
      rw [i2, List.sum_cons]
    · show max (_root_.Fmt.blocksFor (_root_.Fmt.mostAll x.1))
            (Shape.Draws.maxB s (drawsOf f s P)) ≤ a ↔
        ∀ b ∈ _root_.Fmt.blocksFor (_root_.Fmt.mostAll x.1) :: blocksOf f s P, b ≤ a
      rw [max_le_iff, i3 a, List.forall_mem_cons]

theorem drawPlan_samplers : Spec.drawPlan_samplers := fun f s P h a c ha hc =>
  drawsGood 256 (kapSl 128) (one_le_kapSl 128) s (drawsOf f s P) (drawPlan_good f s P h) a c
    (((drawPlan_blocks f s P).2.2 a).2 ha) (by rw [(drawPlan_blocks f s P).2.1]; exact hc)

end Run
