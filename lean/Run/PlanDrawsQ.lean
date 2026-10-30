-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanDrawsQ.lean: the block samplers of a protocol that is made from a plan, as a function of the
rounds' data (the plan's entries and the rounds' kinds); their bias; an instance: a toy of this
library's own.

This file is about how the verifier messages of all rounds of an interactive protocol are made from
blocks of 256 bits, for the protocols that Run/PlanQTypes.lean builds from a list of rounds' data.
Definitions, statements (each a `Prop` in `Run.Spec`) and proofs.
A plan (`Fmt.Plan`, Fmt/Plan.lean) has a list of entries (`Fmt.Entry`), one for a round or a run of
like rounds. An entry says, among other numbers, how many elements, positions and matrix entries
the verifier draws.
A block sampler (`Iop.BS`, Iop/Draw.lean) is a function from b blocks to the values, with a bound
on its fibres. Under its law `BS.Good s κ` one value of a finite type of values takes at most κ
times its even share of all tuples of b blocks: κ bounds the bias.
From Run/PlanQTypes.lean:
  `PQ.CK`: a choice of challenge types. For each entry and kind it has the type of the verifier's
    message, and the map from such a message to the format's record of what was drawn. (`Fmt.Kind`,
    Fmt/Plan.lean: what a round's verifier message consists of; seven kinds.)
  `PQ.RD`: a round's data: the plan's entry, the kind, and what the round's types need besides.
  `PQ.shapeOf C ds`: the shape, with a trivial round in front.
  `PQ.rds S`: the rounds of a chain's description S (`Fmt.Spec`, Fmt/Rules8.lean).
From Run/DrawPlan.lean: `PlanFor`, `drawsOf`; `drawPlan_good`, `drawPlan_samplers`.
`kapSl 128` (Iop/DrawOf.lean) is 1 + 2^-128.

Main names:
  `ck f`: challenges as sampled values: the type of a round's verifier messages is the values of
    its draws; the view is `drawnOf` (Run/PlanDraws.lean).
  `drawsQ f ds`: the block samplers.
  `Spec.planQ_good`: every round's positions have at most 64 bits (`logN` ≤ 64 in each entry) ⇒
    `Shape.Draws.Good (kapSl 128) (PQ.shapeOf (ck f) ds) (drawsQ f ds)`.
  `Spec.planQ_samplers`: and so, under the same hypothesis, the samplers' law holds with
    (1 + 2^-128)^a and (1 + 2^-128)^c, for a ≥ every round's blocks and c ≥ their sum. The law is
    `Samplers.Good`, Iop/Pull.lean: its first number bounds each round's bias, its second their
    product over all rounds.
  `Spec.planQ_blocks`: the blocks, round by round: 0 for the trivial round, then `Fmt.blocksFor` of
    `Fmt.wordsAtMost` of the entry and kind.
  `Spec.planQ_toy`: the instance: at a toy of this library's own (Fmt/Toy1.lean: a root with 8 bits
    of work, three positions below 16; then an element, nothing drawn): the blocks are 0, 1, 0; the
    law holds with (1 + 2^-128)^1 and (1 + 2^-128)^1. So `drawPlan_good` and `drawPlan_samplers` are
    not empty. A degenerate instance for the bias: the toy draws positions alone, which are exactly
    uniform: no element of a field is drawn in it.

Limits: this file says nothing on the wiring that hands a round's blocks to its sampler. It says
nothing on an instance in which an element of a field is drawn (Run/PlanDrawsSix.lean has one).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanDraws
import Run.PlanQTypes
import Fmt.Toy1

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

/-- The values of the draws of `PQ.e0`, an entry that draws nothing, at the kind `Fmt.Kind.nothing`:
exactly one. -/
@[reducible] def frontCk (f : _root_.Fmt.Fld) : Unique (Ch f PQ.e0 .nothing) :=
  ⟨⟨((fun i => i.elim0, ⟨⟩) : (Fin 0 → Bool × Bool) × PUnit)⟩, fun x => by
    obtain ⟨g, ⟨⟩⟩ : (Fin 0 → Bool × Bool) × PUnit := x
    exact Prod.ext (funext fun i => i.elim0) rfl⟩

/-- The choice of challenge types (`PQ.CK`): challenges as sampled values. -/
def ck (f : _root_.Fmt.Fld) : PQ.CK :=
  ⟨Ch f, fun e k => fintypeVals f (_root_.Fmt.dsOf e k),
    fun e k => neVals f (_root_.Fmt.dsOf e k), drawnOf f, frontCk f⟩

def planL (f : _root_.Fmt.Fld) : (ds : List PQ.RD) → PlanFor f (PQ.shapeL (ck f) ds)
  | [] => ()
  | d :: ds => (⟨_root_.Fmt.dsOf d.entry d.kind, Equiv.refl _⟩, planL f ds)

/-- The draws of every round. -/
def planOf (f : _root_.Fmt.Fld) (ds : List PQ.RD) : PlanFor f (PQ.shapeOf (ck f) ds) :=
  (⟨[], Equiv.refl Unit⟩, planL f ds)

/-- The block samplers. -/
def drawsQ (f : _root_.Fmt.Fld) (ds : List PQ.RD) : (PQ.shapeOf (ck f) ds).Draws 256 :=
  drawsOf f _ (planOf f ds)

namespace Spec

def planQ_good : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List PQ.RD), (∀ d ∈ ds, d.entry.logN ≤ 64) →
    Shape.Draws.Good (kapSl 128) (PQ.shapeOf (ck f) ds) (drawsQ f ds)

def planQ_blocks : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List PQ.RD), blocksOf f _ (planOf f ds) =
    0 :: ds.map fun d => _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost d.entry d.kind)

def planQ_samplers : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List PQ.RD), (∀ d ∈ ds, d.entry.logN ≤ 64) →
    ∀ a c : ℕ, (∀ d ∈ ds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost d.entry d.kind) ≤ a) →
      (ds.map fun d => _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost d.entry d.kind)).sum ≤ c →
      (Samplers.ofDraws (PQ.shapeOf (ck f) ds) (drawsQ f ds)).Good (kapSl 128 ^ a) (kapSl 128 ^ c)

/-- The instance: the toy of Fmt/Toy1.lean, at every claim c, over the field `Fmt.Fld.two`. -/
def planQ_toy : Prop :=
  ∀ c : _root_.Fmt.Ext,
    blocksOf .two _ (planOf .two (PQ.rds (_root_.Fmt.Toy1.spec c))) = [0, 1, 0] ∧
    Shape.Draws.Good (kapSl 128) (PQ.shapeOf (ck .two) (PQ.rds (_root_.Fmt.Toy1.spec c)))
      (drawsQ .two (PQ.rds (_root_.Fmt.Toy1.spec c))) ∧
    (Samplers.ofDraws (PQ.shapeOf (ck .two) (PQ.rds (_root_.Fmt.Toy1.spec c)))
        (drawsQ .two (PQ.rds (_root_.Fmt.Toy1.spec c)))).Good
      (kapSl 128 ^ 1) (kapSl 128 ^ 1)

end Spec

theorem lawfulL (f : _root_.Fmt.Fld) :
    ∀ ds : List PQ.RD,
      (∀ d ∈ ds, d.entry.logN ≤ 64) → PlanFor.Lawful f (PQ.shapeL (ck f) ds) (planL f ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨lawful_dsOf d.entry d.kind (h d List.mem_cons_self),
      lawfulL f ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')⟩

theorem lawfulQ (f : _root_.Fmt.Fld) (ds : List PQ.RD) (h : ∀ d ∈ ds, d.entry.logN ≤ 64) :
    PlanFor.Lawful f (PQ.shapeOf (ck f) ds) (planOf f ds) :=
  ⟨fun _ hd => absurd hd List.not_mem_nil, lawfulL f ds h⟩

theorem planQ_good : Spec.planQ_good := fun f ds h =>
  drawPlan_good f _ (planOf f ds) (lawfulQ f ds h)

theorem blocksL (f : _root_.Fmt.Fld) :
    ∀ ds : List PQ.RD, blocksOf f (PQ.shapeL (ck f) ds) (planL f ds) =
      ds.map fun d => _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost d.entry d.kind)
  | [] => rfl
  | d :: ds => by
    show _root_.Fmt.blocksFor (_root_.Fmt.mostAll (_root_.Fmt.dsOf d.entry d.kind)) ::
        blocksOf f (PQ.shapeL (ck f) ds) (planL f ds) = _
    rw [_root_.Fmt.most_list, blocksL f ds]
    rfl

theorem planQ_blocks : Spec.planQ_blocks := fun f ds => by
  show _root_.Fmt.blocksFor (_root_.Fmt.mostAll []) ::
      blocksOf f (PQ.shapeL (ck f) ds) (planL f ds) = _
  rw [blocksL f ds]
  rfl

theorem planQ_samplers : Spec.planQ_samplers := by
  intro f ds h a c ha hc
  refine drawPlan_samplers f _ (planOf f ds) (lawfulQ f ds h) a c ?_ ?_
  · rw [planQ_blocks f ds]
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact Nat.zero_le a
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hb
      exact ha d hd
  · rw [planQ_blocks f ds, List.sum_cons, Nat.zero_add]
    exact hc

theorem planQ_toy : Spec.planQ_toy := by
  intro c
  have hl : ∀ d ∈ PQ.rds (_root_.Fmt.Toy1.spec c), d.entry.logN ≤ 64 := by
    intro d hd
    have e : (PQ.rds (_root_.Fmt.Toy1.spec c)).map (fun d => d.entry.logN) = [4, 0] := rfl
    have : d.entry.logN ∈ [4, 0] := e ▸ List.mem_map_of_mem hd
    rcases List.mem_cons.1 this with h | h
    · omega
    · rcases List.mem_cons.1 h with h | h
      · omega
      · cases h
  have e0 : (PQ.rds (_root_.Fmt.Toy1.spec c)).map (fun d => (d.entry, d.kind)) =
      [(_root_.Fmt.Toy1.entry1, _root_.Fmt.Kind.positions),
        (_root_.Fmt.Toy1.entry2, _root_.Fmt.Kind.nothing)] := rfl
  have e1 : [(_root_.Fmt.Toy1.entry1, _root_.Fmt.Kind.positions),
          (_root_.Fmt.Toy1.entry2, _root_.Fmt.Kind.nothing)].map
        (fun x => _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost x.1 x.2)) = [1, 0] := by decide
  have hb : (PQ.rds (_root_.Fmt.Toy1.spec c)).map
        (fun d => _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost d.entry d.kind)) = [1, 0] := by
    rw [← e1, ← e0, List.map_map]
    rfl
  refine ⟨by rw [planQ_blocks, hb], planQ_good .two _ hl, planQ_samplers .two _ hl 1 1 ?_ ?_⟩
  · intro d hd
    have : _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost d.entry d.kind) ∈ [1, 0] :=
      hb ▸ List.mem_map_of_mem
          (f := fun d : PQ.RD => _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost d.entry d.kind)) hd
    rcases List.mem_cons.1 this with h | h
    · omega
    · rcases List.mem_cons.1 h with h | h
      · omega
      · cases h
  · rw [hb]
    decide

end Run
