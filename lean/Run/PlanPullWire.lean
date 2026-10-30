-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullWire.lean: round by round, the compiler's own generic wiring of a round
(`WireRB.ofLocalD`, Iop/BatchWireDraw.lean), at a round made from a plan (a list of rounds' data:
`List PQ.RD`, Run/PlanQTypes.lean; here one member, `d`), the format's sampler and the numbering "a
position is its own number", is the generic construction's wiring of that round, with challenges as
hash blocks and with whole paths.

A definition, statements (`Spec.planPull_depth`, `Spec.planPull_wire`) and proofs.

A wiring is the data that say how deep the trees are, where a position stands among a tree's leaves,
and how blocks of a hash answer give a verifier message (`ProtocolQueryLayout`, of one round `WireRB`,
Iop/BatchWire.lean). The generic construction (Run/PlanQTypes.lean, Run/PlanQWire.lean,
Run/PlanQS.lean) makes, from a description (`Fmt.Spec`, Fmt/Rules8.lean), the typed protocol, its
wiring and the functions that run a file. Challenges as sampled values (`ck`, Run/PlanDrawsQ.lean):
a round's verifier message is the values that the format draws, field elements and positions among
them. Challenges as hash blocks (`ckP`, Run/PlanPull.lean): it is the round's 256-bit blocks, and
reads and decision apply the sampling rule; the library calls the step from sampled values to hash
blocks "pull". Pruned openings: the opened leaves of a tree share one set of sibling digests, as in
the files; whole paths: each opened leaf has an authentication path of its own; the field `prJ` of a
round's wiring says which.

Why: the compiler's theorems (CompileK/Main.lean: `DataK.W`, which is `QueryLayout.ofDraws ..`) are about
a scheme at their wiring: depths are logarithms of numbers of positions, a tree is there if there is
a position, places come from a numbering that is data, the verifier message is the first b of K
blocks, openings are whole paths. The generic construction (`PQ.wireOf`, Run/PlanQWire.lean) writes
depth, tree and places from the plan's shape (of a tree: `Fmt.Shape`, Fmt/Plan.lean). Here: these
are the same records.

Main names:
  `Spec.planPull_depth`: the logarithm of the number of positions is the shape's depth; there is a
    position if and only if there is a tree.
  `Spec.planPull_wire`: the title's equation, for every f, K, d.

How to read `Spec.planPull_wire`: the left side is built from the round with challenges as sampled
values and the format's sampler: the library's wiring pulls the round through the sampler. The
equation typechecks without a cast only because, with challenges as hash blocks, the round's type of
verifier messages IS the sampler's source (Run/PlanPull.lean: planPull_round): so it is itself a
piece of "the generic construction at ckP is the library's pull", for one round.

Notation:
  `f`: the field, one of the format's two (`Fmt.Fld`, Fmt/Rules1.lean);
  `K`: the number of blocks from which a verifier message is made;
  `chalP f K`: the wiring's function from hash blocks to a challenge (Run/PlanPull.lean);
  `bsRound`: the block sampler of the round, of `b` blocks (Run/PlanDraws.lean).

Limits: the wiring of Run/PlanQS.lean's run functions (`PQ.wqS`) has pruned openings; the wiring in
the compiler's theorems has whole paths: so this is not that run's wiring; the wiring with whole
paths is Run/PlanQSF.lean's (`PQ.wqSF`), behind the reader that fills whole paths in.
This file says nothing on the wirings of all rounds together, on the wiring of a protocol (its
bounds on openings and depths, its test of equality of positions) or of an interface, or on the step
that adds the tests. By `wireS_eq` (Run/PlanQSLaws.lean) the generic construction's wiring of a
round with a test is the library's step on `PQ.wireOf`.
For a variable list of rounds the two shapes are equal by induction only (`planPull_shape`,
Run/PlanPull.lean), so "all rounds together" is an equation between terms of different types; at a
closed description the types are one.
This file does not say that the protocol with challenges as hash blocks is the library's pull.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanPull
import Iop.BatchWireDraw

set_option autoImplicit false

namespace Run
open Prob Iop

/-- the numbering: a position is its own number -/
def npOf (t : Option _root_.Fmt.Shape) : Fin (PQ.posN t) ≃ Fin (Fintype.card (Fin (PQ.posN t))) :=
  finCongr (Fintype.card_fin _).symm

namespace Spec

def planPull_depth : Prop :=
  ∀ t : Option _root_.Fmt.Shape,
    Nat.clog 2 (Fintype.card (Fin (PQ.posN t))) = PQ.depthOf t ∧
    decide (0 < Fintype.card (Fin (PQ.posN t))) = t.isSome

def planPull_wire : Prop :=
  ∀ (f : _root_.Fmt.Fld) (K : ℕ) (d : PQ.RD),
    WireRB.ofLocalD 256 K (PQ.roundOf (ck f) d) (PQ.ptOf (ck f) d)
        (bsRound f d.entry d.kind) (npOf d.tree) =
      { PQ.wireOf (ckP f) K (chalP f K) d with prJ := false }

end Spec

theorem planPull_depth : Spec.planPull_depth := by
  intro t
  rw [Fintype.card_fin]
  cases t with
  | none => exact ⟨rfl, rfl⟩
  | some s =>
    refine ⟨?_, ?_⟩
    · show Nat.clog 2 (2 ^ s.a) = s.a
      exact Nat.clog_pow 2 s.a (by decide)
    · show decide (0 < 2 ^ s.a) = true
      exact decide_eq_true (Nat.two_pow_pos s.a)

theorem planPull_wire : Spec.planPull_wire := by
  intro f K d
  have hc : Fintype.card (Fin (PQ.posN d.tree)) = PQ.posN d.tree := Fintype.card_fin _
  have h1 := (planPull_depth d.tree).1
  have h2 := (planPull_depth d.tree).2
  have h3 : (fun j : ℕ =>
        if h : j < Fintype.card (Fin (PQ.posN d.tree)) then some ((npOf d.tree).symm ⟨j, h⟩)
        else none) =
      fun j : ℕ =>
        if h : j < PQ.posN d.tree then some (⟨j, h⟩ : Fin (PQ.posN d.tree)) else none := by
    funext j
    by_cases hj : j < PQ.posN d.tree
    · rw [dif_pos hj, dif_pos (hc.symm ▸ hj)]
      rfl
    · rw [dif_neg hj, dif_neg (hc.symm ▸ hj)]
  unfold WireRB.ofLocalD PQ.wireOf
  congr 1

end Run
