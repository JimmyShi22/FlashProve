-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Shape/ClaimRunStatement.lean: THE RUN OF CLAIMS OF THE MERGE OF THE CLAIMS ON THE
WEIGHTS (`headMergeClaim`, Johnson/Desc/First/Fork/MergeKind.lean) ON THE SHAPE OF THE CHAIN's STATE
(`chainSh`, Johnson/Desc/First/Shape/Chain.lean): one definition with code, and STATEMENTS: three,
each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and none of the three is one of
the library's goals: they are lemmas' statements. The texts are the description's; no prover is
named.

Why. To follow the batching of a link on shapes, each run of claims says on shapes the shape of the
state behind it and the shapes of its claims: a `RunLaw`
(Johnson/Desc/First/Batch/Shape/ClaimShape.lean): a run on shapes; the run's own premises on values;
"carries"; "returns".

  `mergeRunG n a`      THE RUN ON SHAPES. It refuses unless the shape stands in the head's open link
                       (number 3), holds a ledger, the head's own fields and what the merge left,
                       and the test for a sumcheck's row (`openB`,
                       Johnson/Desc/First/Shape/Parts.lean) passes: the row is not made, the
                       sumcheck is begun, it has at least one variable and as many challenges as
                       variables, each variable has at least one coefficient, and its own slots are
                       there and free. Then: ONE claim's shape: it takes its own number; no run; the
                       form's slots are the sumcheck's own, then the start's · the shape behind: the
                       ledger's marks at the sumcheck's own slots are laid; all else stands
  `MergeRunCarries`    "carries", WITH NO PREMISE ON VALUES: wherever the run returns (cs, s') at a
                       state and the run on shapes returns y at its shape: y is the shapes of cs
                       and the shape of s'
  `MergeRunReturns`    "returns", WITH NO PREMISE ON VALUES: wherever the run on shapes returns at a
                       state's shape: the run returns at the state
  `MergeRunGAt`        the run on shapes is not idle: at the shape that the kind's update lays
                       (`mergeUpd`, StepStatement.lean of this folder) on a shape at which the
                       kind's test says yes (`mergeGuardB`), where the slots from the ledger's next
                       free number to the end value's are free: it returns

Limits. No state is shown at which the run returns. The run on shapes is sufficient, not necessary:
it asks two sizes of the ledger, and that each variable has at least one coefficient, which the
run's own text does not test: so the run may return where the run on shapes refuses. Nothing on any
property.
-/
import Johnson.Desc.K11.Shape.StepStatement
import Johnson.Desc.First.Batch.Shape.ClaimShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.ShapeStep
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim)

/-- **THE RUN ON SHAPES.** -/
def mergeRunG (_ : Nat) (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  match a.here == 3, a.led, a.head with
  | true, some L, some h =>
    match h.wo with
    | some w =>
      if openB w.p L then
        .ok ([ClaimSh.mk none
            (rowFormSh w.p.first (takenSh w.p.degrees) w.p.start (AffSh.mk [] [])) []],
          a.setLed (L.setGot (fillB L.got w.p.first (takenSh w.p.degrees))))
      else .error "the merge on shapes: the sumcheck's row cannot be made"
    | none => .error "the merge on shapes: it has not run"
  | _, _, _ => .error "the merge on shapes: not inside the head's open link"

/-- The statement of "carries". Not proved here; a lemma's statement, none of the library's goals.
-/
def MergeRunCarries : Prop :=
  ∀ (n : Nat) (s s' : S) (cs : List Claim) (y : List ClaimSh × ChainSh),
    headMergeClaim n s = .ok (cs, s') → mergeRunG n (chainSh s) = .ok y →
    y = (cs.map claimSh, chainSh s')

/-- The statement of "returns". Not proved here; a lemma's statement, none of the library's goals.
-/
def MergeRunReturns : Prop :=
  ∀ (n : Nat) (s : S) (y : List ClaimSh × ChainSh), mergeRunG n (chainSh s) = .ok y →
    ∃ z, headMergeClaim n s = .ok z

/-- The statement that the run on shapes returns behind the kind's update. Not proved here; a
lemma's statement, none of the library's goals. -/
def MergeRunGAt : Prop :=
  ∀ (P : HeadMergeP) (n : Nat) (a : ChainSh) (L : LedSh), mergeGuardB P a = true →
    a.led = some L → freeB L L.next (2 * P.lay.lk + 3) = true →
    ∃ y, mergeRunG n (mergeUpd P a) = .ok y

end Johnson.Desc.First.ForkMerge.ShapeStep

#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeRunG
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.MergeRunCarries
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.MergeRunReturns
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.MergeRunGAt
