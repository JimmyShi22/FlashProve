-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Mark.lean: the kind "lookup" (K3): the marks at a lookup's own
place, as structures of the frame's form (`Mark`, Honest/Law/Marks.lean): events on the lookup's own
challenges, at which no test of the lookup's member rejects, and which later members' tests need
silent. Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, good
samples, share, kit and window. In this file: a is the lookup's place and f its face.

What is defined.
  `markK3 a f`: it speaks where `goodK3 f` (Honest/K3/GoodDraws.lean) rejects the member's own
    challenges: some slot of the lookup's may be named with the coefficient 0 alone.
  `markRun a f r`: the like for the slots of one run's window.
  `markOut a f`: it speaks where `goodK3Out f` rejects: for other kinds' slots and entries.
  `fieldSize`: the number of the field's elements. The library has the same text as `OkNat.q`
    (Johnson/Bridge/PlanOkNat.lean); the tie: `fieldSize_eq_q` (Honest/K3/Law/TiesSealedForms.lean
    [not in this library]).
None of the three reads a challenge in front of the member.

Imported: Honest/Law/Marks.lean.

Users. Honest/K3/Good/MarkShare.lean and Honest/K3/Good/MarkOut.lean state a bound on the measure of
the messages at which these marks speak, conditional on two hypotheses on the kit, at a letter for
the share.

Limits. The stated shares are written numbers, no bounds: the number of events over the number of
the field's elements. What a mark's silence gives for the lookup's own slots:
Honest/K3/Good/Gives.lean, and Honest/K3/Good/Paid.lean [not in this library] and
Honest/K3/Good/AtBatch.lean [not in this library].
What the silence of `markOut` gives is not stated in this file: whose slot or entry is
named with 0 alone at such a sample is for the owning kind's files to say.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkEvents
import Johnson.Desc.ProofFile.Honest.Law.Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open VerifiableInference.Desc (Place)

/-- The number of the field's elements: the prime's third power. -/
def fieldSize : Nat := (2 ^ 64 - 2 ^ 32 + 1) ^ 3

/-- **The mark for all of the lookup's own slots.** Its field share is a written number, not what is
proved: the bound of Honest/K3/Good/MarkShare.lean is the number of events times a letter: the share
of a round's challenges, at the kit, that show a given element. That is 1 over the field's size only
at a kit that samples evenly. So too in the two marks below. -/
def markK3 (a : Place) (f : LFace) : Mark :=
  { place := a
    test := fun _ own => if goodK3 f own then none else some "K3: a sample at which a slot may die"
    share := ⟨events f, fieldSize⟩ }

/-- **The mark for one run's slots.** -/
def markRun (a : Place) (f : LFace) (r : Run) : Mark :=
  { place := a
    test := fun _ own =>
      if goodRun f r own then none else some "K3: a sample at which a slot of one run may die"
    share := ⟨eventsRun f r, fieldSize⟩ }

/-- **The mark for other kinds' slots and entries.** -/
def markOut (a : Place) (f : LFace) : Mark :=
  { place := a
    test := fun _ own =>
      if goodK3Out f own then none else some "K3: a sample at which another kind's weight may die"
    share := ⟨eventsOut f, fieldSize⟩ }

end ProofFile.Honest.K3.Good
