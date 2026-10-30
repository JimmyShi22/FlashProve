-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean: how the proof file's description computes its public part
from the three public files: by the planner of PlanPlain.lean, which does not name the program
`verify-on-bytes`'s routines for the segments, and by State.lean's `parP` and `S.startP` for the
first state.

-/
import Johnson.Desc.ProofFile.Pub
import Johnson.Desc.ProofFile.PlanPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile

/-- The first state and its parameters, by State.lean's `parP` and `S.startP`. These are plain
functions: they neither take nor build a context of `verify-on-bytes`. -/
def plainStarts : Starts :=
  { word := "S.startP and parP of State.lean: plain functions that build no context " ++
      "of the older verifier"
    par := VerifiableInference.Desc.First.parP
    start := fun P first =>
      VerifiableInference.Desc.First.S.startP P first.codes first.shape first.layout }

/-- The public part, from the three public files. `o` stands for the second hash function. -/
def pubPlain (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) : Except String Pub :=
  pubBy (ProofFile.PlainG.madeOf o) plainStarts pol lay KL

/-- The way of computing the public part that `onlineDescription` uses. The segments' records are
`linksPlain`'s, which depend on the public record alone. -/
def pureRoad : Road :=
  { word := "PlanPlain.lean's planner: its text names none of the older verifier's links' routines"
    start := plainStarts.word, pub := pubPlain, links := fun X _ => ProofFile.Plain.linksPlain X }

end ProofFile
