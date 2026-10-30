-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/RowOf.lean: the honest side of an attention segment's own rounds as
a row of parts, general in what is summed. Definitions with code; no theorem. Tests:
Honest/K5/RowOfToy.lean.

The row's shape is folded from the verifier's own list of stages (`shapes`,
Johnson/Desc/K5/Honest/Faces.lean): a masked sumcheck, with the scalars that stand in front of it,
is one part (`sumPart`, Honest/Sum.lean); a round by itself that sends masked scalars is one
(`scalarsPart`, Honest/ForKinds.lean); a round by itself that sends nothing is one (`quietPart`).

  `Jobs`     for each part, by its number: the true values of the scalars that are sent by
             themselves; the summand
  `rowOf`    the row
  `simsOf`   the form of a simulator beside each part: data; nothing is said of what they are good
             for
  `dueOf`    the stretches of coins that the row spends, in order: name and count
  `Jobs.fits`   a test: at an input and challenges, every list of values sent by themselves has the
             shape's length, and every summand the shape's numbers of variables and end values

The coins. No part takes a coin of its own or carries one. Each part that sends something spends
entries of the segment's mask row, as many as it sends scalars, in the order of sending: a sumcheck
in two stretches, "sum" and "ends", a round of masked scalars in one, "scalars".

Limits. Nothing holds `Jobs` against the verifier's text here. The parts pad or cut a list of
another length than the shape's in silence. `Jobs.fits`, for a caller's toy, tests the lengths of
the lists sent by themselves and each summand's numbers of variables and end values; of a round
polynomial's number of coefficients it asks nothing (a test on that: `Summand.cutIsZero`,
Johnson/Desc/K5/Honest/Terms.lean).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Job
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.K5.Honest.Faces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Place)
open H2K5.Honest (Summand Chal PartShape shapes)

variable {W Pb : Type}

/-- **What is sent by itself and what is summed**, part by part. -/
structure Jobs (W : Type) where
  /-- the true values of the scalars that stand in front of the sumcheck that is part p, or that the
  one round of part p sends -/
  alone : Nat → W → Chal → List E
  /-- the summand of the sumcheck that is part p -/
  sum : Nat → W → Chal → Summand

/-- The lists and the summands have the shapes' counts, part by part. -/
def Jobs.fits (J : Jobs W) (x : OnBytes.Params.AttentionRounds) (w : W) (c : Chal) : Bool :=
  (shapes x).zipIdx.all fun s =>
    match s.1 with
    | .sum k => (J.alone s.2 w c).length == k.lead &&
        (J.sum s.2 w c).fits k.vs.length ((k.ends.map (·.n)).getD 0)
    | .one n => (J.alone s.2 w c).length == n

/-- The three names of a part's stretches. -/
def nameOf (a : Place) (p : Nat) (use : String) : String := runName maskRowRun ⟨a, p⟩ use

/-- **The row.** a: the place. chalOf: the challenges that a part may read, of all that were heard
in front of it. -/
def rowOf (a : Place) (x : OnBytes.Params.AttentionRounds) (chalOf : List Fmt.Drawn → Chal)
    (J : Jobs W) : List (Part Unit W Unit) :=
  (shapes x).zipIdx.map fun s =>
    match s.1 with
    | .sum k =>
      sumPart (nameOf a s.2 "sum") (nameOf a s.2 "ends")
        (jobOf k (fun w fr => J.alone s.2 w (chalOf fr.heard)) fun w fr =>
          J.sum s.2 w (chalOf fr.heard))
    | .one 0 => quietPart
    | .one n => scalarsPart (nameOf a s.2 "scalars") n fun w fr => J.alone s.2 w (chalOf fr.heard)

/-- The form of a simulator beside each part. -/
def simsOf (a : Place) (x : OnBytes.Params.AttentionRounds) : List (Sim Pb) :=
  (shapes x).zipIdx.map fun s =>
    match s.1 with
    | .sum k => sumSim ⟨a, s.2⟩ k
    | .one 0 => quietSim ⟨a, s.2⟩
    | .one n => scalarsSim ⟨a, s.2⟩ n

/-- The stretches that the row spends, in the order of the parts: the part's number, the name, the
number of elements of the extension field. -/
def dueOf (a : Place) (x : OnBytes.Params.AttentionRounds) : List (Nat × String × Nat) :=
  (shapes x).zipIdx.flatMap fun s =>
    match s.1 with
    | .sum k => [(s.2, nameOf a s.2 "sum", ownRun k)] ++
        (k.ends.map fun e => (s.2, nameOf a s.2 "ends", e.n)).toList
    | .one 0 => []
    | .one n => [(s.2, nameOf a s.2 "scalars", n)]

end ProofFile.Honest.K5
