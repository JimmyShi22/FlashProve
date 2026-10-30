-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/CubeJob.lean: from one masked sumcheck's data, as the feed-forward
layers' rounds have them (Johnson/Desc/K4/Honest/Cube.lean: `Job`), to a caller's job in the form of
Honest/Sum.lean (`SumJob`). No part is made here: `sumPart` there makes one of such a job.
Definitions with code. No theorem.

NOT SHOWN HERE. Nothing in this file compares a shape with the job that is used with it: that the
cube has as many rounds as the shape has variables, that they are summed in the shape's way, that
the job has the shape's numbers of lead and end values and its degree in the further variable. Where
they differ `sumPart` pads with 0 or cuts, and no move returns an error. One case goes otherwise:
where the job's end values are not as many as the shape's, `polyInY` (Cube.lean) yields the empty
list, and the round in the further variable holds nothing of the summand. A public test with code
asks these things of a job and its call: `k4JobFits` (Honest/K4/Part.lean), which `k4MakersFit`
there asks of the row's seven jobs, at the zero input and zero challenges alone. The tests that play
these parts against the verifier's text stand in the files ToyCubeLevel, ToyCubeToken, ToyCubePlain
and ToyCubeMerge beside this one (no part of the library yet).

  `k4LevelShape`, `k4TokenShape`, `k4PlainShape`   the three public shapes of a call
  `k4SumJobAt`, `k4SumJob`                      the caller's job, of a function that makes the data

What a job's maker is handed. The input and `Front` (Honest/Sum.lean: the challenges in front of the
part; what was handed on; the rounds shown in front of the part). EVERY MOVE MAKES THE DATA ANEW,
and a move asks two of the job's functions (the points, and its own): so with `k4SumJob` the maker
runs twice a round, with `k4SumJobAt` once.

A job that reads sent values. The batched sumcheck's summand holds end values of an earlier sumcheck
AS THEY WERE SENT. Its maker reads them off `Front.seen`: the rounds that were shown in front of the
part, the part's own left out. Nothing of this file's stands between: the maker is handed `Front`
whole. Honest/Sum.lean's head states a condition on such a job (the mask entries under the items
that are read and the entries that the part spends are apart); nothing here holds it.

Limits. Where the maker yields nothing (`none`) the lists that are made of it are empty (with
`k4SumJobAt` the points are made apart and are not): the part then sends the hiding polynomial's
scalars and mask entries alone, summed at the shape's stand-in 0 where no point is at hand; no move
returns an error.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.K4.Honest.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Desc.First.K4.Honest (Job polyInY)
open VerifiableInference.Desc.Part.MaskedSum (Call)

variable {V W X : Type}

/-- A product level with mu variables: no lead; each variable summed at a point, three coefficients
a round; degree 2 in the further variable; two end values. -/
def k4LevelShape (mu : Nat) : Call := ⟨0, List.replicate mu (.point zeroE 3), some ⟨2, 2⟩⟩

/-- A sumcheck over the tokens: the claimed sum as its lead; lt variables, each summed at a point.
-/
def k4TokenShape (lt dY n : Nat) : Call := ⟨1, List.replicate lt (.point zeroE 3), some ⟨dY, n⟩⟩

/-- A sumcheck of lam variables that are summed plainly; no lead. -/
def k4PlainShape (lam dY n : Nat) : Call := ⟨0, List.replicate lam (.plain 3), some ⟨dY, n⟩⟩

/-- **The caller's job.** shape: public and fixed. points: the coordinates at which the rounds'
variables are summed, in the order of the rounds: WHAT THE JOB's CUBE HAS AS ITS `points`, made
apart so that a move need not lay the tables for them; nothing here holds the two against each
other. job: the data, of the input and of what stands in front of the part. -/
def k4SumJobAt (shape : Call) (points : W → Front X → List E) (job : W → Front X → Option Job) :
    SumJob W X :=
  { shape := shape
    points := points
    lead := fun w fr => ((job w fr).map (·.lead)).getD []
    round := fun w fr rs => ((job w fr).map (·.cube.round rs)).getD []
    inY := fun w fr rs m =>
      ((job w fr).map fun j => polyInY j.dY (j.atEnds rs) (j.ends rs) m).getD []
    ends := fun w fr rs => ((job w fr).map (·.ends rs)).getD [] }

/-- The same, with the points read off the job's own cube. -/
def k4SumJob (shape : Call) (job : W → Front X → Option Job) : SumJob W X :=
  k4SumJobAt shape (fun w fr => ((job w fr).map (·.cube.points)).getD []) job

end ProofFile.Honest.K4
