-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumFits.lean: one named test for every caller of the masked sumcheck's
part and of the round of scalars: the job's lists have the shape's counts. `sumPart`
(Honest/Sum.lean) and `scalarsPart` (Honest/ForKinds.lean) never return an error: where a caller's
list is too short it is padded with 0 (a missing point: the shape's placeholder stays), where it is
too long it is cut, silently (the limits of Honest/Sum.lean say so). A move must stay total; so the
test is put beside the part: in a
toy example or a printout it is run and its result is shown; in a statement on what is sent it is a
named hypothesis. Executable definitions, and tests at a toy example; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

  `pointsIn`   how many variables of a shape are summed at a point
  `SumJob.fitsAt`   at an input, a `Front`, the variables' challenges and the end values' mask
     entries: the points, the lead's values and the end values are exactly as many as the shape
     says; of no round's polynomial is a coefficient that is not 0 cut (`noneCut`: fewer
     coefficients, or zeros beyond the variable's degree, are the same polynomial)
  `SumJob.lensFitAt`   the same by lengths alone: the stricter test; it reads no element's value
  `scalarsFitAt`   the values of a round of scalars are exactly n
  `challengesFit`   each of the part's own challenges that it reads holds an element (one without
     counts as 0 in `drawnE`): all but the last where the shape has ends
  `SumJob.fitsShapeAt`   `fitsAt` with the library's own test on the shape (`MaskedSum.shapeOk`)

Where the tests are required, and where not. They are required wherever a statement says what is
sent: that a part plays the protocol's own message, that the verifier accepts it, that the job is
the protocol's: there a padded or cut value is a wrong message, silently. They are not required for
a lemma that says only how what is shown is distributed over the borrowed coins: no list of the
job's reaches a coin's place: every take, drop or padding on a coin has its count from the shape or
the type. Such a lemma needs none of these tests as a hypothesis, only the library's `shapeOk`,
besides `drawsFit` at the call's entries, which `Good.exact` carries (a reading of the definition of
`sumPart`; stated by no theorem here).

Limits.
  * None of these tests is a hypothesis on public data, in any form: all five functions of a job are
    given the prover's input; `inY` is given the end values' mask entries m too, which are coins;
    and `noneCut` reads not lengths alone but whether the coefficients beyond the degree are 0:
    values. So a statement that carries one of them as a hypothesis has it at all inputs, `Front`s,
    challenges and coins, or its hypothesis selects among these.
  * `lensFitAt` reads lengths alone and is the stricter (a list within the length has nothing cut:
    stated by no theorem here); the lengths are still those of lists computed from the input.
  * The padded lists are the caller's values, which are under mask entries.
  * `sumPart` applies its padding to one list of coins too, the end values' mask entries: there it
    has no effect, since that list has the shape's count by its type; `fitsAt` asks it of m all the
    same.
  * `fitsAt` passes at a call without a variable and without ends, where `sumPart` sends the
    constant 0 though one coin is borrowed: that shape is what `shapeOk` rejects (`fitsShapeAt` asks
    both).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call shapeOk)

variable {W X : Type}

/-- How many variables are summed at a point. -/
def pointsIn (vs : List Var) : Nat :=
  (vs.filter fun v => match v with | .point _ _ => true | .plain _ => false).length

/-- Nothing but zeros is cut where a polynomial's list is cut to d coefficients. -/
def noneCut (d : Nat) (g : List E) : Bool := (g.drop d).all (· == zeroE)

/-- **The job's lists have the shape's counts.** `rs`: the variables' challenges, as many as there
are variables. `m`: the end values' mask entries. -/
def SumJob.fitsAt (J : SumJob W X) (w : W) (fr : Front X) (rs m : List E) : Bool :=
  let k := J.shape
  (J.points w fr).length == pointsIn k.vs && (J.lead w fr).length == k.lead &&
    rs.length == k.vs.length &&
    (k.vs.zipIdx.all fun v => noneCut v.1.d (J.round w fr (rs.take v.2))) &&
    (match k.ends with
     | none => true
     | some e => noneCut (e.dY + 1) (J.inY w fr rs m) && (J.ends w fr rs).length == e.n &&
        m.length == e.n)

/-- **The same by lengths alone**: no round's list is longer than its variable's degree allows. The
stricter test: a list within the length has nothing cut. It reads no element's value. -/
def SumJob.lensFitAt (J : SumJob W X) (w : W) (fr : Front X) (rs m : List E) : Bool :=
  let k := J.shape
  (J.points w fr).length == pointsIn k.vs && (J.lead w fr).length == k.lead &&
    rs.length == k.vs.length &&
    (k.vs.zipIdx.all fun v => decide ((J.round w fr (rs.take v.2)).length ≤ v.1.d)) &&
    (match k.ends with
     | none => true
     | some e => decide ((J.inY w fr rs m).length ≤ e.dY + 1) && (J.ends w fr rs).length == e.n &&
        m.length == e.n)

/-- **The values of a round of scalars are exactly n.** -/
def scalarsFitAt (n : Nat) (vals : W → Front X → List E) (w : W) (fr : Front X) : Bool :=
  (vals w fr).length == n

/-- **Each challenge that the part reads holds an element.** `ds`: the part's own challenges, one
for each round. Where the shape has ends the last round samples no element, and the part does not
read its challenge: it is left out. Without ends the last challenge is asked too, though the part
does not read it. -/
def challengesFit (k : Call) (ds : List Fmt.Drawn) : Bool :=
  ds.length == (scalarsOf k).length &&
    (if k.ends.isSome then ds.dropLast else ds).all fun d => !d.elems.isEmpty

/-- **Both tests**: the library's own test on the shape (`MaskedSum.shapeOk`; among other things: a
call without ends has a variable) and `fitsAt`. -/
def SumJob.fitsShapeAt (J : SumJob W X) (w : W) (fr : Front X) (rs m : List E) : Bool :=
  shapeOk J.shape && J.fitsAt w fr rs m

/-! ### Tests at a toy example -/

namespace SumFitsToy

def e (x : UInt64) : E := E.ofTriple (x, 0, 0)

/-- One lead value; a plain variable of three coefficients, one at a point of two; no ends. -/
def J : SumJob Unit Unit :=
  { shape := { lead := 1, vs := [.plain 3, .point zeroE 2], ends := none }
    points := fun _ _ => [e 5], lead := fun _ _ => [e 1]
    round := fun _ _ rs => if rs.isEmpty then [e 1, e 2, e 3] else [e 4]
    inY := fun _ _ _ _ => [], ends := fun _ _ _ => [] }
def fr : Front Unit := { heard := [], own := () }
def dE (x : UInt64) : Fmt.Drawn := ⟨[(x, 0, 0)], [], [], none⟩
def d0 : Fmt.Drawn := ⟨[], [], [], none⟩

#guard pointsIn J.shape.vs == 1
#guard J.fitsAt () fr [e 7, e 8] []
-- a lead's value missing; a point too many; a polynomial that would be cut; challenges too few
#guard !({ J with lead := fun _ _ => [] }).fitsAt () fr [e 7, e 8] []
#guard !({ J with points := fun _ _ => [e 5, e 6] }).fitsAt () fr [e 7, e 8] []
#guard !({ J with round := fun _ _ _ => [e 1, e 2, e 3] }).fitsAt () fr [e 7, e 8] []
#guard !J.fitsAt () fr [e 7] []
-- zeros beyond the degree are the same polynomial
#guard ({ J with
    round := fun _ _ rs => if rs.isEmpty then [e 1, e 2, e 3, zeroE, zeroE] else [e 4] }).fitsAt
  () fr [e 7, e 8] []
#guard noneCut 2 [e 1, e 2, zeroE] && !noneCut 2 [e 1, e 2, e 3] && noneCut 2 [e 1]
-- by lengths alone: the example's job passes; the job with zeros beyond the degree does not
#guard J.lensFitAt () fr [e 7, e 8] [] &&
  !({ J with
    round := fun _ _ rs => if rs.isEmpty then [e 1, e 2, e 3, zeroE, zeroE] else [e 4] }).lensFitAt
  () fr [e 7, e 8] []
#guard scalarsFitAt 2 (fun (_ : Unit) (_ : Front Unit) => [e 1, e 2]) () fr &&
  !scalarsFitAt 2 (fun (_ : Unit) (_ : Front Unit) => [e 1]) () fr
-- the example's call has three rounds, no ends: each challenge holds an element; one without: no
#guard challengesFit J.shape [dE 1, dE 2, dE 3] && !challengesFit J.shape [dE 1, d0, dE 3] &&
  !challengesFit J.shape [dE 1, dE 2]
-- with ends the last round samples no element: an honest list passes; an empty one before it: no
#guard challengesFit { J.shape with ends := some ⟨1, 1⟩ } [dE 1, dE 2, dE 3, dE 4, d0] &&
  !challengesFit { J.shape with ends := some ⟨1, 1⟩ } [dE 1, dE 2, dE 3, d0, d0]
-- a call without a variable and without ends: `fitsAt` passes; the library's test on the shape does
-- not: so `fitsShapeAt` returns false
#guard ({ J with shape := { lead := 1, vs := [], ends := none }, points := fun _ _ => [] }).fitsAt
    () fr [] [] &&
  !({ J with shape := { lead := 1, vs := [], ends := none }, points := fun _ _ => []
    }).fitsShapeAt () fr [] [] && J.fitsShapeAt () fr [e 7, e 8] []

end SumFitsToy

end ProofFile.Honest
