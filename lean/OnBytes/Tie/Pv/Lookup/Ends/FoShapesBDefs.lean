-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoShapesBDefs.lean: the test "the plan's record of a lookup's numbers is
what Forest.shape makes of the calls that the check passes to the lookup": the definitions.

Each sub-proof's check passes to the lookup's routine Forest.pad a list of calls, the numbers of
padding keys and a cap on a tree's depth. Forest.pad makes the lookup's numbers anew, by
Forest.shape, and lays them into its record. The plan holds a record of the same kind, made when the
layout was made; the chain's plan of rounds is computed from that one. This file holds a test, on
public numbers alone, that the two are the same record. It imports no file of proofs, so that the
test can be run wherever a parameter file lies.

 - callsEqB, shapeEqB: two lists of calls, two records of a lookup's numbers, agree in every field.
 - madeB calls lid fs: Forest.shape calls lid returns, and fs is what it returns with fs's own
   numbers of padding keys laid in.
 - shapeParts X: madeB at the six kinds of lookups of the verifier's record of public numbers, with
   the arguments that the checks pass: the layers' (X.y.cl, X.y.h.lidb, X.y.fo); for each plan hp of
   the layers the smallness test's (the two calls of hp.tl, hp.tl.lidb, hp.tl.f9); for each
   attention plan a its own (the calls of a.S, a.lid, a.fs) and its smallness test's (a.seam.tl);
   the head's (X.HLy.cl, X.hS.LIDB, X.HLy.fs) and its smallness test's (X.H.tl).
 - shapesB X: all of them.
That the checks pass these arguments to Forest.pad is read off OnBytes/Model/Layer.lean, Tail.lean,
Attention.lean and HeadHeard.lean; no statement says it. madeB does not test Forest.pubAsk, the
test that Forest.pad makes of the numbers of padding keys. No file of this library states anything
under shapesB.

No statement. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttBDefs
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model

/-- Two lists of calls agree in every field. -/
def callsEqB (a b : Array Call) : Bool :=
  decide (a.size = b.size) && (List.range a.size).all fun i =>
    callEqB (a.getD i default) (b.getD i default)

/-- Two records of a lookup's numbers agree in every field. -/
def shapeEqB (a b : Forest.Shape) : Bool :=
  callsEqB a.calls b.calls && decide (a.dT = b.dT) && decide (a.kT = b.kT) &&
    decide (a.NT = b.NT) && decide (a.rK = b.rK) && decide (a.NC = b.NC) &&
    decide (a.cK = b.cK) && decide (a.iota = b.iota) && decide (a.first = b.first) &&
    decide (a.callOf = b.callOf) && decide (a.pub = b.pub)

/-- The record fs is what Forest.shape makes of the calls, with fs's own padding numbers. -/
def madeB (calls : Array Call) (lid : ℕ) (fs : Forest.Shape) : Bool :=
  match Forest.shape calls lid with
  | .ok h0 => shapeEqB fs { h0 with pub := fs.pub }
  | .error _ => false

/-- madeB at a smallness test's lookup. -/
def madeZB (tl : HTailF2) : Bool := madeB #[tl.z1.call, tl.z2.call] tl.lidb tl.f9

/-- madeB at an attention sub-proof's lookup. -/
def madeAB (a : Attention.Plan) : Bool := madeB (a.S.calls.map (·.call)) a.lid a.fs

/-- The test at the six kinds of lookups, one by one. -/
def shapeParts (X : Verify.Public) : List (String × Bool) :=
  [("G", madeB X.y.cl X.y.h.lidb X.y.fo)] ++
    (X.G.toList.zipIdx.map fun x => (s!"tG_{x.2}", madeZB x.1.tl)) ++
    (X.A.toList.zipIdx.map fun x => (s!"A_{x.2}", madeAB x.1)) ++
    (X.A.toList.zipIdx.map fun x => (s!"tA_{x.2}", madeZB x.1.seam.tl)) ++
    [("H", madeB X.HLy.cl X.hS.LIDB X.HLy.fs), ("tH", madeZB X.H.tl)]

/-- The test at all lookups of the record. -/
def shapesB (X : Verify.Public) : Bool := (shapeParts X).all (·.2)

end Fo
