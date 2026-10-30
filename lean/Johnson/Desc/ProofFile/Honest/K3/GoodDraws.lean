-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/GoodDraws.lean: the kind "lookup" (K3): a test with code on the
lookup's own samples; and how many events make the test reject. It is meant as the condition under
which every slot that the lookup's rounds take is named, with a coefficient that is not 0, by a form
of one of the lookup's runs of claims (among them the key side's last form, which the caller's claim
closes): that statement has further conditions and is not in this file. Definitions with code; no
theorem. Its tests by evaluation are in
Honest/K3/GoodDrawsGuards.lean [not in this library]; the statement is in
Honest/K3/GoodDrawsLaw.lean.

Terms. Honest/K3/GLOSSARY.md ("spot", "event", "good samples", "share", "window"). In this file:
"LINE" and "JOIN" are the plan's names of rounds: the round behind a level of a product tree, and
the round of the stage join.

Why. A later test of the verifier asks that in the one batched equation no slot's coefficient is 0.
That coefficient is a polynomial in the batching challenge, whose coefficients are those with which
the single claims name the slot. Where a sample of the lookup makes the only claim that names a slot
name it with 0, the later test rejects at every batching challenge. So the share of such samples has
to be counted, kind by kind, each kind for its own slots.

How a slot is named (Johnson/Desc/Part/MaskedSum4.lean, `row`, `hidingAt`; all variables of a lookup
are summed at a point, so no product of later challenges stands in a coefficient).
  A sumcheck's own slots (the coefficients of its hiding polynomial) stand in its own row alone:
    under r and r ^ 2 for a variable with the challenge r; the last variable's constant under 1. The
    challenge of the further variable Y is no spot: the hearing rejects the word 0 there, and a
    sample that the round can sample has its words below the prime and is not 0 (a hypothesis of the
    statement).
  An end value's slot stands in no row of its own sumcheck. It stands in the row of the next
    sumcheck whose start form names it, under that sumcheck's eps times the start form's
    coefficient: 1 (the tie's chain; the key side's root); 1 - xi and xi (a level's two end values,
    xi the sample of the round "LINE" behind the level); the equality weight of plane j at the point
    of "JOIN" (a plane's root).
  The bits' end value stands in the planes' second claim, under 1.
  The two end values of the last key level stand in the key side's last form, under 1 - xi and xi.
    That form is closed by the caller's claim, not by one of the lookup's own.

What is defined.
  1 `Spot`, `spotsAt`, `spots`: the sampled elements that matter, by stage, round and number; for
    each, whether 0 alone is forbidden, or 0 and 1.
  2 `Spot.value`, `Spot.fine`, `Run`, `Spot.run`, `goodRun`, `goodK3`: the test, run by run and
    whole.
  3 `eventsRun`, `events`, `eventsClosed`, `eventsAt`: the count of events "one named sampled
    element has one named value"; in closed form; at a proof file's lookup of 2 ^ v keys and 2 ^ d
    rows.
  4 `runOf`, `windowOf`: which run of claims names which of the lookup's slots.
  5 `coefIn`, `liveIn`: a slot's coefficient in a form; "some form names it, not with 0".
  6 `spotsOut`, `goodK3Out`, `eventsOut`, `eventsOutAt`: for other kinds' slots: samples of the
    lookup on which weights of other kinds' tests depend.

Users. Honest/K3/GoodDrawsLaw.lean states its sentences over `goodRun`, `goodK3`, `windowOf` and
`liveIn`. The files under Honest/K3/Good/ use the definitions, among them Gives.lean, Mark.lean,
MarkEvents.lean and MarkOut.lean.

Limits. The test may be wider than needed: where fewer than half of the places for bits are real
planes, a coordinate of the point of "JOIN" at 0 makes 0 only the weights of planes that are not
real, and the test rejects all the same. That costs share and harms nothing else. The count is a
number of events; what share of the lists of challenges an event has, and that the shares add up to
a bound, is not said in this file. Shown in part: Honest/K3/Good/MarkShare.lean
(`markK3_le`): the measure is at most the number of events times a letter, under two named
hypotheses; that each event has at most that share is one of the two, and is assumed there.
`eventsClosed`, `eventsAt` and `eventsOutAt` are closed forms; no theorem of this file ties them to
`events` or `eventsOut`. Evaluated in part: Honest/K3/GoodDrawsGuards.lean [not in this library]:
`events` is `eventsClosed` at five synthetic
faces; `events` is `eventsAt`, and `eventsOut` is `eventsOutAt`, at three pairs of sizes: at these
faces and sizes alone. A face without a level on the table side (d = 0) is not served: `runOf` would
put the planes' roots in the wrong run. `goodK3Out` follows one reading of the other
kinds' tests: see its own docstring and that of `spotsOut`.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Row
import Johnson.Desc.ProofFile.Honest.K3.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE addE okE isZeroE)
open OnBytes.Model (Aff)

/-! ## 1 The sampled elements that matter -/

/-- **A sampled element of the lookup, by name.** -/
structure Spot where
  stage : Stage
  /-- the round's number in the stage, from 0 -/
  round : Nat
  /-- the element's number among those that the round samples, from 0 -/
  draw : Nat
  /-- false: 0 alone is forbidden. true: 0 and 1 -/
  one : Bool
  deriving DecidableEq, Repr

/-- The spots of a stage. Round 0 of a sumcheck samples eps; round 1 + l samples the challenge
of variable l. -/
def spotsAt (f : LFace) (s : Stage) : List Spot :=
  let eps : List Spot := [⟨s, 0, 0, false⟩]
  let vars : List Spot :=
    (List.range (((s.call f).map (·.vs.length)).getD 0)).map fun l => ⟨s, 1 + l, 0, false⟩
  match s with
  -- the tie's first step and the bits start from the constant 0: their eps scales no slot
  | .tie 0 => []
  | .tie _ => eps
  | .split _ => eps
  | .join => (List.range f.mu).map fun k => ⟨s, 0, k, true⟩
  | .key _ _ => eps ++ vars
  | .keyLine _ _ => [⟨s, 0, 0, true⟩]
  | .tab _ => eps ++ vars
  | .tabLine _ => [⟨s, 0, 0, true⟩]
  | .leaves => eps ++ vars
  | .bits => vars
  | _ => []

/-- **All spots of a lookup**, in the order of the rounds. -/
def spots (f : LFace) : List Spot := (stages f).flatMap (spotsAt f)

/-! ## 2 The test -/

/-- The element at a spot. Here ds are the lookup's own samples, by round, from its first round on.
-/
def Spot.value (f : LFace) (ds : List Fmt.Drawn) (p : Spot) : E :=
  (elemsAt ds (firstRound f p.stage + p.round)).getD p.draw zeroE

/-- The element's words are below the prime; it is not 0; where 1 is forbidden too, it is not 1. -/
def Spot.fine (f : LFace) (ds : List Fmt.Drawn) (p : Spot) : Bool :=
  okE (p.value f ds) && !isZeroE (p.value f ds) && (!p.one || p.value f ds != oneE)

/-- The runs of claims in which the lookup's slots are named: the claims that read hidden values
alone (the lookup's sub-protocol states them); the three claims on the planes (at some places the
lookup's sub-protocol states them, at others the calling kind's); the caller's claim that closes the
key side's last form. -/
inductive Run where
  | objects
  | planes
  | join
  deriving DecidableEq, Repr

/-- **The run whose slots a spot concerns**: a forbidden value at the spot makes a claim of that run
name a slot with 0. The leaves' eps and challenges, and the sample of the round "LINE" behind the
last table level: the planes' claims. The sample of "LINE" behind a part's last key level: the
caller's claim. All others: the lookup's own claims. -/
def Spot.run (f : LFace) (p : Spot) : Run :=
  match p.stage with
  | .leaves => .planes
  | .tabLine l => if l + 1 == f.d then .planes else .objects
  | .keyLine i m => if m + 1 == f.parts.getD i 0 then .join else .objects
  | _ => .objects

/-- **The test for one run's slots**, on the lookup's own samples. -/
def goodRun (f : LFace) (r : Run) (ds : List Fmt.Drawn) : Bool :=
  ((spots f).filter fun p => p.run f == r).all (Spot.fine f ds)

/-- **The test for all of the lookup's slots.** -/
def goodK3 (f : LFace) (ds : List Fmt.Drawn) : Bool :=
  goodRun f .objects ds && goodRun f .planes ds && goodRun f .join ds

/-! ## 3 The count -/

/-- How many events "one named sampled element has one named value" make one run's test reject. -/
def eventsRun (f : LFace) (r : Run) : Nat :=
  (((spots f).filter fun p => p.run f == r).map fun p => if p.one then 2 else 1).sum

/-- **How many make the whole test reject.** -/
def events (f : LFace) : Nat := ((spots f).map fun p => if p.one then 2 else 1).sum

/-- The same in closed form: the variables' challenges (key levels; table levels; leaves; bits); the
eps (the tie's later steps; the parts' steps; key levels; table levels; the leaves); twice the
rounds "LINE"; twice the coordinates of "JOIN". -/
def eventsClosed (f : LFace) : Nat :=
  ((f.parts.map fun v => v * (v - 1) / 2).sum + (f.mu * f.d + f.d * (f.d - 1) / 2) +
      2 * (f.mu + f.d)) +
    ((f.planes - 2) + (f.parts.length - 1) + f.parts.sum + f.d + 1) +
    2 * (f.parts.sum + f.d) + 2 * f.mu

/-- At a proof file's lookup (mu 5, 32 planes, one part of 2 ^ v keys, 2 ^ d rows). -/
def eventsAt (v d : Nat) : Nat :=
  v * (v - 1) / 2 + d * (d - 1) / 2 + 3 * v + 10 * d + 51

/-! ## 4 Which run of claims names which slot -/

/-- The run that names a stage's slots. If ends is true: the end values' slots; else the sumcheck's
own. -/
def runOf (f : LFace) (s : Stage) (ends : Bool) : Run :=
  match s, ends with
  | .leaves, _ => .planes
  | .bits, true => .planes
  | .tab l, true => if l + 1 == f.d then .planes else .objects
  | .key i m, true => if m + 1 == f.parts.getD i 0 then .join else .objects
  | _, _ => .objects

/-- **The lookup's slots that a run names**, counted from the lookup's first slot. -/
def windowOf (f : LFace) (r : Run) : List Nat :=
  (stages f).flatMap fun s =>
    (if runOf f s false == r then (List.range (s.own f)).map (firstSlot f s + ·) else []) ++
      (if runOf f s true == r then (List.range (s.tail f)).map (firstSlot f s + s.own f + ·) else
        [])

/-! ## 5 A slot's coefficient -/

/-- The coefficient with which a form names slot j: its entries for that slot, added up. -/
def coefIn (a : Aff) (j : Nat) : E :=
  a.slots.toList.foldl (fun c x => if x.1 == j then addE c x.2 else c) zeroE

/-- Some form of the list names slot j with a coefficient that is not 0. -/
def liveIn (l : List Aff) (j : Nat) : Bool :=
  l.any fun a => okE (coefIn a j) && !isZeroE (coefIn a j)

/-! ## 6 For other kinds' slots -/

/-- **Samples of the lookup on which weights in other kinds' tests depend**, each forbidden at 0 and
at 1:
  the challenges of the last key level's variables and the sample of the round "LINE" behind it:
    they are the coordinates of the key side's last point, of which the callers' key points, the
    calls' weights and, at the output head, the points of two tables on the matrix hf are cut;
  the challenges of the leaves' and the bits' variables: they are the two points at which the planes
    are read; at the lookup on the digits of a smallness test the column weights of the planes'
    array are equality weights at their coordinates.
Whose slot or entry is named with 0 at such a sample is for the owning kind's files to say. This
list follows one reading of the tests behind the batching (no weight on a row of the arrays of a
smallness test is 0); it takes every coordinate, where the owner may need fewer. -/
def spotsOut (f : LFace) : List Spot :=
  (f.parts.zipIdx.flatMap fun x =>
    (List.range (x.1 - 1)).map (fun l => (⟨.key x.2 (x.1 - 1), 1 + l, 0, true⟩ : Spot)) ++
      [⟨.keyLine x.2 (x.1 - 1), 0, 0, true⟩]) ++
    (List.range (f.mu + f.d)).map (fun l => (⟨.leaves, 1 + l, 0, true⟩ : Spot)) ++
    (List.range (f.mu + f.d)).map fun l => (⟨.bits, 1 + l, 0, true⟩ : Spot)

/-- **The second test, for the owners of other slots to call**: these samples are neither 0 nor 1;
and the factor of the planes' value in the leaves' claim, alpha - 1 - the table's row at the leaves'
point, is not 0 (its other factor, the leaves' eps, is covered by `goodK3`). -/
def goodK3Out (f : LFace) (ds : List Fmt.Drawn) : Bool :=
  (spotsOut f).all (Spot.fine f ds) &&
    (let p := ptsOf f 0 ds
     let x := f.leaf p.theta p.alpha (leavesR f 0 ds)
     okE x && !isZeroE x)

/-- Its count: two events for each spot, and one more. -/
def eventsOut (f : LFace) : Nat := 2 * (spotsOut f).length + 1

/-- At a proof file's lookup. -/
def eventsOutAt (v d : Nat) : Nat := 2 * (v + 2 * d + 10) + 1

end ProofFile.Honest.K3
