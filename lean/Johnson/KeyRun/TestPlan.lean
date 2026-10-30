-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/KeyRun/TestPlan.lean: what a plan's entries must say at the rounds of a proximity test, as
a list that is computed from the test's public sizes, and the test that a plan says so. Definitions
with code, on public data alone.

Words: the head of Johnson/KeyRun/ThirdAtClaim.lean.
Why. A check of a proximity test that is a plain function of the views (such as `dec₃`,
Johnson/KeyRun/Third.lean) reads little of the plan. The verifier program asks more of it. Whenever
its blocks close a round they hold the plan's entry against the round's name, its number of draws
that must not be 0, its range of positions and its count of rows (`Blk.close`,
`Blk.closePositions`, `Blk.requireRows`, OnBytes/Iop/Ground.lean); its strict reader holds the
entry's bytes, roots and answers against the round's description. Here these questions are put to
the plan by themselves.
Main names:
  `Want`: what an entry must say, but for its bits of work and for how many positions it draws.
    `Want.meets`: an entry says so. `Want.misses`: in which fields it does not, for a print.
  `wantsTest`: the entries of a proximity test from its batching round on. Its arguments: the codes,
    the number of answers to a sample, the stages, the number of rows that are batched, the roots
    that the first fold sends itself, and whether later masks ride. Written after the planner's
    list (`ioppList`, OnBytes/Params/PlanListsProx.lean) and after what the blocks ask.
  `wantSeed`, `wantAnswer`: the two rounds of a sending, for a caller's own rounds.
  `okFrom`: the plan's entries from a round on meet a list of wants. `firstMiss`: the first entry
    that does not, for a print.
Limits: no theorem. `wantsTest` is for a test with mask rows and without kept rows (three rows for
each position at "CS"); that it is the planner's list there, or all that the program asks, is not
proved. It is stricter than the program at one place: where no position is drawn it wants the range
0. The bits of work and the numbers of positions come from the planner's sizing and are held against
nothing here. Where a stage names a code that the plan does not have, the code (0, 0, 0) is
taken: `ioppOk` (OnBytes/Iop/Prox.lean) is the test for that. Nothing on soundness.


-/
import OnBytes.Iop.Prox
import OnBytes.Params.Chains

set_option autoImplicit false

namespace Johnson.KeyRun.TestPlan

open OnBytes OnBytes.Params

/-- What a plan's entry must say. -/
structure Want where
  name : String
  msg : Nat := 0
  roots : Nat := 0
  answers : Nat := 0
  drawE : Nat := 0
  drawNZ : Nat := 0
  /-- the range of the positions, if the round draws positions -/
  logN : Option Nat := none
  /-- the rows that the round batches, from the number of its positions -/
  rows : Nat → Nat := fun _ => 0

def Want.meets (w : Want) (e : Fmt.Entry) : Bool :=
  e.name == w.name && e.count == 1 && e.msg == w.msg && e.roots == w.roots &&
  e.answers == w.answers &&
  e.drawE == w.drawE && e.drawNZ == w.drawNZ && e.trits == 0 &&
  (match w.logN with
    | some a => decide (0 < e.poss) && e.logN == a
    | none => e.poss == 0 && e.logN == 0) &&
  e.rows == w.rows e.poss

/-- The fields in which an entry misses a want. -/
def Want.misses (w : Want) (e : Fmt.Entry) : List String :=
  (if e.name != w.name then [s!"name {e.name}, wanted {w.name}"] else []) ++
  (if e.count != 1 then [s!"count {e.count}"] else []) ++
  (if e.msg != w.msg then [s!"msg {e.msg}, wanted {w.msg}"] else []) ++
  (if e.roots != w.roots then [s!"roots {e.roots}, wanted {w.roots}"] else []) ++
  (if e.answers != w.answers then [s!"answers {e.answers}, wanted {w.answers}"] else []) ++
  (if e.drawE != w.drawE then [s!"drawE {e.drawE}, wanted {w.drawE}"] else []) ++
  (if e.drawNZ != w.drawNZ then [s!"drawNZ {e.drawNZ}, wanted {w.drawNZ}"] else []) ++
  (if e.trits != 0 then [s!"trits {e.trits}"] else []) ++
  (match w.logN with
    | some a =>
      (if e.poss == 0 then ["no position"] else []) ++
        (if e.logN != a then [s!"logN {e.logN}, wanted {a}"] else [])
    | none =>
      (if e.poss != 0 then [s!"poss {e.poss}, wanted 0"] else []) ++
        (if e.logN != 0 then [s!"logN {e.logN}, wanted 0"] else [])) ++
  (if e.rows != w.rows e.poss then [s!"rows {e.rows}, wanted {w.rows e.poss}"] else [])

/-- The round of seeds of a prover's message of so many trees. bits: the coordinates of the largest
cube among its sampled messages. -/
def wantSeed (samples roots bits : Nat) : Want :=
  { name := "SEND seed", msg := 32 * roots, roots := roots, drawE := samples * (bits + 1),
    drawNZ := samples }

/-- The round of the answers of n sampled messages. -/
def wantAnswer (samples n : Nat) : Want :=
  { name := "SEND answer", msg := 24 * (samples * n), answers := samples * n }

/-- The stages' rounds. The Bool: this is the test's first stage. -/
def wantsStages (codes : Codes) (samples firstMaskRoots : Nat) (ride : Bool) :
    Bool → List IoppStage → List Want
  | first, x :: y :: rest =>
    let r := if first then firstMaskRoots else if ride then 0 else 1
    let cube := (Send.cube codes (switchTargetStage y.code y.maskCode y.k y.h samples).shape).bits
    [{ name := "FOLD epsilon", msg := 32 * r + 24, roots := r, drawE := 1 }] ++
    List.replicate x.k { name := "FOLD round", msg := 48, drawE := 1 } ++
    [wantSeed samples 1 cube,
     { name := "CS", msg := 24 * samples, answers := samples, drawE := 1,
       logN := some (codes.base.getD x.code default).logN,
       rows := fun t => 1 + samples + 3 * t }] ++
    wantsStages codes samples firstMaskRoots ride false (y :: rest)
  | _, [x] =>
    let r := if ride then 0 else 1
    [{ name := "BASE lambda", msg := 32 * r + 24, roots := r, drawE := 1 },
     { name := "BASE",
       msg := 24 * ((codes.base.getD x.code default).dim +
         (codes.mask.getD x.maskCode default).dim),
       logN := some (codes.base.getD x.code default).logN }]
  | _, [] => []

/-- **The entries of a proximity test, from its batching round on.** -/
def wantsTest (codes : Codes) (samples : Nat) (st : List IoppStage)
    (rowsAtBat firstMaskRoots : Nat) (ride : Bool) : List Want :=
  { name := "BAT", drawE := 1, rows := fun _ => rowsAtBat } ::
    wantsStages codes samples firstMaskRoots ride true st

/-- The plan's entries from round i on meet the wants, one by one. -/
def okFrom (ws : List Want) (es : List Fmt.Entry) (i : Nat) : Bool :=
  ((es.drop i).take ws.length).length == ws.length &&
    (ws.zip (es.drop i)).all fun p => p.1.meets p.2

/-- The first entry that misses, with the fields. -/
def firstMiss (ws : List Want) (es : List Fmt.Entry) (i : Nat) : Option String :=
  if ((es.drop i).take ws.length).length != ws.length then some "the plan ends too early"
  else ((ws.zip (es.drop i)).zipIdx.find? fun p => !p.1.1.meets p.1.2).map fun p =>
    s!"round {i + p.2}: {p.1.1.misses p.1.2}"

end Johnson.KeyRun.TestPlan
