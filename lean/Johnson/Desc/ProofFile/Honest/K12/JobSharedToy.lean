-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/JobSharedToy.lean: tests (`#guard`) of `jobAtU` and `jobAtOmega`
(JobShared.lean), the jobs of the shared chain's two proximity tests, on the groups G_u = {o_u,
o_sp} and G_omega = {o_omega, o_sp}, at the small made-up chain of SharedSmall.lean.
SharedHonest.lean gives honest values for the eight sub-protocols before the tests, over `rowsOf` at
made-up readers, and checks that the constraints which these leave on the two groups hold of the
prover's tables. Here the two proximity tests follow, one after the other: `runBy` (RunBy.lean)
computes the prover's side from the job, and the test's own block decides.

The example. Each test has three stages, (k, h) = (1, 0), (1, 1), (0, 0). o_u has two main rows,
o_omega one, o_sp one mask row. The first fresh table of the test on G_u was sent with o_u; the test
on G_omega sends its own. The members' random values are chosen so that the pads and o_sp's entries
are those of SharedHonest.lean's `wordsAt`, from which its answers are computed.

What is checked, for each test (acceptance and the absence of warnings at two lists of its
challenges, all else at the first). The job's public numbers are those of the verifier's state on
entry (`layFits`), and the rows as given have the stage's sizes (`rowsFit`); at G_omega one of the
two main rows is no member's. The test's own block accepts the output of `runBy`, with no warning.
With `Seams.fast` (and, at G_u, with the folded row passed in as a parameter) the items sent and the
opened columns are the same. The state on entry to the second test is the chain's state after the
first test's accepted output (the seat's `leave` and `enter`). Negative tests, each alone. At G_u:
an entry of the folded row made one larger; an entry of the matrix; o_u's pad; an entry of o_sp. At
G_omega: an entry of omega_col; o_omega's pad; an entry of o_sp. Each time the block rejects. With a
tail of o_u made one larger it accepts: a tail is in no constraint, and the columns are computed
from the same rows. The first opening's columns. The columns of o_u's tree (with the first fresh
table), of o_sp's tree and of o_omega's tree, as the job gives them, equal `columnOf`
(Johnson/Desc/ProofFile/Honest/K14/Sendings.lean) at the sending's own rows (`SendJob.rows`), at all
positions. There the random values are arrays in the sending's order, message after message; their
sizes are the counts that the sendings' parts take.

Limits. Tiny sizes, one list of the chain's challenges. `runBy` is called as it is, where a test has
shown `StagesOk`; a prover's side that is used takes `lightHalfOf` (PartsByJob.lean). No test
changes the reader `rand`. That the block rejects means that `accepts` is false: no rejection is
compared with its message. That the block accepts is a test at one example, no word on completeness.
The state on entry is made by the sub-protocols' `decide` functions in a row, then the seat's
`enter`, the block's `decide`, `leave` and `enter`: not by `Block.step`, `Seat.onGu`,
`Seat.onGomega` or `doorOf`. What precedes the second test holds no round of the first. `first0`
repeats two lines of `runBy`. The arrays of random values are written here by hand: nothing shows
that a player of the parts hands a test's parts the matching ranges. The output is not compared with
`testAll` here. No part is played by the functions of Honest/Frame.lean. Of the three trees of
`jobAtOmega`, o_omega's alone is compared with `columnOf`: o_sp's tree as that job gives it, and the
tree of the fold's own fresh table, are seen only through the columns that the block decides on.
Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.SharedHonest
import Johnson.Desc.ProofFile.Honest.K12.JobShared
import Johnson.Desc.ProofFile.Honest.K12.RunManyToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SharedToy
open OnBytes (E)
open OnBytes.Slice (toE)
open Desc.K14 (St)
open Desc.K14.Honest.Toy (shape chal rnd kappa bump)
open ProofFile.Honest.K12.Light.SharedSmall (codes2 P3 nums p numsO pO)
open ProofFile.Honest.K12.Light.SharedHonest (weights rand rows keyAt roundsAt runAt)
open ProofFile.Honest.K12.ToyWide (genOf)
open ProofFile.Honest.K12.Light.ByToy (at' same)
open VerifiableInference.Desc (noDigest roundsFit Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest.K14 (SendPub Ask)

/-- The chain's state after the eight sub-protocols, at the honest values. -/
def run3 : Except String St := runAt (keyAt (rows 0)) (rows 0) (chal 0)

def door : T12 :=
  (run3.bind
    (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))).toOption.getD noState

def declared : List Fmt.DeclaredRound := (H2U.roundsOfNums nums).getD []

/-- What a test can change: numbers added to an entry of the folded row, of the committed table, to
o_u's pad, to an entry of o_sp, to a tail of o_u; whether the folded row is passed in. -/
structure Turn where
  u : ℕ := 0
  table : ℕ := 0
  pad : ℕ := 0
  sp : ℕ := 0
  tail : ℕ := 0
  passed : Bool := false

def uAt (t : Turn) (i : ℕ) : E :=
  bump (if i == 3 then t.u else 0) (Desc.K14.Honest.uAtE shape (chal 0).psi (rows 0) i)

def job (t : Turn) : ManyJob Unit Unit :=
  jobAtU ⟨P3, 0⟩ p (fun _ _ => door) (fun _ => weights t.table) (fun _ => rand)
    (if t.passed || t.u != 0 then some fun _ _ => uAt t else none)

/-- What precedes the test: the chain's challenges and rounds. The toy stands where no column is
handed: `Seen.bare`. -/
def fr : Front Unit :=
  let rs := (roundsAt (rows 0) (chal 0)).flatMap (·.1)
  ⟨rs.map (·.drawn), (), Seen.bare rs⟩

def ge (x : E) : OnBytes.Slice.GE := toE x.triple

/-- The random values. o_u: four tail entries, then its pad. o_sp: four entries, then two tail
entries. The pad and o_sp's entries are those of SharedHonest.lean's `wordsAt`. -/
def coins (t : Turn) : TestCoins :=
  ⟨fun i => ge (rnd (400 + i)), fun b q => ge (rnd (500 + 2 * b + q)),
    fun m => ⟨fun _ => 0, fun i =>
      if m = 0 then
        (if i = 4 then ge (bump t.pad (rnd 50))
        else ge (bump (if i = 0 then t.tail else 0) (rnd (80 + i))))
      else if i = 0 then ge (bump t.sp kappa) else if i = 3 then ge (rnd 52)
      else if i < 4 then ge (rnd (70 + i)) else ge (rnd (90 + i))⟩,
    fun i => ge (rnd (600 + i))⟩

def light (S : Seams) (t : Turn) (n : ℕ) : RunOut :=
  runBy S (RunIn.ofRun (job t).toRun () fr (coins t)) (at' (genOf declared n))
def accepts (a : RunOut) : Bool :=
  roundsFit (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds a.rs &&
    Except.isOk ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide door (a.rs.map noDigest) a.gs)

/-- The same items sent, and the same opened columns. -/
def sameOut (a b : RunOut) : Bool := a.rs.map (·.vals) == b.rs.map (·.vals) && a.gs == b.gs

-- the eight sub-protocols accept; the block's test on the plan accepts the parameters
#guard run3.isOk && (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk
-- layout, sizes, stages
#guard (job {}).layFits door && (job {}).toRun.rowsFit () fr (coins {}).mem &&
  StagesOk p.nums.stages
-- the block accepts; no warning
#guard accepts (light .lib {} 0) && accepts (light .lib {} 1)
#guard (light .lib {} 0).no == [] && (light .lib {} 1).no == []
-- with the folded row passed in, and with Seams.fast: the same output
#guard sameOut (light .lib { passed := true } 0) (light .lib {} 0)
#guard sameOut (light .fast {} 0) (light .lib {} 0)
-- negative tests
#guard !accepts (light .lib { u := 1 } 0) && !accepts (light .lib { table := 1 } 0)
#guard !accepts (light .lib { pad := 1 } 0) && !accepts (light .lib { sp := 1 } 0)
-- a tail is in no constraint
#guard accepts (light .lib { tail := 1 } 0) &&
  (light .lib { tail := 1 } 0).gs != (light .lib {} 0).gs

/-! ## The first opening's columns against the sendings' own tables -/

/-- The state at which the two sendings' parts are evaluated. -/
def st : State Ask Unit := ⟨⟨rows 0⟩, fr.heard, ()⟩

/-- The random values of "send o_u", in the sending's own order: o_u's five, then the first fresh
table's: three coefficients and two tail entries. -/
def csU : Array E :=
  ((List.range 5).map fun i => if i = 4 then rnd 50 else rnd (80 + i)).toArray ++
    ((List.range 3).map fun i => rnd (400 + i)).toArray ++
    ((List.range 2).map fun q => rnd (500 + q)).toArray

/-- The random values of "send o_omega": o_omega's two tail entries and its pad, then o_sp's six. -/
def csO : Array E :=
  #[rnd 700, rnd 701, rnd 51, kappa, rnd 71, rnd 72, rnd 52, rnd 94, rnd 95]

/-- The first stage's lists as `runBy` holds them, with the fresh table. -/
def first0 (I : RunIn) : Fmt.M1.Own.PSt :=
  let rd := ridersBy .two I.coin 1 (I.p.nums.stages.headD default) false
  { I.first with P := rd.1, Pi := rd.2 }

def treeAt (I : RunIn) (i x : ℕ) : List UInt64 := ((I.trees (first0 I)).getD i (0, fun _ => [])).2 x

def inU : RunIn := RunIn.ofRun (job {}).toRun () fr (coins {})

-- the sendings' counts of random values are these arrays' sizes
#guard (ProofFile.Honest.K14.sendingPart (ProofFile.Honest.K14.jobU ⟨P3, 0⟩)).takes == ⟨0, csU.size⟩ &&
  (ProofFile.Honest.K14.sendingPart (ProofFile.Honest.K14.jobOmega ⟨P3, 0⟩)).takes == ⟨0, csO.size⟩
-- o_u's tree (with the first fresh table), at all 64 positions; o_sp's tree, at all 16
#guard (List.range 64).all fun x =>
  treeAt inU 0 x == ProofFile.Honest.K14.columnOf codes2 (ProofFile.Honest.K14.jobU ⟨P3, 0⟩).Q.sent
    ((ProofFile.Honest.K14.jobU ⟨P3, 0⟩).rows st csU) 0 x
#guard (List.range 16).all fun x =>
  treeAt inU 1 x == ProofFile.Honest.K14.columnOf codes2 (ProofFile.Honest.K14.jobOmega ⟨P3, 0⟩).Q.sent
    ((ProofFile.Honest.K14.jobOmega ⟨P3, 0⟩).rows st csO) 1 x
-- the columns are not empty, and the comparison can fail
#guard (treeAt inU 0 5).length == 9 && (treeAt inU 1 5).length == 3
#guard treeAt inU 0 5 != ProofFile.Honest.K14.columnOf codes2 (ProofFile.Honest.K14.jobU ⟨P3, 0⟩).Q.sent
  ((ProofFile.Honest.K14.jobU ⟨P3, 0⟩).rows st (csU.modify 6 (bump 1))) 0 5

/-! ## The test on G_omega, after the test on G_u -/

/-- The state on entry to the test on G_omega, computed from the chain's state after the accepted
test on G_u; `noState` where a step returns an error. -/
def doorO : T12 :=
  let a := light .lib {} 0
  (run3.bind fun d =>
    ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide door (a.rs.map noDigest) a.gs).bind fun t =>
      (VerifiableInference.Desc.K12.Seat.leave d t).bind
        (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)).toOption.getD noState

def declaredO : List Fmt.DeclaredRound := (H2U.roundsOfNums numsO).getD []

/-- up: added to entry 1 of omega_col. -/
def jobO (up : ℕ) : ManyJob Unit Unit :=
  jobAtOmega ⟨P3, 0⟩ pO (fun _ _ => doorO) (fun _ => weights 0) (fun _ => rand)
    (if up = 0 then none else some fun _ _ i =>
      bump (if i == 1 then up else 0) (Desc.K14.Honest.omegaAtE shape (chal 0).psi (rows 0) i))

def coinsO (pad sp : ℕ) : TestCoins :=
  ⟨fun i => ge (rnd (800 + i)), fun b q => ge (rnd (810 + 2 * b + q)),
    fun m => ⟨fun _ => 0, fun i =>
      if m = 0 then (if i = 2 then ge (bump pad (rnd 51)) else ge (rnd (700 + i)))
      else if i = 0 then ge (bump sp kappa) else if i = 3 then ge (rnd 52)
      else if i < 4 then ge (rnd (70 + i)) else ge (rnd (90 + i))⟩,
    fun i => ge (rnd (900 + i))⟩

def lightO (S : Seams) (up pad sp n : ℕ) : RunOut :=
  runBy S (RunIn.ofRun (jobO up).toRun () fr (coinsO pad sp)) (at' (genOf declaredO n))
def acceptsO (a : RunOut) : Bool :=
  roundsFit (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds a.rs &&
    Except.isOk ((proximityTestKind guardedProximityTestParts pO : Block T12 Unit).decide doorO (a.rs.map noDigest) a.gs)

#guard (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).planOk && StagesOk pO.nums.stages
-- row 1 of the stage's two main rows is no member's
#guard (jobO 0).layFits doorO && (jobO 0).toRun.rowsFit () fr (coinsO 0 0).mem
#guard acceptsO (lightO .lib 0 0 0 0) && acceptsO (lightO .lib 0 0 0 1)
#guard (lightO .lib 0 0 0 0).no == [] && (lightO .lib 0 0 0 1).no == []
#guard sameOut (lightO .fast 0 0 0 0) (lightO .lib 0 0 0 0)
-- negative tests
#guard !acceptsO (lightO .lib 1 0 0 0) && !acceptsO (lightO .lib 0 1 0 0) &&
  !acceptsO (lightO .lib 0 0 1 0)
-- o_omega's tree against the sending's own table, at all 32 positions
#guard (List.range 32).all fun x =>
  treeAt (RunIn.ofRun (jobO 0).toRun () fr (coinsO 0 0)) 0 x ==
    ProofFile.Honest.K14.columnOf codes2 (ProofFile.Honest.K14.jobOmega ⟨P3, 0⟩).Q.sent
      ((ProofFile.Honest.K14.jobOmega ⟨P3, 0⟩).rows st csO) 0 x

end ProofFile.Honest.K12.Light.SharedToy

#print axioms ProofFile.Honest.K12.Light.SharedToy.run3
#print axioms ProofFile.Honest.K12.Light.SharedToy.door
#print axioms ProofFile.Honest.K12.Light.SharedToy.declared
#print axioms ProofFile.Honest.K12.Light.SharedToy.Turn
#print axioms ProofFile.Honest.K12.Light.SharedToy.uAt
#print axioms ProofFile.Honest.K12.Light.SharedToy.job
#print axioms ProofFile.Honest.K12.Light.SharedToy.fr
#print axioms ProofFile.Honest.K12.Light.SharedToy.ge
#print axioms ProofFile.Honest.K12.Light.SharedToy.coins
#print axioms ProofFile.Honest.K12.Light.SharedToy.light
#print axioms ProofFile.Honest.K12.Light.SharedToy.accepts
#print axioms ProofFile.Honest.K12.Light.SharedToy.sameOut
#print axioms ProofFile.Honest.K12.Light.SharedToy.st
#print axioms ProofFile.Honest.K12.Light.SharedToy.csU
#print axioms ProofFile.Honest.K12.Light.SharedToy.csO
#print axioms ProofFile.Honest.K12.Light.SharedToy.first0
#print axioms ProofFile.Honest.K12.Light.SharedToy.treeAt
#print axioms ProofFile.Honest.K12.Light.SharedToy.inU
#print axioms ProofFile.Honest.K12.Light.SharedToy.doorO
#print axioms ProofFile.Honest.K12.Light.SharedToy.declaredO
#print axioms ProofFile.Honest.K12.Light.SharedToy.jobO
#print axioms ProofFile.Honest.K12.Light.SharedToy.coinsO
#print axioms ProofFile.Honest.K12.Light.SharedToy.lightO
#print axioms ProofFile.Honest.K12.Light.SharedToy.acceptsO
