-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FitShared.lean: checks, computed from public data alone, on the
jobs of the shared chain's two proximity tests (`jobAtU`, `jobAtOmega`, JobShared.lean). Definitions
only. It imports Mathlib.

Why. Two checks on a job are not public by their types: `RunJob.rowsFit` (RunJob.lean) takes the
prover's input, what precedes the test and the members' random values, and `ManyJob.layFits`
(RunMany.lean) takes a verifier's state. And no check compares the numbers at which the sender
builds the first fresh table with the first stage's.

  `memFits`      a member has a row, and its codes have the message and tail lengths of the stage's
                 codes, for the rows that it has
  `sharedFitsU`, `sharedFitsOmega`   `memFits` at both members of a test's group. Where it is true,
                 `rowsFit` is true for all arguments (`rowsFit_atU`, `rowsFit_atOmega`)
  `freshFitsU`   "send o_u" builds the first fresh table at the first stage's k and h, as 2 ^ h mask
                 rows and no main row, under the stage's mask code; the test's parameters say that
                 the fold does not send it; and h ≤ k
  `coefAt`       the number of a coefficient of the hiding polynomial among the table's values
  `freshFitsOmega`   the test's parameters say that the first fold sends its own fresh table
  `PubState`, `pubOf`, `PubState.st`, `layFitsPub`   the part of a state that `layFits` reads: the
                 codes, each group's two code numbers, members and kept marks, each oracle message's
                 shape, and the number of the group under test. `layFitsPub` calls `layFits` at a
                 state that is built from that part alone (`stateOfPub`), and equals `layFits`
                 (`layFits_pub`). It takes a whole job; that `layFits` reads of a job only its
                 parameters and its members' shapes is `layFits_pubJob` (FitSharedAt.lean)
The theorems are in FitSharedLaw.lean. At the small example of SharedSmall.lean the checks are
theorems that Lean's kernel evaluates (FitSharedAt.lean). FitAtHead.lean has the four checks on
members and fresh table at the full size: at the typed plan and the written places by the kernel,
and at the seated places under the library's head. `layFitsPub` is proved at the small example
alone (FitSharedAt.lean); its narrower form `layFitsNear` (PubNear.lean) at the small example
(PubAtSmall.lean) and, under the library's head, at the full size (NearAtHead.lean).

The first fresh table. Where `freshFitsU` is true, with k, h, Z the first stage's:
- The sender's count of the table's random values is the count that the test's second part states
  for the stretch that it carries (`freshDue_atU`). The first part states 2 * k + 1, for the
  coefficients alone.
- The sender's rows are `freshRow` at its values number `coefAt k l t`, with the constant at number
  2 * (k - 1) (`freshCoef_atU`). Its tail entry q of row b is its value number 2 * k + 1 + b * Z.r +
  q (`freshTail_atU`).
- For any random values C, the test's first state holds `packedN` of `byName` at the values number
  `coefAt k l t` of `C.hide`, with the constant at number 2 * (k - 1) (`freshTest_atU`). This needs
  h ≤ k: the test calls `hideAt` at h + (k - h). The table's tails there are `C.tails`
  (`freshTails_atU`).
- The test reads the coefficients a second time: the first fold's rounds are computed from field `W`
  of `coinsOf` (Coins.lean) at stage 0. That is `byName` at the same numbers of `C.hide`
  (`freshSums_atU`). That `testAll` passes `coinsOf` at `C.hide` on, and that the fold reads `W` at
  stage 0, are the definitions in Test.lean and Johnson/Desc/K12/Honest/Stages.lean; no theorem here
  says it.
- At C := `restCoins J c` (Parts.lean), tail entry q of row b is `C.hide` at number 2 * k + 1 + b *
  Z.r + q (`restCoins_tails`, `tailsIn_eq`). That the second part's moves pass these values on is
  that part's definition in Parts.lean; no theorem here says it.
- The first part's moves get another C (`firstPart`, Parts.lean): at `jobAtU` its `C.hide` is the
  stretch of 2 * k + 1 values that this part spends (`spentRun`), and its `C.tails` is 0 everywhere.
  `freshTest_atU` and `freshSums_atU` hold at that C as at any other; the sentence on `restCoins`
  does not speak of it. No theorem here compares the spent stretch with the stretch that the second
  part carries.
Not proved here: that the sender's table and the test's are the same table. That `freshRows` and the
packing `packedN` put a coefficient at the same place, where the rows have room for the coefficients
(2 * k + 1 ≤ h + Z.l for h ≤ k), is a theorem of the library (`fresh_packed`,
Johnson/Prover/Link/FoldPairs.lean, on `packed`); its form at `packedN`, for coefficients whose
words are below the prime, is `nx_fresh` (RunByNext.lean), and `coefU_numbered` (RunByTies.lean)
ties `coefU` to `hideAt`. Its corollary at the job is `fresh_atU` (FreshAtJob.lean): entry by entry,
decoded, the sender's table is the test's. It asks `freshFitsU`, that room, which is a clause of
`StagesOk` and none of `freshFitsU`, and that sender and test are given the same values
(`SameFresh`), which is up to the caller. JobSharedToy.lean compares, at one example, the sender's
columns with the columns of the job on words, whose fresh table is built by `freshRows` as well
(`ridersBy`, Run.lean): by itself that test does not compare `freshRows` with `packedN`. That
`coefAt k l t` and the number 2 * (k - 1) are the numbers 0 to 2 * k, below the tails', is not
proved here; its like in other letters is `hide_perm` (KeptLaw2.lean), on `hideIx`, whose text at n
= 2 * l + t is `coefAt`'s, by reading. `srcOf` (KeptSpec.lean) has a formula of the same form, in
terms of the number 2 * l + t, and `kept_perm` with `src_nodup` (KeptLaw2.lean) proves, where the
stages pass `StagesOk`, that `srcOf` maps the kept addresses one to one onto the numbers within the
counts. `srcOf_hide` (KeptLaw2.lean) ties `srcOf` to `hideIx`; no statement of this library ties
`coefAt` to `srcOf` or to `hideIx`.

Limits.
- No definition evaluates these checks. A caller may; nothing refuses a job at which one is false.
- No proof uses the clause of `memFits` that a member has a row (`rowsOk_mem`, FitSharedLaw.lean,
  drops it).
- `rowsFit` speaks of lengths alone. It is true also where two members' blocks overlap or run beyond
  the stage's rows (`layFits` tells that at a state), and it does not compare the count of random
  values that a member states with what its rows read.
- Two further public checks belong to these jobs and are not evaluated or repeated here:
  `sendingsFit` (Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean), on the shapes at which
  `laid` builds what it is meant to build; and `OnBytes.linOk` (OnBytes/Iop/Lin.lean), without which
  `rowsOf` can lay an entry of the matrix where a pad is due.
- `layFits` at a job's state on entry, for every input and whatever precedes the test, follows where
  that state has one public part for all of them (`layFits_all`). At `doorOf` (JobShared.lean) with
  `fall := stateOfPub P` that premise follows from one hypothesis: wherever the fold over the blocks
  before the test and the seat's `enter` return a state, its public part is P (`pubOf_doorOf`,
  `layFits_atDoor`). That hypothesis is not proved here. PubAtDoor.lean proves it for the shared
  chain's test on G_u, under public conditions on the plan (`pub_at_U`; `door_U` is the conclusion
  at `doorOf`). For the test on G_omega PubNear.lean proves the like of a narrower part of the
  state, which is all that `layFits` reads (`layFits_near`, `nearDoor_Omega`). At `fall := noState`,
  `layFits` is false wherever `doorOf` falls back (`layFits_noState`): where the rounds before the
  test are too few, a block rejects one, or `enter` fails.
- With `fall := stateOfPub P`, `layFits` at the state on entry does not tell whether the fold
  returned, and a state function that is `stateOfPub P` everywhere passes as well. So these checks
  are never to be read as "the state on entry is the verifier's": see the limits of JobShared.lean.
  `pubOf` is the part that `layFits` reads, not all that is public of a state: the roots, the book
  and the mask's number are outside it.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.JobShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape)
open Fmt.M1 (Stage)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K14 (SendJob SendPub jobU jobOmega)

variable {W X : Type}

/-! ## 1 The members' rows -/

/-- A member has a row, and its codes have the message and tail lengths of the stage's codes, for
the rows that it has. codes, o: the sending's codes and the message's shape. A message that does not
exist has the default shape, which has no row. -/
def memFits (codes : Codes) (o : OracleShape) (s : Stage) : Bool :=
  !(o.mainRows == 0 && o.maskRows == 0) &&
  (o.mainRows == 0 || ((codes.base.getD o.code default).ell == s.C.l &&
    (codes.base.getD o.code default).r == s.C.r)) &&
  (o.maskRows == 0 || ((codes.mask.getD o.maskCode default).ell == s.Z.l &&
    (codes.mask.getD o.maskCode default).r == s.Z.r))

/-- The shape of message number k of a sending. -/
def shapeAt (J : SendJob) (k : ℕ) : OracleShape := (J.Q.sent.getD k default).shape

/-- The first stage; a stage of zeros where there is none. The same as `ManyJob.s₀`, `RunJob.s₀` and
`TestJob.s₀` at a job with the parameters p (`s₀_many`, `s₀_run`, `s₀_test`, FitSharedLaw.lean). -/
def stage₀ (p : P12) : Stage := p.nums.stages.headD default

/-- `memFits` at o_u and o_sp. -/
def sharedFitsU (A : SendPub) (p : P12) : Bool :=
  memFits (jobU A).Q.codes (shapeAt (jobU A) 0) (stage₀ p) &&
    memFits (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) (stage₀ p)

/-- `memFits` at o_omega and o_sp. -/
def sharedFitsOmega (A : SendPub) (p : P12) : Bool :=
  memFits (jobOmega A).Q.codes (shapeAt (jobOmega A) 0) (stage₀ p) &&
    memFits (jobOmega A).Q.codes (shapeAt (jobOmega A) 1) (stage₀ p)

/-! ## 2 The first fresh table -/

/-- The numbers at which "send o_u" builds the first fresh table are the first stage's: k and h; no
main row and 2 ^ h mask rows; the mask code. The fold does not send the table. And h ≤ k. -/
def freshFitsU (A : SendPub) (p : P12) : Bool :=
  (match (jobU A).sort 1 with
    | .fresh k h => k == (stage₀ p).k && h == (stage₀ p).h
    | .plain _ => false) &&
  (shapeAt (jobU A) 1).mainRows == 0 && (shapeAt (jobU A) 1).maskRows == 2 ^ (stage₀ p).h &&
  sameCode ((jobU A).Q.codes.mask.getD (shapeAt (jobU A) 1).maskCode default) (stage₀ p).Z &&
  !p.nums.ownMask && decide ((stage₀ p).h ≤ (stage₀ p).k)

/-- The number, among a fresh table's random values, of coefficient t (1 or 2) of variable l (1 to
k) of the hiding polynomial. The constant has the number 2 * (k - 1). `laid`
(Johnson/Desc/ProofFile/Honest/K14/Sendings.lean) and `hideAt` (Coins.lean) both write this formula
out; FitSharedLaw.lean ties both to this name (`freshCoef_atU`, `hideAt_coef`, `freshTest_atU`). -/
def coefAt (k l t : ℕ) : ℕ := if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t

/-- The parameters of the test on G_omega say that the first fold sends its own fresh table. -/
def freshFitsOmega (p : P12) : Bool := p.nums.ownMask

/-! ## 3 What `layFits` reads of a state -/

/-- A group without its rows. -/
structure PubGroup where
  code : ℕ
  maskCode : ℕ
  members : Array ℕ
  kept : Array Bool
  deriving DecidableEq, Repr

/-- The codes, the groups without their rows, and the oracle messages' shapes. -/
structure PubState where
  codes : Codes
  groups : Array PubGroup
  shapes : Array OracleShape
  deriving DecidableEq, Repr

/-- That part of a statement. -/
def pubSt (S : OnBytes.Statement) : PubState :=
  ⟨S.codes, S.groups.map fun G => ⟨G.code, G.maskCode, G.members, G.kept⟩, S.oracles.map (·.shape)⟩

/-- That part of a state, with the number of the group under test. -/
def pubOf (t : T12) : PubState × ℕ := (pubSt t.st, t.g)

/-- A statement that holds that part and nothing else: no row, no ledger, no pad. -/
def PubState.st (P : PubState) : OnBytes.Statement :=
  { codes := P.codes, oracles := P.shapes.map fun s => { shape := s }
    groups := P.groups.map fun G =>
      { code := G.code, maskCode := G.maskCode, members := G.members, kept := G.kept } }

/-- A state that holds that part, the number of the group under test, and nothing else. -/
def stateOfPub (P : PubState × ℕ) : T12 := { noState with st := P.1.st, g := P.2 }

/-- `ManyJob.layFits` at a state that is built from the public part alone. -/
def layFitsPub (A : ManyJob W X) (P : PubState × ℕ) : Bool := A.layFits (stateOfPub P)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.memFits
#print axioms ProofFile.Honest.K12.Light.shapeAt
#print axioms ProofFile.Honest.K12.Light.stage₀
#print axioms ProofFile.Honest.K12.Light.sharedFitsU
#print axioms ProofFile.Honest.K12.Light.sharedFitsOmega
#print axioms ProofFile.Honest.K12.Light.freshFitsU
#print axioms ProofFile.Honest.K12.Light.coefAt
#print axioms ProofFile.Honest.K12.Light.freshFitsOmega
#print axioms ProofFile.Honest.K12.Light.PubGroup
#print axioms ProofFile.Honest.K12.Light.PubState
#print axioms ProofFile.Honest.K12.Light.pubSt
#print axioms ProofFile.Honest.K12.Light.pubOf
#print axioms ProofFile.Honest.K12.Light.PubState.st
#print axioms ProofFile.Honest.K12.Light.stateOfPub
#print axioms ProofFile.Honest.K12.Light.layFitsPub
