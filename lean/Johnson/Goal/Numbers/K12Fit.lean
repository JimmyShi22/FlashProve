-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K12Fit.lean: the one comparison of numbers in the seam between the shared chain's two
proximity
tests (the kind K12) and the messages that they test (sent by the kind K1): a test with code, and
its
yes, by Lean's kernel, at the written records of a proof file and of a key file.

The laws that carry a proximity test's witness to its member messages (Johnson/Desc/K12/Law/
ShareNear.lean: gp_share, and the files above it) take as a premise, a member a line:
  e < (e0 + 1) * 2 ^ (s.C.a - aOf cs sh)
e: the test's radius at its first stage s, in positions of the range 2 ^ s.C.a; e0: the member
message's own radius, in the leaves of its own tree, of depth aOf cs sh: the radius in the member's
entry of the sending's list, at which K1's law is called. One leaf of a shorter tree is read at
2 ^ (s.C.a - aOf cs sh) positions.
  fitB σ st cs l: the test: at the first stage of the planner's list st, at K12's files' radius
      radBy σ st (K12/Law/CondAtMade.lean: the planner's: the upper end of the group's distance
      times
      the length, rounded down), for every pair (shape, radius) of l
  fit_of: from its yes: the premise, sign for sign, at every written stage a with the first stage's
      numbers and every pair of l
  membersOf fl: the pairs of the written records of the shared chain's first two sendings: o_u;
      o_omega
      and the mask message of the split
  fit_real_U, fit_real_O, fit_key_U, fit_key_O: the yes, at all three pairs, at both tests: decide
      +kernel. In a proof file at K12's files' written stages szUFull, szOFull and setting
      setAt
  fit_at_scope: so at the sized proof's own setting and stages wherever AtFull holds (K12/Law/Sizes/
      StageSizesAtScope.lean: in the goals' scope by atFull_of_publicO)
  spare_real, spare_key: HOW MUCH ROOM: at o_u against the test on G_u, and at o_omega against the
      test
      on G_omega, the two radii are ONE number: e < e + 1: nothing to spare
  least_real, least_key: EACH OF THE THREE RADII IS THE LEAST THAT PASSES: with o_u's one less the
      test
      on G_u says no; with o_omega's, or the mask message's, one less the test on G_omega says no
  teeth_real, teeth_key: with all three one less both tests say no

What is not claimed. That a written stage a at a seated description has the first stage's numbers.
That the members' list at the seat holds these pairs. The laws that spend the premise. The full size
alone. Nothing on soundness of a verifier, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14OwnAt
import Johnson.Desc.K12.Law.CondAtMade
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Johnson.G
open Johnson.Pack (aOf)
open Johnson.Top.H (stageOf)
open H2K.Pub (radBy sgOf)
open H2K.Sizes (AtFull)
open H2K.Member (setAt szUFull szOFull)
open VerifiableInference.Desc.K1
open Lk6.AtPlan (keyFull)

/-- **The test.** -/
def fitB (σ : Setting) (st : List StageSize) (cs : Codes) (l : List (OracleShape × ℕ)) : Bool :=
  match st with
  | [] => false
  | y :: _ => l.all fun m =>
      decide (radBy σ st (stageOf y.g y.t) < (m.2 + 1) * 2 ^ ((stageOf y.g y.t).C.a - aOf cs m.1))

/-- **From a yes: the premise, sign for sign.** -/
theorem fit_of {σ : Setting} {y : StageSize} {rest : List StageSize} {cs : Codes}
    {l : List (OracleShape × ℕ)} (h : fitB σ (y :: rest) cs l = true) (a : Fmt.M1.Stage)
    (ha : sgOf a = stageOf y.g y.t) (sh : OracleShape) (e0 : ℕ) (hm : (sh, e0) ∈ l) :
    radBy σ (y :: rest) (sgOf a) < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf cs sh) := by
  rw [ha]
  exact of_decide_eq_true (List.all_eq_true.1 h (sh, e0) hm)

/-- The pairs (shape, radius) of the written records of the shared chain's first two sendings. -/
def membersOf (fl : ℕ) : List (OracleShape × ℕ) :=
  ((litAt sendsFullLit packFullLit fl 1).take 2).flatMap (·.2.l)

theorem members_three : (membersOf 2).length = 3 ∧ (membersOf 0).length = 3 := by decide +kernel

theorem fit_real_U : fitB setAt szUFull codesFull2 (membersOf 2) = true := by decide +kernel

theorem fit_real_O : fitB setAt szOFull codesFull2 (membersOf 2) = true := by decide +kernel

theorem fit_key_U :
    fitB recordSet keyFull.once.folded.stages keyFull.codes (membersOf 0) = true := by
  decide +kernel

theorem fit_key_O :
    fitB recordSet keyFull.once.omega.stages keyFull.codes (membersOf 0) = true := by
  decide +kernel

/-- **At the sized proof's own setting and stages.** -/
theorem fit_at_scope {M : Configured} (h : AtFull M) :
    fitB M.sized.proof.set M.sized.proof.batch.folded.stages codesFull2 (membersOf 2) = true ∧
      fitB M.sized.proof.set M.sized.proof.batch.omega.stages codesFull2 (membersOf 2) = true := by
  rw [h.setP, h.U, h.O]
  exact ⟨fit_real_U, fit_real_O⟩

/-- The first stage's radius, by K12's files' term radBy. -/
def firstRad (σ : Setting) (st : List StageSize) : ℕ :=
  match st with
  | [] => 0
  | y :: _ => radBy σ st (stageOf y.g y.t)

/-- **Nothing to spare**: in a proof file o_u's radius is the radius of the test on G_u, and
o_omega's that of the test on G_omega. -/
theorem spare_real : ((membersOf 2)[0]?).map (·.2) = some (firstRad setAt szUFull) ∧
    ((membersOf 2)[1]?).map (·.2) = some (firstRad setAt szOFull) ∧
    firstRad setAt szUFull = 8342416 ∧ firstRad setAt szOFull = 3131972 := by decide +kernel

/-- The like in a key file. -/
theorem spare_key :
    ((membersOf 0)[0]?).map (·.2) = some (firstRad recordSet keyFull.once.folded.stages) ∧
    ((membersOf 0)[1]?).map (·.2) = some (firstRad recordSet keyFull.once.omega.stages) ∧
    firstRad recordSet keyFull.once.folded.stages = 8342420 ∧
    firstRad recordSet keyFull.once.omega.stages = 3138896 := by decide +kernel

/-- The pairs with the radius of member k one less. -/
def lessAt (k : ℕ) (l : List (OracleShape × ℕ)) : List (OracleShape × ℕ) :=
  l.zipIdx.map fun m => (m.1.1, if m.2 = k then m.1.2 - 1 else m.1.2)

/-- **Each of the three radii is the least that passes**, in a proof file: o_u's at the test on G_u;
o_omega's, and the split's mask message's, at the test on G_omega. -/
theorem least_real : fitB setAt szUFull codesFull2 (lessAt 0 (membersOf 2)) = false ∧
    fitB setAt szOFull codesFull2 (lessAt 1 (membersOf 2)) = false ∧
    fitB setAt szOFull codesFull2 (lessAt 2 (membersOf 2)) = false := by decide +kernel

/-- The like in a key file. -/
theorem least_key :
    fitB recordSet keyFull.once.folded.stages keyFull.codes (lessAt 0 (membersOf 0)) = false ∧
    fitB recordSet keyFull.once.omega.stages keyFull.codes (lessAt 1 (membersOf 0)) = false ∧
    fitB recordSet keyFull.once.omega.stages keyFull.codes (lessAt 2 (membersOf 0)) = false := by
  decide +kernel

/-- The pairs with every radius one less. -/
def lessOne (l : List (OracleShape × ℕ)) : List (OracleShape × ℕ) := l.map fun m => (m.1, m.2 - 1)

/-- **The test can fail.** -/
theorem teeth_real : fitB setAt szUFull codesFull2 (lessOne (membersOf 2)) = false ∧
    fitB setAt szOFull codesFull2 (lessOne (membersOf 2)) = false := by decide +kernel

theorem teeth_key :
    fitB recordSet keyFull.once.folded.stages keyFull.codes (lessOne (membersOf 0)) = false ∧
    fitB recordSet keyFull.once.omega.stages keyFull.codes (lessOne (membersOf 0)) = false := by
  decide +kernel

end Desc.K14.Law

#print axioms Desc.K14.Law.fit_of
#print axioms Desc.K14.Law.members_three
#print axioms Desc.K14.Law.fit_real_U
#print axioms Desc.K14.Law.fit_real_O
#print axioms Desc.K14.Law.fit_key_U
#print axioms Desc.K14.Law.fit_key_O
#print axioms Desc.K14.Law.fit_at_scope
#print axioms Desc.K14.Law.spare_real
#print axioms Desc.K14.Law.spare_key
#print axioms Desc.K14.Law.least_real
#print axioms Desc.K14.Law.least_key
#print axioms Desc.K14.Law.teeth_real
#print axioms Desc.K14.Law.teeth_key
