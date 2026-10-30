-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyJobW.lean: the job at the key file's last proximity test (the own test, piKWFull): the
proof file's jobW (K12/AtProof/JobW.lean) at the key's senders, and its public fields held against
the literals of jobOwn (E2E/KeyTestSizes.lean). On no row.

Why a twin and not a call. jobW names its senders: senderW is the proof file's
⟨⟨1, none, 4, .K1⟩, 0⟩, and senderI K1.firstAddr; the key file's W is sent at piece 14, its index
masks at piece 1. So jobW at the key would name the wrong parts. jobKW is jobW's text with the two
addresses of the key, and one reader lift in the place of readers and wit: both sendings of the key
read one input.

  jobKW          the job
  jobKW_members, jobKW_fresh, jobKW_p   its public fields, by unfolding
  parIK, parWK   the two sendings' parameters at the written sizes of a key, as far as the counts
                 read them: codes and notices. Place, gp and groups are not read by what is held
                 here; gp's samples is written 1, sendingPar's is one.given.plan.samples. parWK
                 takes #[] where linMessageW gives nothing: rides_full shows that it gives
  widthsKB       the trees' depths and words against the place's
  membersKW, freshKW, stagesKW, widthsKW   the held facts: members and fresh against jobOwn's
      literals, the place's stages against stagesOwn, the trees against piKWFull's first list

What can say no. The members' counts (K1's and K14's reckoning, at keyFull) against literals typed
apart; the address of Omega's sender (K14's text) against sOmega; the trees against a list made by
a program off a print. The senders' two addresses are written here from the same literals: they
are true by make, and say only that this text and jobOwn agree.

Letters left: door, and on it the key's last chain's way in; JI.data and JW.data (the vector W at
a filling); lift; ask; n₁, which counts the first chain's challenges. No layFits at this test here.

Limits.
- As JobW.lean's: nothing shows that a row read is the row that the sender sent; no job is laid in a
  filling; its first list of trees is treesW's text, off the proof file's place: widthsKW holds it
  at the key's.
- parIK and parWK stand for sendingPar at keyFull's values (E2E/KeySendJobs.lean, OneFull in
  E2E/KeyBookHeldK1Jobs.lean); that a filling's sendings have them is the caller's. The laws on
  jobKW stand at letters, the held facts at these closed terms: no theorem joins them; Omega's
  member there has n₁ + A.atPoint, here 0: msgOf_atPoint (JobW.lean) closes that.
- Another name jobKW stands in the house (ProofFile.Honest.K12.jobKW, StepsReturnLast.lean): another
  namespace, another type.
- What may be said here on hiding, and no more (a rule of use for whoever builds on this file;
  no theorem), given for the proof file's test at W; with «the witness, » struck for the key's own
  test:
  «The state on entry reads the instance's public part, the rounds shown, and ALL columns opened in
  front of this test, in the order of reading: the first chain's, the shared chain's, the last
  chain's own. They are computed from the index, the stored tables' pads and encoding randomness,
  AND THE RUN's COINS. Never a word on a simulator at this place without «given the instance's
  public part, the rounds shown and all columns opened in front, in all three chains». But for the
  stored tables' columns no one can hand a simulator these from outside: the simulators of EVERY
  part in front must have made them: this test stands last, and its «given» is the whole view in
  front. At a called part of the last chain, at any description, at a stand of the member
  (`StandsAt`), where the plan is fit and `ready` and `runC` return, what the simulators' function
  makes of the run's front is what the way in makes of the state that the run's own fold reaches
  (`stateFromViewOnLastChain_at_stand`), and a read of the two earlier chains finds its words in
  that front (`early_words`; both Johnson/Desc/ProofFile/Honest/K12/Sim2/DoorW.lean). Each read's
  position is among the positions read of its tree (`mem_treeAsks`,
  Johnson/Desc/ProofFile/Honest/Law/Rule/Words.lean). No statement named here ties these to this
  file's job, and that a run returns, calls a part or stands at the member is not shown in these
  files.»
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyLayFits
import E2E.KeyBookHeldK1Jobs
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLay
open H2K.Member (piKWFull)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14.Shape.EndToy (atKey)
open Lk6.AtPlan (keyFull)
open ProofFile.Honest (Addr Front)
open ProofFile.Honest.K14 (SendPub Ask)
open ProofFile.Honest.K12.Light (ManyJob firstsOf memOfSending)
open ProofFile.Honest.K12.AtProof (memK1 msgK1 msgOf shapesW treesW memShape wordsOfTrees senderO)
open AtPublicFiles.KeyTest (sIdx sW sOmega jobOwn stagesOwn)

variable {Wd W X : Type}

/-- **The job at the key file's own test.** jobW's text at the key's senders. JI, JW: the sendings
of the index masks and of W; lift: their input, of the test's. -/
def jobKW (q : P12) (door : W → Front X → T12) (JI JW : ProofFile.Honest.K1.SendJob Wd X)
    (A : SendPub) (lift : W → Wd) (ask : W → Ask) (n₁ : Nat) : ManyJob W X :=
  let JO := ProofFile.Honest.K14.jobOmega ⟨A.P, n₁ + A.atPoint⟩
  let fs := firstsOf (shapesW JI.P JW.P (JO.Q.sent.getD 0 default).shape)
  { p := q
    mems :=
      [memK1 JI lift sIdx (JI.P.sent.size - 1) (fs.getD 0 (none, none)),
       memK1 JW lift sW 0 (fs.getD 1 (none, none)),
       memOfSending JO senderO 0 (fs.getD 2 (none, none)) ask none]
    fresh := some (sW, JW.P.sent.size - 1), rec₀ := door
    trees := treesW q }

section Fields
variable (q : P12) (door : W → Front X → T12) (JI JW : ProofFile.Honest.K1.SendJob Wd X) (A : SendPub)
  (lift : W → Wd) (ask : W → Ask) (n₁ : Nat)

/-- Its parameters. -/
theorem jobKW_p : (jobKW q door JI JW A lift ask n₁).toRun.toTest.p = q := rfl

/-- **Its members**: the index masks' sending's last message; W's message 0; Omega's. -/
theorem jobKW_members : (jobKW q door JI JW A lift ask n₁).toRun.toTest.members =
    [msgK1 sIdx JI.P JI.ride (JI.P.sent.size - 1), msgK1 sW JW.P JW.ride 0,
      msgOf senderO (ProofFile.Honest.K14.jobOmega ⟨A.P, n₁ + A.atPoint⟩) 0] := rfl

/-- The first fresh table is the last message of W's sending. -/
theorem jobKW_fresh : (jobKW q door JI JW A lift ask n₁).toRun.toTest.fresh =
    some (sW, JW.P.sent.size - 1) := rfl

end Fields

/-- The parameters of the index masks' sending at the written sizes. -/
def parIK : VerifiableInference.Desc.K1.Par :=
  { place := ⟨1, none, 1, .K1⟩, codes := keyFull.codes, gp := { samples := 1, firstTree := 0 }
    work := 0, parts := [("the index masks", #[keyFull.once.input])], groups := [] }

/-- The parameters of W's sending at the written sizes. -/
def parWK : VerifiableInference.Desc.K1.Par :=
  { place := ⟨1, none, 14, .K1⟩, codes := keyFull.codes, gp := { samples := 1, firstTree := 0 }
    work := 0
    parts := [("W and what rides with it", (OnBytes.linMessageW keyFull.once.shape).getD #[])]
    groups := [] }

/-- Omega's shape at the key's written sizes. -/
def shapeOK : OnBytes.OracleShape :=
  ((ProofFile.Honest.K14.jobOmega AK).Q.sent.getD 0 default).shape

/-- The trees' depths and words at these shapes, against the place's. -/
def widthsKB : Bool :=
  let sh := shapesW parIK parWK shapeOK
  let fs := firstsOf sh
  let ms := sh.zipIdx.map fun x => memShape x.1 (fs.getD x.2 (none, none))
  wordsOfTrees (piKWFull.nums.stages.headD default) ms (treesW piKWFull) ==
    piKWFull.nums.first.map fun x => (x.1.a, x.1.W)

-- what the two sides hold, as the evaluator read them
#guard jobOwn.members.map (fun m => (m.2.1, m.2.2.f, m.2.2.e)) ==
  [(0, 0, 305), (0, 0, 403), (0, 0, 1177)]
#guard parWK.sent.size == 2
#guard piKWFull.nums.first.map (fun x => (x.1.a, x.1.W)) == [(13, 3), (22, 12), (22, 36)]

/-- **The members are jobOwn's.** -/
theorem membersKW :
    [msgK1 sIdx parIK (fun _ => none) (parIK.sent.size - 1), msgK1 sW parWK AtPublicFiles.KeyBook.rideW 0,
      msgOf senderO (ProofFile.Honest.K14.jobOmega AK) 0] = jobOwn.members := by
  decide +kernel

/-- **The word on the fresh table is jobOwn's.** -/
theorem freshKW : some (sW, parWK.sent.size - 1) = jobOwn.fresh := by
  decide +kernel

/-- **The place's stages are stagesOwn.** -/
theorem stagesKW : piKWFull.nums.stages = stagesOwn := by
  decide +kernel

/-- **The trees' depths and words are the place's.** -/
theorem widthsKW : widthsKB = true := by
  decide +kernel

end AtPublicFiles.KeyLay

#print axioms AtPublicFiles.KeyLay.jobKW
#print axioms AtPublicFiles.KeyLay.jobKW_p
#print axioms AtPublicFiles.KeyLay.jobKW_members
#print axioms AtPublicFiles.KeyLay.jobKW_fresh
#print axioms AtPublicFiles.KeyLay.parIK
#print axioms AtPublicFiles.KeyLay.parWK
#print axioms AtPublicFiles.KeyLay.shapeOK
#print axioms AtPublicFiles.KeyLay.widthsKB
#print axioms AtPublicFiles.KeyLay.membersKW
#print axioms AtPublicFiles.KeyLay.freshKW
#print axioms AtPublicFiles.KeyLay.stagesKW
#print axioms AtPublicFiles.KeyLay.widthsKW
