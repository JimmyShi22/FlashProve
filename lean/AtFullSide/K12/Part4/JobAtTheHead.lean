-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/JobAtTheHead.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the place W):
UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN, AT THE GROUND THAT THE DESCRIPTION's MAKER LAYS,
THE JOB THAT jobRealW RETURNS IS OF THE MAKE THAT THE LAWS ON ITS TREES 0 AND 1 ASK: its first two
members are messages of sendings at the written plans and rides, its trees 0 and 1 have the written
pieces and depths, all public premises hold, and it stands at the place W.

WHAT IT IS NOT.
  * Public facts alone: no coin, no book, no run, no thread, no column.
  * The hypothesis (P5J.AtMgA: the full size and the format's second hash function alone), its opening O and
    "jobRealW returns a job" are premises.
  * At the ground Bs.G₀ of the hypothesis's opening: that a maker's return has that ground is
    another law's.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. Two definitions; six theorems.

  OfTheMake              the make, as a proposition on a job
  writtenRideOfTheIndexMasks   the first sending's ride at the written parameters (the term that
                         AtFullSide/K12/HeldAtHeadW.lean calls rideGF; writtenRideOfW is its rideWF)
  sentFitsUnderTheHead   the closed test says yes at the shared chain's own plan
  jobWIsOfTheMake        jobW is of that make, under eight public equations and the test's yes
  depthsAtTheHead, sendingsAtTheHead, jobRealWIsJobW   under the hypothesis: the two depths; the two
                         sendings' plans and rides; the job is jobW at these
  jobAtTheHeadIsOfTheMake   **the statement**

CALLED. sentFitsAtTheTypedSizes, sentFitsReadsThePlan, sentMembersFitAtJobW, membersOfJobW
(K12/Part4/ColumnsOfJobW.lean). Of other authors: written_at_head, qAt_written (K12/FitAtHead.lean);
stages_at_head (K12/StagesAtHead.lean); nums_head_W (AtFullSide/K12/RestTiesAtHeadW.lean);
msg_w_head, parW_written (K1/Law/FitsAtW.lean); eG_atAll, pin1_atAll; firstRide_head
(AtFullSide/K12/StatedAtHeadW.lean); likeFull_in_scope; p12At_place (K12/AtProof/Places.lean). The
proof's road is omegaAtW_head's (K12/AtFile/WJointHead.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.ColumnsOfJobW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfW
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K12.StagesAtHead
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import AtFullSide.K12.RestTiesAtHeadW
import AtFullSide.K12.StatedAtHeadW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Part4
open VerifiableInference.Desc (Chain Block FileDescription)
open VerifiableInference.Desc.K1 (qAt parGF parWF qFull)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open ProofFile.Honest.K12.Light (ManyJob Mem depthOf)
open ProofFile.Honest.K12.AtProof (memK1 senderI senderW placeW jobRealW jobW fourOf sendPub inOf
  p12At_place idleT12)
open ProofFile.Honest.K14 (SendPub)
open Johnson.G (codesFull2)
open P5J (TS)

/-- The first sending's ride at the written parameters. -/
abbrev writtenRideOfTheIndexMasks : ℕ → Option K1.Ride := K1.rideOf (K1.firstFold qFull)

/-- **The make that the laws on trees 0 and 1 ask of a job.** numberI, numberW, dataI, dataW, liftI,
liftW: what is left free of the two sendings' jobs and of the members' inputs. -/
def OfTheMake {W X WI WW : Type} (M : ManyJob W X) (numberI numberW : ℕ)
    (dataI : WI → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (dataW : WW → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (liftI : W → WI) (liftW : W → WW) : Prop :=
  ∃ f0 f1 mC,
    M.mems =
      [memK1 ⟨parGF, numberI, writtenRideOfTheIndexMasks, dataI⟩ liftI senderI
          (parGF.sent.size - 1) f0,
        memK1 ⟨parWF, numberW, writtenRideOfW, dataW⟩ liftW senderW 0 f1, mC] ∧
    M.trees[0]? = some (13, [.mask 0]) ∧
    M.trees[1]? = some (22, [.main 1, .mask 1, .fresh]) ∧
    SentMembersFit M.s₀ parGF parWF writtenRideOfW f0 f1 ∧ M.p.place = placeW

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The closed test says yes at the shared chain's own plan, under the hypothesis.** -/
theorem sentFitsUnderTheHead (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) (a : ℕ) :
    sentFitsB ⟨qAt Zp Np, a⟩ = true := by
  obtain ⟨y, isTyped, written⟩ := ProofFile.Honest.K12.Light.written_at_head h
  have yes := sentFitsAtTheTypedSizes
  rw [isTyped] at yes
  simp only [Option.all_some] at yes
  rw [sentFitsReadsThePlan, ProofFile.Honest.K12.Light.qAt_written written Np]
  exact yes

/-- **jobW is of that make**, where its two sendings stand at the written plans and rides, its
place's stages and the depths of its trees 0 and 1 are the written ones, it stands at the place W,
and the closed test says yes. -/
theorem jobWIsOfTheMake {W X Xi : Type} (q : VerifiableInference.Desc.K12.P12)
    (door : W → Front X → VerifiableInference.Desc.K12.T12) (JI : K1.SendJob Readers X)
    (JW : K1.SendJob (K1.PlaceIn Xi) X) (A : SendPub) (readers : W → Readers)
    (wit : W → K1.PlaceIn Xi) (ask : W → ProofFile.Honest.K14.Ask) (n₁ : ℕ) (planI : JI.P = parGF)
    (rideI : JI.ride = writtenRideOfTheIndexMasks) (planW : JW.P = parWF)
    (rideW : JW.ride = writtenRideOfW)
    (stages : q.nums.stages = H2K.Member.piWFull.nums.stages) (depth0 : depthOf q 0 = 13)
    (depth1 : depthOf q 1 = 22) (atW : q.place = placeW) (yes : sentFitsB A = true) :
    OfTheMake (jobW q door JI JW A readers wit ask n₁) JI.first JW.first JI.data JW.data readers
      wit := by
  obtain ⟨PI, numberI, rI, dataI⟩ := JI
  obtain ⟨PW, numberW, rW, dataW⟩ := JW
  obtain rfl : PI = parGF := planI
  obtain rfl : rI = writtenRideOfTheIndexMasks := rideI
  obtain rfl : PW = parWF := planW
  obtain rfl : rW = writtenRideOfW := rideW
  refine ⟨_, _, _, membersOfJobW q door _ _ A readers wit ask n₁, ?_, ?_,
    sentMembersFitAtJobW q door _ _ A readers wit ask n₁ rfl rfl rfl stages yes, atW⟩
  · show some (depthOf q 0, [ProofFile.Honest.K12.Light.Piece.mask 0]) = _
    rw [depth0]
  · show some (depthOf q 1, [ProofFile.Honest.K12.Light.Piece.main 1, .mask 1, .fresh]) = _
    rw [depth1]

variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x) {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

omit O in
/-- Under the hypothesis the depths of trees 0 and 1 at the seated place are the written ones. -/
theorem depthsAtTheHead : depthOf (fourOf Np).W 0 = 13 ∧ depthOf (fourOf Np).W 1 = 22 := by
  unfold depthOf
  rw [ProofFile.Honest.K12.Light.nums_head_W h.toAtMg]
  exact ⟨rfl, rfl⟩

/-- Under the hypothesis the two sendings' jobs stand at the written plans and rides. -/
theorem sendingsAtTheHead {Xi X : Type} (S : OnBytes.HonestTrace.Sz) (number : ℕ)
    (data : RowDataOf Xi) :
    (K1.firstJob (X := X) S Zp Bs.G₀).P = parGF ∧
      (K1.firstJob (X := X) S Zp Bs.G₀).ride = writtenRideOfTheIndexMasks ∧
      (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 wMsgFull number data).P = parWF ∧
      (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 wMsgFull number data).ride = writtenRideOfW :=
  ⟨VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h),
    (firstRide_head h O).trans (K1.firstRide_eq qFull), ProofFile.Honest.K1.parW_written h O,
    congrArg (fun lin => K1.rideOf (K1.wFold lin))
      (VerifiableInference.Desc.K13.Law.likeFull_in_scope h.scope h.laid.pub
        (VerifiableInference.Desc.K1.pin1_atAll h)).lin⟩

/-- Under the hypothesis the job that jobRealW returns is jobW at the seated place, the two
sendings' jobs and public data whose plan is the shared chain's own. -/
theorem jobRealWIsJobW {W₀ Rc Xi Tr X : Type} (S : OnBytes.HonestTrace.Sz)
    (Fd : FileDescription Xi) (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → ℕ)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand)
    {M : ManyJob (Local W₀ Rc Xi Tr) X}
    (made : jobRealW S Fd enter pile no readers weights rand Zp Bs.G₀ = some M) :
    ∃ A : SendPub, A.P = qAt Zp Np ∧
      M = jobW (fourOf Np).W (ProofFile.Honest.K12.Light.doorW Fd (·.x) enter placeW idleT12)
        (K1.firstJob S Zp Bs.G₀)
        (K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩)
          (K13.wDataAt pile Zp Bs.G₀))
        A readers (inOf readers) (ProofFile.Honest.K12.Light.askOf A weights (rand A.P))
        (Fd.first.blocksInOrder.flatMap (·.rounds)).length := by
  unfold jobRealW at made
  obtain ⟨F, isFour, made⟩ := Option.bind_eq_some_iff.1 made
  obtain ⟨A, isPublic, made⟩ := Option.bind_eq_some_iff.1 made
  obtain ⟨msg, isMessage, rfl⟩ := Option.map_eq_some_iff.1 made
  obtain ⟨places, -⟩ := ProofFile.Honest.K12.Light.stages_at_head h.toAtMg
  obtain rfl : F = fourOf Np := Option.some.inj (isFour.symm.trans places)
  obtain rfl : msg = wMsgFull :=
    Option.some.inj (isMessage.symm.trans (ProofFile.Honest.K1.msg_w_head h O))
  refine ⟨A, ?_, rfl⟩
  unfold sendPub at isPublic
  rw [(ProofFile.Honest.K14.readers_at Zp Np h.laid.places).1] at isPublic
  change Option.map _ _ = some A at isPublic
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 isPublic
  rfl

/-- **The job that jobRealW returns at the hypothesis's ground is of the make that the laws on its
trees 0 and 1 ask.** The two members' data are the two sendings' jobs' own. -/
theorem jobAtTheHeadIsOfTheMake {W₀ Rc Xi Tr X : Type} (S : OnBytes.HonestTrace.Sz)
    (Fd : FileDescription Xi) (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → ℕ)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand)
    {M : ManyJob (Local W₀ Rc Xi Tr) X}
    (made : jobRealW S Fd enter pile no readers weights rand Zp Bs.G₀ = some M) :
    OfTheMake M (K1.firstJob (X := X) S Zp Bs.G₀).first
      (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩)
        (K13.wDataAt pile Zp Bs.G₀)).first
      (K1.firstJob (X := X) S Zp Bs.G₀).data
      (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩)
        (K13.wDataAt pile Zp Bs.G₀)).data readers (inOf readers) := by
  obtain ⟨A, plan, rfl⟩ := jobRealWIsJobW h O S Fd enter pile no readers weights rand made
  obtain ⟨planI, rideI, planW, rideW⟩ := sendingsAtTheHead (X := X) h O S (no ⟨1, none, 4, .K1⟩)
    (K13.wDataAt pile Zp Bs.G₀)
  obtain ⟨depth0, depth1⟩ := depthsAtTheHead h
  have yes : sentFitsB A = true := by
    rw [sentFitsReadsThePlan, plan, ← sentFitsReadsThePlan ⟨qAt Zp Np, 0⟩]
    exact sentFitsUnderTheHead h.toAtMg 0
  exact jobWIsOfTheMake _ _ _ _ A readers (inOf readers) _ _ planI rideI planW rideW
    (ProofFile.Honest.K12.Light.stages_at_head h.toAtMg).2.2.2.1 depth0 depth1 (p12At_place _ _) yes

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.sentFitsUnderTheHead
#print axioms AtFullSide.K12.Part4.jobWIsOfTheMake
#print axioms AtFullSide.K12.Part4.depthsAtTheHead
#print axioms AtFullSide.K12.Part4.sendingsAtTheHead
#print axioms AtFullSide.K12.Part4.jobRealWIsJobW
#print axioms AtFullSide.K12.Part4.jobAtTheHeadIsOfTheMake
