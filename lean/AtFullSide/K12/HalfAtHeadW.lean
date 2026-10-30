-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/HalfAtHeadW.lean: THE REQUEST's OWN PROXIMITY TEST (the place W), THE FULL SIZE,
UNDER THE LIBRARY's HEAD (`P5J.AtMgA` and `IM.Open`: hypotheses): THE JOB `realW` HAS THE PUBLIC
FIELDS THAT LendsAtHeadW.lean ASKS, AND THE FRAME LENDS THE PAIR BEHIND THE GUARD ITS COINS. PUBLIC
DATA ALONE.

  `firstRide_written`   the first opening's two texts of its ride are one at the written plan
  `lendRow_W_guard`   `lendRow_W` through the guard (FieldGuard.lean): the guard keeps a part's
                 counts and names
  `realW_public`   UNDER THE HEAD: place, members, fresh table, stages of the job that `realW`
                 returns
  `halfW_lent`   UNDER THE HEAD: each side that `halfW` returns at the head's ground is lent its
                 row, at every run's coins

Limits.
- `halfW_lent` is over `g ∈ halfW …`: where `halfW` is [] it says nothing. That `realW` returns is
  a premise here: `sendPub_at_head` (AtProof/HalfAtPure.lean) is not called.
- The eight letters of `jobRealW` stay letters; `hm` here does not read them: the group's public
  numbers are the senders' at any of them.
- WHAT IS HANDED IS NOT DESCRIBED. No filling is named. All limits of LendsAtHeadW.lean, JobW.lean
  and HalfW.lean stand.
- `halfW` asks no test on the shape: `askOf` reads `rowsOf`, and at a shape whose matrix's places
  run into the pads an entry of the matrix lies where a pad of the index committer is due
  (JobShared.lean), at Omega's member here as at O. Under the library's head the shape of the shared
  chain passes `LinShape.ok` (`linOk_at_head`,
  Johnson/Desc/ProofFile/Honest/K14/SendingsAtFilling.lean, with `linOk_ok`).
- What may be said of this pair on hiding stands in the head of
  Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfW.lean.
- The full size alone. It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.LendsAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain Block FileDescription)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piWFull)
open P2Law.ProofPlan (WP wp_placesOk)
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (bookWhole_returns_written_ahead)
open P5J (TS)

variable {V W X : Type}

set_option maxRecDepth 1000000 in
/-- **The first opening's two rides are one at the written plan**: `K1.firstRide`, that `firstJob`
and `membersW` read, and the filling's sender's `rideOf (firstFold …)`, at each of its messages. An
evaluation in Lean's kernel. -/
theorem firstRide_written :
    (List.range VerifiableInference.Desc.K1.parGF.sent.size).map
        (ProofFile.Honest.K1.firstRide VerifiableInference.Desc.K1.qFull) =
      (List.range VerifiableInference.Desc.K1.parGF.sent.size).map
        (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.firstFold VerifiableInference.Desc.K1.qFull)) := by
  decide +kernel

/-- hB is a premise. **THE FRAME LENDS THE PAIR BEHIND THE GUARD**: the guard keeps what a part
takes, spends and carries. -/
theorem lendRow_W_guard {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (J : TestJob W X) (hp : J.p.place = placeW)
    (hm : J.members = membersWF) (hf : J.fresh = some (senderW, 1))
    (hs : J.p.nums.stages = piWFull.nums.stages) (k : Coins B) :
    ∃ c, lendRow B (B.rowsOf 2) (k.look 2) placeW
        (proverSideOfProximityTest J : Placed V W X).needsField.parts 0 = .ok c :=
  lendRow_of_fit (F := WP) (bookWhole_word hB) wp_placesOk (ch := 2) (Or.inr (Or.inr rfl))
    placeW_in_WP k _ 0 fun i p hq => by
      rw [Nat.zero_add]
      have hq' : ((proverSideOfProximityTest J : Placed V W X).parts.map Part.needsField)[i]? = some p := hq
      rw [List.getElem?_map] at hq'
      obtain ⟨q, hq₁, rfl⟩ := Option.map_eq_some_iff.1 hq'
      exact fit_W hB J hp hm hf hs i q hq₁

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Xi Tr : Type}

variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x) {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- **Under the head the job that `realW` returns has the public fields** that the lending asks. -/
theorem realW_public (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi)
    (enter : Fd.S₃ → Except String T12) (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi)
    (no : VerifiableInference.Desc.Place → Nat) (readers : Local W₀ Rc Xi Tr → Readers)
    (weights : Local W₀ Rc Xi Tr → Weights) (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand)
    {J : TestJob (Local W₀ Rc Xi Tr) X}
    (hJ : realW S Fd enter pile no readers weights rand Zp Bs.G₀ = some J) :
    J.p.place = placeW ∧ J.members = membersWF ∧ J.fresh = some (senderW, 1) ∧
      J.p.nums.stages = piWFull.nums.stages := by
  unfold realW jobRealW at hJ
  obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1 hJ
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, hA, hM⟩ := Option.bind_eq_some_iff.1 hM
  rw [ProofFile.Honest.K1.msg_w_head h O] at hM
  obtain rfl := Option.some.inj hM
  obtain ⟨hf, -, -, hW, -⟩ := ProofFile.Honest.K12.Light.stages_at_head h.toAtMg
  obtain rfl : F = fourOf Np := Option.some.inj (hF.symm.trans hf)
  have eA : A.P = VerifiableInference.Desc.K1.qAt Zp Np := by
    unfold sendPub at hA
    rw [(ProofFile.Honest.K14.readers_at Zp Np h.laid.places).1] at hA
    change Option.map _ _ = some A at hA
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hA
    rfl
  have ho : omegaDueB ⟨A.P, (Fd.first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩ = true := by
    rw [eA]
    exact omegaDue_head h.toAtMg _
  have eO : ProofFile.Honest.K12.AtProof.msgOf senderO (ProofFile.Honest.K14.jobOmega
            ⟨A.P, (Fd.first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩) 0 = rowOF := by
    unfold omegaDueB at ho
    have e := beq_iff_eq.1 ho
    unfold ProofFile.Honest.K12.AtProof.msgOf rowOF
    rw [e]
  have eR : ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold Zp.first.lin) 0 = none := by
    rw [ProofFile.Honest.K1.ride_w_head h O]
    decide +kernel
  have eW : msgK1 senderW (VerifiableInference.Desc.K1.parW Zp.first (ProofFile.Honest.K1.wGp Zp) 4
      VerifiableInference.Desc.K13.Law.wMsgFull)
      (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold Zp.first.lin)) 0 = rowWF := by
    unfold rowWF msgK1
    rw [eR, ProofFile.Honest.K1.parW_written h O]
  have eI : msgK1 senderI (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp)) (ProofFile.Honest.K1.firstRide Bs.G₀.first)
      ((VerifiableInference.Desc.K1.firstPar Bs.G₀.first
        (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1) = rowIF := by
    rw [VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h),
      firstRide_head h O]
    rfl
  refine ⟨p12At_place _ _, ?_, ?_, hW⟩
  · refine (jobW_members _ _ _ _ _ _ _ _ _).trans ?_
    show [msgK1 senderI (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp)) (ProofFile.Honest.K1.firstRide Bs.G₀.first)
          ((VerifiableInference.Desc.K1.firstPar Bs.G₀.first
            (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1),
        msgK1 senderW (VerifiableInference.Desc.K1.parW Zp.first (ProofFile.Honest.K1.wGp Zp) 4
          VerifiableInference.Desc.K13.Law.wMsgFull)
          (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold Zp.first.lin)) 0,
        ProofFile.Honest.K12.AtProof.msgOf senderO (ProofFile.Honest.K14.jobOmega
                ⟨A.P, (Fd.first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩) 0] = membersWF
    rw [eI, eW, eO]
    rfl
  · refine (jobW_fresh _ _ _ _ _ _ _ _ _).trans ?_
    have e : (VerifiableInference.Desc.K1.parW Zp.first (ProofFile.Honest.K1.wGp Zp) 4
        VerifiableInference.Desc.K13.Law.wMsgFull).sent.size - 1 = 1 := by
      rw [ProofFile.Honest.K1.parW_written h O]
      decide +kernel
    exact congrArg (fun n => some (senderW, n)) e

/-- hW IS A PREMISE. **UNDER THE HEAD, AT THAT BOOK: EACH SIDE THAT `halfW` RETURNS AT THE HEAD's
GROUND IS LENT ITS ROW, AT EVERY RUN's COINS.** The eight letters are free. -/
theorem halfW_lent {Bk : ProverCoinCounts}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk)
    (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi)
    (enter : Fd.S₃ → Except String T12) (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi)
    (no : VerifiableInference.Desc.Place → Nat) (readers : Local W₀ Rc Xi Tr → Readers)
    (weights : Local W₀ Rc Xi Tr → Weights) (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand)
    {g : Placed V (Local W₀ Rc Xi Tr) X}
    (hg : g ∈ halfW S Fd enter pile no readers weights rand Zp Bs.G₀) (k : Coins Bk) :
    ∃ c, lendRow Bk (Bk.rowsOf 2) (k.look 2) placeW g.parts 0 = .ok c := by
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hg
  obtain ⟨hp, hm, hf, hs⟩ := realW_public h O S Fd enter pile no readers weights rand
    (Option.mem_toList.1 hJ)
  obtain ⟨B₀, h₀, -⟩ := bookWhole_returns_written_ahead
  obtain rfl : Bk = B₀ :=
    Except.ok.inj (hW.symm.trans (ProofFile.Honest.K14.bookWhole_same_at_made h₀ h))
  exact lendRow_W_guard h₀ J hp hm hf hs k

end AtFullSide.K12

#print axioms AtFullSide.K12.firstRide_written
#print axioms AtFullSide.K12.lendRow_W_guard
#print axioms AtFullSide.K12.realW_public
#print axioms AtFullSide.K12.halfW_lent
