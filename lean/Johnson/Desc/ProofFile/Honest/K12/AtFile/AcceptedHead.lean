-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/AcceptedHead.lean: `AcceptedS` at member 9 of a shared thread at the
proof file: K12At's five fields at a stand, where `SaysAt` holds at every coin lent.

  `acceptedS_head_U`   the statement

By what. `acceptedS_at_test` (AcceptedAtTest.lean); `agree_head_U`, `count_of_plan`, `enters_at_nine`
(FieldsAtU.lean); `opens_head_U` (TreesSentBeforeTestAtU.lean); `accepts_head_U` (AcceptedAtU.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS.
- hsay is the one premise on values: `says_head_U` (AcceptedAtNine.lean) pays it.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtU

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace treesU)
open ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place OpenedColumn noDigest)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks frontBlock withU first)
open Desc.K14.Honest (Like)
open Johnson.G (proofSendsFull codesFull2)

open H2K.Member (piUFull)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (jobAtU doorUF colsLoc sentOf SaysAt bookCutsU dataThree_head shape_head_UF
  five_head ts_head planB_head formPubB_head ts_of_front colsMany plainMany alike_head_U
  planOk_head_U ManyJob)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

section
variable {W₀ Rc X₀ Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- **It is accepted, at member 9**, where `SaysAt` holds at every coin lent. -/
theorem acceptedS_head_U (h : P5J.AtMg o Z D r Zp Np cF)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb) (Said : ℕ → Coins Bk → Mid _ X₀ → Prop)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (c₀ : OnBytes.Model.Verify.Chains) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hU : withU (K1.qAt Zp Np).S = some (sentOf (K1.qAt Zp Np).S))
    (hpre : List.Forall₂ Like (T.bs.take 9) [frontBlock c₀, b1, b2, b3, b4, b5, b6, b7, b8])
    (hah : T.ahead = []) (hch : T.chain = 1) (hft : T.ft = 0)
    (hbeg : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = first (K1.qAt Zp Np).codes w.key)
    (hst : ∀ w, T.stored w = st w.w₀ w.rc)
    {blk : Block St Cl} (hblk : T.bs[9]? = some blk)
    (hseat : SeatOf blk (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest
      (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave)
    (hf : (T.hs.find? fun g => g.place == (fourOf Np).U.place) =
      some (proverSideOfProximityTest (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest))
    (hbt : treesTo T.bs 9 = 3) (ht : T.taken = [])
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (hf1 : 1 ≤ T.fixed (.own 0)) (hu : treesU (K1.qAt Zp Np) = 1)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (fall : ℕ → St → List Fmt.Drawn → Option String)
    (hsay : ∀ k s m E (c : RowCoins
        [(firstPart (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest :
          Part V _ _),
        restPart (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest]),
      ThrS T Said 9 k s m E →
      lendRow Bk (Bk.rowsOf 1) (k.look 1) (fourOf Np).U.place
        [(firstPart (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest :
          Part V _ _),
        restPart (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest] 0 = .ok c →
      SaysAt (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd) m.st.input (frontOf m)
        (restCoins (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest c.2.1)) :
    AcceptedS T Said fall 9 := by
  obtain ⟨s₁, t₁, rest, hstg₀⟩ := stages_head_U h
  have hstg : (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts
      rnd).toRun.toTest.p.nums.stages = s₁ :: t₁ :: rest := hstg₀
  have hk : s₁.k = (sgOf s₁).h + (sgOf s₁).g := by
    have e := k_head_U h
    rw [hstg₀] at e
    exact e
  refine acceptedS_at_test T Said hblk
    (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest
    (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
    VerifiableInference.Desc.K12.Seat.leave hseat s₁ t₁ rest hstg hk hf fall ?_
  intro k s m E ds c u hd _ hc
  rw [hch] at hc
  have ag := agree_head_U (V := V) h hB
    (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] (fun w => w.key)
      (fun w fr => colsLoc (K1.qAt Zp Np) (st w.w₀ w.rc) fr.seen.rounds))
    (fun c => wts c.w₀) (fun c => rnd c.rc) (Bk.rowsOf 1) (k.look 1) c hc m.st.input (frontOf m)
  have ct := count_of_plan
    (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest s₁ (t₁ :: rest) 3
    (planPlays_head_U h _ rfl rfl s₁ (t₁ :: rest) hstg) m.st.input (frontOf m)
    (restCoins (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest c.2.1)
    (byNo ds)
  have op := opens_head_U h T wts rnd JU JO own₀
    (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] (fun w => w.key)
      (fun w fr => colsLoc (K1.qAt Zp Np) (st w.w₀ w.rc) fr.seen.rounds))
    hbt ht htb hf1 hu c2 c5 (AtFullSide.K12.bookCutsU_head h hB) u.1 c hc
  have en := enters_at_nine T c₀ (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) b1 b2 b3 b4 b5 b6 b7 b8 hb hU
    hpre hah hch hft hbeg st hst u.1
  have ac := accepts_head_U h [b1, b2, b3, b4, b5, b6, b7, b8] hb (fun w => w.key)
    (fun w fr => colsLoc (K1.qAt Zp Np) (st w.w₀ w.rc) fr.seen.rounds) (fun c => wts c.w₀)
    (fun c => rnd c.rc) none m.st.input (frontOf m)
    (restCoins (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest c.2.1)
    ds
  have hs := hsay k s m E c u hc
  have ac2 := ac hd hs
  obtain ⟨t', ht'⟩ := ac2
  have hl : ∃ s', VerifiableInference.Desc.K12.Seat.leave s t' = .ok s' := ⟨_, rfl⟩
  exact ⟨ag, ct, op, en, t', ht', hl⟩


end

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.acceptedS_head_U
