-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/CoreMems.lean: the members' public numbers of the last chain's job at
the base prover are those of the written sendings: the premises `hm` and `ht` of `lines_of_narrow` (CoreNarrow.lean).

  `mems_lit`       at the filling: the job's members' numbers are `memsW` and its trees `treesW` at the
                   written place

By what. Under the head the three sendings are written: `eG_atAll`, `parW_written`, `msg_w_head`; Omega's by
`qAt_written`.

Limits. Under the head and at `onlineProverFromPublicFiles`'s return. Public numbers alone. Nothing on a run. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.CoreShapes
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtHead
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open H2K.Member (piWFull)
open ProofFile.Honest.K12.Light (ManyJob memOfSending nums_head_W written_at_head qAt_written)
open P5J (F0T TS AtMgA)
open AtFullSide.K12 (jobAtFill ground_at_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ : Type}

/-- **The job's members' numbers are the printed ones.** -/
theorem mems_lit (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill Zp Np cF I S O A.G = some M) :
    M.mems.map (·.shape) = memsW ∧ M.trees = treesW piWFull := by
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have eG := ground_at_head h.laid Op hA
  obtain ⟨y, hy, Wr⟩ := written_at_head h.toAtMg
  unfold jobAtFill jobRealW at hM
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨An, hAn, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hM
  obtain rfl : F = fourOf Np :=
    Option.some.inj (hF.symm.trans (ProofFile.Honest.K12.Light.stages_at_head h.toAtMg).1)
  obtain rfl : msg = VerifiableInference.Desc.K13.Law.wMsgFull :=
    Option.some.inj (hmsg.symm.trans (ProofFile.Honest.K1.msg_w_head h Op))
  have eP : An.P = VerifiableInference.Desc.K1.qAt Zp Np := by
    unfold sendPub at hAn
    rw [(ProofFile.Honest.K14.readers_at Zp Np h.laid.places).1] at hAn
    change Option.map _ _ = some An at hAn
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hAn
    rfl
  have eI : VerifiableInference.Desc.K1.firstPar A.G.first (VerifiableInference.Desc.K1.gpOf Zp) =
      VerifiableInference.Desc.K1.parGF := by
    rw [eG]
    exact VerifiableInference.Desc.K1.eG_atAll h Op (VerifiableInference.Desc.K1.pin1_atAll h)
  have eW := ProofFile.Honest.K1.parW_written h Op
  have eO : ((ProofFile.Honest.K14.jobOmega ⟨An.P, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap
            (·.rounds) |>.length |> (· + An.atPoint)⟩).Q.sent.getD 0 default).shape =
      ((Desc.K14.withOmega y.shape).getD 0 default).shape := by
    rw [eP, qAt_written Wr Np]
    simp [ProofFile.Honest.K14.jobOmega, Desc.K14.parK1, VerifiableInference.Desc.K1.Par.sent]
  refine ⟨?_, ?_⟩
  · show memsOf [Johnson.Prover.Send.shapeAt (VerifiableInference.Desc.K1.firstPar A.G.first
        (VerifiableInference.Desc.K1.gpOf Zp))
        ((VerifiableInference.Desc.K1.firstPar A.G.first
          (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1),
      Johnson.Prover.Send.shapeAt (VerifiableInference.Desc.K1.parW Zp.first (K1.wGp Zp) 4
        VerifiableInference.Desc.K13.Law.wMsgFull) 0,
      ((ProofFile.Honest.K14.jobOmega ⟨An.P, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap
              (·.rounds) |>.length |> (· + An.atPoint)⟩).Q.sent.getD 0 default).shape] = memsW
    rw [eI, eW, eO]
    unfold memsW
    rw [hy]
    rfl
  · show treesW (fourOf Np).W = treesW piWFull
    unfold treesW ProofFile.Honest.K12.Light.depthOf
    rw [nums_head_W h.toAtMg]

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.mems_lit
