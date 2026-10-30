-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/SecondMadeW.lean: «second ≠ []»: UNDER THE LIBRARY's HEAD AND ITS TEST, THE PROVER
THAT `onlineProverFromPublicFiles` RETURNS AT THE WIDE FILLING HOLDS THE LAST CHAIN's PAIR: the job is made and the
field is one job's pair behind the guard.

  `realW_made`   under the head `realW` returns: `four`, `sendPub`, `linMessageW` are had
  `second_made`   `secondW` is that job's pair behind the guard
  `second_ne_nil`   at `onlineProverFromPublicFiles`'s prover: `A.H.second` is no empty list

By what. `nowSharedBy_at_head` (K14/AtWiderShared.lean); `stages_at_head`, `msg_w_head`; `one_A`
(OmegaMemberSent.lean); `filling_at_head` (DescAtHeadW.lean); `atPure_returns_fillW₀`
(ReturnsAtFillW.lean).

Limits.
- Having a side is no ground that it plays. `ready`'s tests are not read here.
- The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
- The full size alone. It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.ReturnsAtFillW
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared
import Johnson.Desc.ProofFile.Honest.K12.AtProof.OmegaMemberSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Block Chain Place FileDescription)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile (Pub Ground SecondHashFunctionArgument)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **Under the head `realW` returns**, at every choice of its letters but the sendings' readers:
wt: the index's reader by which `one_A` reads `sendPub`. -/
theorem realW_made {W₀ Xi Rc Tr X : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Op : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (wt : W₀ → Weights) (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi)
    (enter : Fd.S₃ → Except String T12) (pile : Pub → Ground → K13.PileOf Xi)
    (no : Place → Nat) (readers : Local W₀ Rc Xi Tr → Readers)
    (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (G : Ground) :
    ∃ J : TestJob (Local W₀ Rc Xi Tr) X,
      realW S Fd enter pile no readers weights rand Zp G = some J := by
  have h6 := ProofFile.Honest.K14.nowSharedBy_at_head h wt
  obtain ⟨A, -, hA, -⟩ := one_A wt Zp h6
  have hf := (ProofFile.Honest.K12.Light.stages_at_head h.toAtMg).1
  have hm := ProofFile.Honest.K1.msg_w_head h Op
  unfold realW jobRealW
  rw [hf]
  simp only [Option.bind_some, hA, hm, Option.map_some]
  exact ⟨_, rfl⟩

/-- **`secondW` is `realW`'s job's pair behind the guard.** -/
theorem second_made {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Op : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (G : Ground) :
    ∃ J : TestJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit,
      realW S (P5J.F0T OnBytes.secondHashFunction Zp Np cF) VerifiableInference.Desc.K12.Seat.enterOwn O.pile
        (K1.lotNo OnBytes.secondHashFunction Zp) (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩)
        (fun w => I.weights Zp w.w₀) (fun P w => randAt P w.rc) Zp G = some J ∧
      (secondW I OnBytes.secondHashFunction S O Zp G : List (Placed _ _ Unit)) =
        [(proverSideOfProximityTest J : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) _ Unit).needsField] := by
  have h6 := ProofFile.Honest.K14.nowSharedBy_at_head h (I.weights Zp)
  rw [secondW_ok I OnBytes.secondHashFunction S O G h6 h.laid.places h.laid.chain]
  obtain ⟨J, hJ⟩ := realW_made (X := Unit) h Op (I.weights Zp) S
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF) VerifiableInference.Desc.K12.Seat.enterOwn O.pile
    (K1.lotNo OnBytes.secondHashFunction Zp) (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩)
    (fun w => I.weights Zp w.w₀) (fun P w => randAt P w.rc) G
  refine ⟨J, hJ, ?_⟩
  unfold halfW
  rw [hJ]
  rfl

/-- **«second ≠ []»: `onlineProverFromPublicFiles`'s prover holds the last chain's pair.** CONDITIONAL: h, hl. -/
theorem second_ne_nil (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
        (onlineProverPartsInUse fullIn OnBytes.secondHashFunction S O) = .ok A ∧ A.H.second ≠ [] := by
  obtain ⟨A, hA, eZ, -, -⟩ := atPure_returns_fillW₀ h hl OnBytes.secondHashFunction S O
  obtain ⟨Bs', base', Op⟩ := h.laid.opened
  obtain ⟨-, -, -, -, -, -, -, -, -, h2, -⟩ := atPure_ok hA
  refine ⟨A, hA, ?_⟩
  rw [h2, eZ]
  obtain ⟨J, -, hJ⟩ := second_made h Op fullIn S O A.G
  show secondW fullIn OnBytes.secondHashFunction S O Zp A.G ≠ []
  rw [hJ]
  exact List.cons_ne_nil _ _

end AtFullSide.K12

#print axioms AtFullSide.K12.realW_made
#print axioms AtFullSide.K12.second_made
#print axioms AtFullSide.K12.second_ne_nil
