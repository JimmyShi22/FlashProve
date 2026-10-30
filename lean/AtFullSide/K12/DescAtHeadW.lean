-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/DescAtHeadW.lean: UNDER THE LIBRARY's HEAD (`P5J.AtMgA`: a hypothesis), WHERE
`onlineProverFromPublicFiles` RETURNS AT THE WIDE FILLING (hA: a hypothesis): THE DESCRIPTION THAT `onlineProverFromPublicFiles` MAKES IS
THE ONE THAT THE PAIR's DOOR AND TEST SPEAK OF: `P5J.F0T OnBytes.secondHashFunction Zp Np cF`.
Of HalfW.lean's eight letters: Fd against Z.

  `second_is_secondW`   the filling's field `second` is `secondW`, by rfl
  `filling_at_head`   what `onlineProverFromPublicFiles` returns has the head's public part and description; where the
                 six are made its prover's `second` is `halfW` at that description, at `enterOwn`,
                 at `secondW`'s letters, at that public part and ground

So `door_own_at_called` and `atHandW_at_run`, whose letters B and P are free, speak of the filling's
own runs: at B and H of the first clause. By what: `atPure_is` (Honest/AtHead.lean); the head's
`places`; `LaidAt.chain` (Johnson/P5J/ChainFree.lean); `secondW_letters` (WMemberSent.lean).

Limits.
- THAT `onlineProverFromPublicFiles` RETURNS AT THIS FILLING IS A PREMISE HERE: `atPure_returns_fillW₀`
  (AtFullSide/K12/ReturnsAtFillW.lean) has it at the reader fullIn, under the head and the test
  `protocolDataWellFormed`.
- hs: that the six are made is a premise.
- o := OnBytes.secondHashFunction alone. One named filling, at `LongLots.plain`.
- The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
- What may be said of this pair on hiding stands in the head of
  Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfW.lean.
- The full size alone. It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WMemberSent
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open ProofFile.Honest ProofFile.Honest.K12.AtProof
open P5J (TS)

variable {W₀ : Type}

/-- The filling's field `second` is `secondW`. -/
theorem second_is_secondW (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : (onlineProverPartsInUse I o S O).second = secondW I o S O := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT `onlineProverFromPublicFiles` RETURNS AT THE WIDE FILLING HAS THE HEAD's PUBLIC PART AND DESCRIPTION**, and
where the six are made its prover's `second` is the pair at that description. -/
theorem filling_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)}
    (hs : nowSharedBy (I.weights Zp) Zp = .ok six) :
    (∃ G B H rd rw, A = ⟨Zp, G, P5J.F0T OnBytes.secondHashFunction Zp Np cF, B, H, rd, rw⟩) ∧
      A.H.second =
        halfW S (P5J.F0T OnBytes.secondHashFunction Zp Np cF) VerifiableInference.Desc.K12.Seat.enterOwn O.pile
          (K1.lotNo OnBytes.secondHashFunction Zp) (lettersW I Zp) (fun w => I.weights Zp w.w₀)
          (fun P w => randAt P w.rc) Zp A.G := by
  have hZ := (atPure_at_laid h.laid hA).1
  obtain ⟨-, -, -, -, -, -, -, -, -, h2, -⟩ := atPure_ok hA
  refine ⟨atPure_is h.laid hA, ?_⟩
  rw [h2, hZ]
  exact secondW_letters I OnBytes.secondHashFunction S O A.G hs h.laid.places h.laid.chain

end AtFullSide.K12

#print axioms AtFullSide.K12.second_is_secondW
#print axioms AtFullSide.K12.filling_at_head
