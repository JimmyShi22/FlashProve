-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLSeatPlaysPremises.lean

It states no goal. No property of the protocol is claimed.

Three public facts at the base prover
(the maker's return A at the filling `onlineProverPartsInUse I secondHashFunction Sz Op`), which the laws on the first
chain's closing proximity test ask as premises.

  `blankGround_at_base`       hG: the ground that the maker returns is the blank ground
  `makersBook_at_base`        hB: the maker's book is what `bookWhole` returns at the written sendings
  `closingTestTies_at_base`   hT of `plays_head_L` (K12/AtFile/ClosingAtHead.lean): the public test
                              on the book's entries for the test's two parts

By what. `atPure_at_laid_ground` (Honest/AtHeadGround.lean); `atPure_book_at_head`
(Honest/K14/AtPureBookAtHead.lean), `sends_in_scope` (Johnson/Goal/Numbers/MadeInScope.lean); `hT_head_L`
(AtFullSide/K12/TiesAtHeadL.lean).

Hypotheses. h: the head. hA: the maker returns A at the base prover's filling. hf: pl is the finish.

Limits. The full size and the format's second hash function alone. Public facts: nothing on a run.
At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER,
whose filling reads this one through the coins' map. The statements at the maker's return are typed
at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot even be written at the online prover's return
(`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`, E2E/TheHonestProver.lean): no law through `OnlineProverParts.through`
is made here.
Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import AtFullSide.K12.TiesAtHeadL
import AtFullSide.K1.FirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (T12)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.K1 (LocB readersB closingB)
open ProofFile.Honest.K12.AtProof (doorAtL membersL finishAt)
open Johnson.G (proofSendsFull)
open P5J (AtMgA TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Sz : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {pl : K2.SwitchPlace}

/-! ## 1 The ground, the book -/

/-- **The ground that the maker returns is the blank ground.** -/
theorem blankGround_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A) :
    ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [eG]
  exact O.blank

/-- **The maker's book is what `bookWhole` returns at the written lists of sendings.** -/
theorem makersBook_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A) :
    bookWhole (P5J.F0T OnBytes.secondHashFunction A.Z Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder) = .ok A.B := by
  have e := K14.atPure_book_at_head h hA
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1] at e
  exact e

/-- **hT: the public test on the book's entries for the test's two parts.** -/
theorem closingTestTies_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) :
    tiesB A.B (H2U.p12OfMade A.Z.made).place (membersL pl).length = true :=
  AtFullSide.K12.hT_head_L h.toAtMg (makersBook_at_base h hA) (blankGround_at_base h hA) hf
    (doorAtL A.Z : LocB W₀ → Front Unit → T12) (widerRows Sz A.Z A.G) (readersB I A.Z)
    (closingB A.Z A.G)

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.blankGround_at_base
#print axioms ProofFile.Honest.K12.LotL.makersBook_at_base
#print axioms ProofFile.Honest.K12.LotL.closingTestTies_at_base
