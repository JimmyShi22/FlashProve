-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookLineAtBase.lean

It states no goal. No property of the protocol is claimed.

The public test `wordsBookB` says yes at the base
prover's return: the premise hbook of `wordsTied_at_first_thread` (LotLScriptThread.lean), to the letter,
by the light road (LotLBookLine.lean): no closed line over the book's whole written list is beneath.

  `wordsBookB_at_base`

By what. `wordsBookB_at_makers_book` (LotLBookLine.lean); `makersBook_at_base`, `blankGround_at_base`
(LotLSeatPlaysPremises.lean).

Hypotheses. h: the head at A's public part. hA: the maker returns A at the base prover's filling. hf: pl is
the finish at A's ground.

Limits. LotLBookLine.lean's stand. The full size and the format's second hash function alone. A public fact:
nothing on a run.
At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER,
whose filling reads this one through the coins' map. The statements at the maker's return are typed
at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot even be written at the online prover's return
(`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`, E2E/TheHonestProver.lean): no law through `OnlineProverParts.through`
is made here.
Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatPlaysPremises

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.K12.LotL (makersBook_at_base blankGround_at_base)
open P5J (AtMgA TS)

/-- **At the base prover's return**: the premise hbook of `wordsTied_at_first_thread`. -/
theorem wordsBookB_at_base {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {I : WiderIn W₀}
    {Sz : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    {pl : K2.SwitchPlace} (hf : finishAt A.Z A.G = some pl) :
    wordsBookB A.B ⟨pl.place, 0⟩ ⟨(H2U.p12OfMade A.Z.made).place, 1⟩ pl.front.length = true :=
  wordsBookB_at_makers_book h.toAtMg (makersBook_at_base h hA) (blankGround_at_base h hA) hf

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.wordsBookB_at_base
