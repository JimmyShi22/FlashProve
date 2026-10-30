-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsLeftThree.lean: CONDITIONAL: WHAT IS LEFT OF "THE MAKER
onlineProverFromPublicFiles RETURNS AT THE HEAD's THREE FILES AND THE FILLING widerFillAt": THREE BINDERS BESIDE THE HEAD
AND THE LIBRARY's TEST ON THE HEAD's PUBLIC FILES.

Main name:
  `atPure_returns_three`: `atPure_returns_four` (ReturnsLeftFour.lean) with K13's line called:
    `K13.k13Lot_no_strays_light` (Johnson/Desc/ProofFile/Honest/K13/NoStrayLight.lean). Its binders
    beside the head and the library's test: book: the book's maker returns; k14: no half of the
    shared chain's list strays in the shared chain; range: the named member of the index's range is
    in range.

Limits. An implication: none of the three is proved here. THAT THE BOOK's MAKER RETURNS IS A PREMISE
HERE: NOT PROVED IN THIS FILE. k14: as in ReturnsLeft.lean. range is a fact on the letter I. The
head is a hypothesis, and so is the library's test. The head and the library's test have a member
together at the library's written copy of the full-size public files
(`AtFullSide.Top.headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the
package's files by no theorem. At the library's full size and the function `OnBytes.secondHashFunction` alone.
Through its imports the file stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsLeftFour
import Johnson.Desc.ProofFile.Honest.K13.NoStrayLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}

/-- **WHAT IS LEFT, K13's LINE CALLED TOO.** Conditional: h: the head; hl: the library's test on the
head's public files; book: the book's maker returns; k14: no half of the shared chain's list strays
in the shared chain; range: the named member of the index's range is in range. -/
theorem atPure_returns_three (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (book : ∀ k0 k1 k2 e p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
        ∃ B, bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
          (mergesByName cF.blocksInOrder) = .ok B)
    (k14 : strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      ((nowSharedBy (I.weights Zp) Zp).toOption.getD []) = [])
    (range : I.inRange I.dummy = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o' S O) = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
  atPure_returns_four h hl I o' S O book
    (fun G _ => K13.k13Lot_no_strays_light h (I.weights Zp) O.pile G) k14 range

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atPure_returns_three
