-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsLeftTwo.lean: CONDITIONAL: WHAT IS LEFT OF "THE MAKER
onlineProverFromPublicFiles RETURNS AT THE HEAD's THREE FILES AND THE FILLING widerFillAt": TWO BINDERS BESIDE THE HEAD
AND THE LIBRARY's TEST ON THE HEAD's PUBLIC FILES: THE BOOK's MAKER RETURNS, AND THE RANGE.

Main name:
  `atPure_returns_two`: `atPure_returns_three` (ReturnsLeftThree.lean) with the shared chain's line
    called: `K14.wider_k14_light` (Johnson/Desc/ProofFile/Honest/K14/NoStrayLight.lean). Its binders
    beside the head and the library's test: book: the book's maker returns; range: the named member
    of the index's range is in range.

Limits. An implication: neither of the two is proved here. THAT THE BOOK's MAKER RETURNS IS A
PREMISE HERE: NOT PROVED IN THIS FILE. range is a fact on the letter I. The head is a hypothesis,
and so is the library's test. The head and the library's test have a member together at the
library's written copy of the full-size public files (`AtFullSide.Top.headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the package's files by no theorem. At the
library's full size and the function `OnBytes.secondHashFunction` alone. Through its imports the file stands
above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsLeftThree
import Johnson.Desc.ProofFile.Honest.K14.NoStrayLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}

/-- **WHAT IS LEFT, ALL LINES ON STRAYS CALLED.** Conditional: h: the head; hl: the library's test
on the head's public files; book: the book's maker returns; range: the named member of the index's
range is in range. -/
theorem atPure_returns_two (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (book : ∀ k0 k1 k2 e p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
        ∃ B, bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
          (mergesByName cF.blocksInOrder) = .ok B)
    (range : I.inRange I.dummy = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o' S O) = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
  atPure_returns_three h hl I o' S O book
    (K14.wider_k14_light h.laid.pub h.laid.value (I.weights Zp)) range

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atPure_returns_two
