-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsLeftOneFullIn.lean: CONDITIONAL: AT fullIn ONE BINDER IS
LEFT OF "THE MAKER onlineProverFromPublicFiles RETURNS AT THE HEAD's THREE FILES AND THE FILLING widerFillAt", BESIDE THE
HEAD AND THE LIBRARY's TEST ON THE HEAD's PUBLIC FILES: THE BOOK's MAKER RETURNS. `fullIn` is a
value of `WiderIn`: the full-size trace and the index's own matrix of digits, in the form in which
`widerFillAt` takes them; it is no input of a run.

Main name:
  `atPure_returns_one_fullIn`: `atPure_returns_two` (ReturnsLeftTwo.lean) at I := `fullIn`
    (Johnson/Desc/ProofFile/Honest/AtPureFullIn.lean), whose `fullIn_range` has the range.

Limits. An implication: THAT THE BOOK's MAKER RETURNS IS A PREMISE HERE: NOT PROVED IN THIS FILE.
All limits of AtPureFullIn.lean hold here: `fullIn` is noncomputable: no program can run a choice of
fields that is made from it; it is at the full size alone; the test programs run `widerFillAt` at
another value of `WiderIn`, and nothing compares the two; `inRange` is true at every index there,
because the range is in the type of the index: so the range holds there by construction: it is had
for nothing. The argument S of `widerFillAt` stays a free letter here too: nothing says that a
caller supplies the full size there. The head is a hypothesis, and so is the library's test. The
head and the library's test have a member together at the library's written copy of the full-size
public files (`AtFullSide.Top.headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean), which is
tied to the package's files by no theorem. At the function `OnBytes.secondHashFunction` alone. Through its
imports the file stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsLeftTwo
import Johnson.Desc.ProofFile.Honest.AtPureFullIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT fullIn THE BOOK ALONE IS LEFT.** Conditional: h: the head; hl: the library's test on the
head's public files; book: the book's maker returns. -/
theorem atPure_returns_one_fullIn (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (book : ∀ k0 k1 k2 e p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
        ∃ B, bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
          (mergesByName cF.blocksInOrder) = .ok B) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt fullIn o' S O) = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
  atPure_returns_two h hl fullIn o' S O book fullIn_range

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atPure_returns_one_fullIn
