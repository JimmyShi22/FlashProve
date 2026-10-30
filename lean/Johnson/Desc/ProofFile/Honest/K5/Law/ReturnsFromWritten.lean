-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsFromWritten.lean: CONDITIONAL: THE FRAME's MAKER onlineProverFromPublicFiles
RETURNS AT THE FILLING `widerFillAt fullIn o' S O`, UNDER THE LIBRARY's HEAD AND ITS TEST protocolDataWellFormed,
FROM ONE CLOSED SENTENCE ON THE WRITTEN BOOK: hB: THE BOOK's MAKER bookWhole RETURNS A BOOK AT THE
LIBRARY's WRITTEN DESCRIPTION WP. AN IMPLICATION: hB IS NOT PROVED IN THIS FILE, NOR BENEATH IT. One
theorem; no definition; one call.

Why. `atPure_returns_one_fullIn` (ReturnsLeftOneFullIn.lean) has one premise beside the head and the
test: book: the book's maker returns at the head's description. Other authors have carried that from
the written description to the head's (`ProofFile.Honest.K14.book_for_atPure_of_written`,
Johnson/Desc/ProofFile/Honest/K14/BookForAtPure.lean). Their conclusion and our premise were one
string as texts; here they meet as terms.

Main name:
  `atPure_returns_fullIn_of_written`: h, hl, hB ⊢ there is an A that onlineProverFromPublicFiles returns, with A.Z = Zp
    and A.F the head's description.

Which way it goes. An exchange: book, which names the head's letters, goes; hB comes, which names
written constants alone: WP, the written lists of sendings, the guessed merges. hB has no letter in
it: it is true or false once for all.

Limits. hB is a premise. That bookWhole returns says that the book's eleven own tests accept, and no
more. Which sumchecks count as merges is the frame's guess (`mergesByName`). It holds of the makers'
texts as they lie beneath this file: of `segmentCarries` as
Johnson/Desc/ProofFile/Honest/BookCarry.lean has it there. All limits of ReturnsLeftOneFullIn.lean
and of BookForAtPure.lean hold: `fullIn` is noncomputable, at the full size alone, and no program
runs it; that onlineProverFromPublicFiles returns says nothing on what its prover plays. The head is a hypothesis, and so
is the library's test. The head and the library's test have a member together at the library's
written copy of the full-size public files (`AtFullSide.Top.headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the package's files by no theorem. Through
its imports the file stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsLeftOneFullIn
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **onlineProverFromPublicFiles RETURNS AT `fullIn`, FROM ONE CLOSED SENTENCE ON THE WRITTEN BOOK.** Conditional: h:
the head; hl: the library's test on the head's public files; hB: the book's maker returns a book at
the library's written description. -/
theorem atPure_returns_fullIn_of_written (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt fullIn o' S O) = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
  atPure_returns_one_fullIn h hl o' S O (K14.book_for_atPure_of_written hB h)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atPure_returns_fullIn_of_written
