-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsFill.lean: CONDITIONAL: THE FRAME's MAKER onlineProverFromPublicFiles RETURNS
AT A FILLING P, P A LETTER: UNDER THE LIBRARY's HEAD, ITS TEST protocolDataWellFormed, ONE CLOSED SENTENCE ON THE
WRITTEN BOOK (hB), AND WHAT THE MAKER ASKS OF THE FILLING (`MakerAsks` P). AN IMPLICATION: NEITHER
hB NOR `MakerAsks` P IS PROVED HERE. One theorem; no definition.

Why. A law that is stated at one written filling does not carry over to a wider one. The maker
returns at P just where eight parts hold (`atPure_returns_iff`, ReturnsOf.lean): four do not name
the filling (`MakerHas`), four ask something of it (`MakerAsks` P). The first four are had under the
head, the test and hB (`made_live`, ReturnsHead.lean; `K14.book_for_atPure_of_written`,
Johnson/Desc/ProofFile/Honest/K14/BookForAtPure.lean). So the return at a letter P is left with the
second four alone, as one premise on the filling.

Main name:
  `atPure_returns_fill`: h, hl, hB, f ⊢ there is an A that onlineProverFromPublicFiles returns at P, with A.Z = Zp, A.F
    the head's description, and A.G the ground of the head's public part.

The premise f: at the ground G of the head's public part: `MakerAsks` P Zp G (the head's
description): no half of P's lots strays from the first chain's list; none of its shared chain's;
none of its second's; P's range accepts P's dummy. The first goes lot by lot (`strays_firstOf_iff`,
ReturnsOf.lean). That f can be met at a filling: `makerAsks_wider_fullIn` (FillPremisesCheck.lean, a
file of checks beside this one).

Limits. hB is a premise: its authors tell of a proof (`bookWhole_returns_written`,
AtFullSide/K14/BookWholeWritten.lean), which does not lie beneath this file. That bookWhole returns
says that the book's eleven own tests accept, and no more; which sumchecks count as merges is the
frame's guess (`mergesByName`); it holds of the makers' texts as they lie beneath this file. That
the maker returns says nothing on what its prover plays, nor on whether P has a side at every place
of the description: `MakerAsks` forbids halves that stray, it does not ask for halves. The head is a
hypothesis, and so is the library's test. The head and the library's test have a member together at
the library's written copy of the full-size public files (`AtFullSide.Top.headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the package's files by no theorem. Through
its imports the file stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsHead
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **onlineProverFromPublicFiles RETURNS AT A FILLING P, P A LETTER.** Conditional: h: the head; hl: the library's test
on the head's public files; hB: the book's maker returns a book at the library's written
description; f: what the maker asks of the filling. -/
theorem atPure_returns_fill {W₀ Rc Tr X₀ X : Type} (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (P : OnlineProverParts W₀ Rc Tr X₀ X)
    (f : ∀ G, blankBy pureRoad.links Zp = some G →
      MakerAsks P Zp G (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G := by
  obtain ⟨G, B, m⟩ := made_live h hl (K14.book_for_atPure_of_written hB h)
  obtain ⟨A, hA, eZ, eG, eF, -⟩ := atPure_of_parts m (f G m.ground)
  exact ⟨A, hA, eZ, eF, by rw [eG]; exact m.ground⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atPure_returns_fill
