-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K3/Term/LookupThreeTestsUnderTheHeadAlone.lean: the kind "lookup" (K3): UNDER THE HEAD ALONE (`P5J.AtMgA`, the
library's one hypothesis at the full size), at every set of public files at which the head holds, at the book of whatever
`onlineProverFromPublicFiles` (Honest/AtPure.lean) returns, at any filling: at EVERY ONE of the fifty sites all three public tests on the book
accept (`bookFits`, `placeFits`: Honest/K3/Law/RowLends.lean; `startsFit`: Honest/K3/Law/MasksBook.lean), the third at the site's
own first scalar. It is the text of `k3Fits_at_atPure` (AtFullSide/Honest/K3/FitsAtPure.lean) without its premise that the public
files are one of the two named sets. No definition, three theorems: calls alone; nothing is evaluated here.

  `lookupFirstScalarIsWrittenUnderTheHead`   the head, a site s ⊢ s.p.first = `firstW (sortOf s.link) s.digits`
  **`lookupThreeTestsUnderTheHeadAlone`**      the head, hA ⊢ at every site: the mask row's owner is found and the three tests
                                             accept A.B
  `bookLendsTheMaskRowUnderTheHeadAlone`     the head, hA ⊢ at every site: owner, `bookFits`, `startsFit`

How. `lookupThreeTestsUnderTheHead`, `bookLendsTheMaskRowAtEverySite`, `lookupFirstScalarIsWrittenAtASite`
(LookupThreeTestsUnderTheHead.lean beside this file) at their one named premise, which `linkScalarsAreWrittenUnderTheHead`
(LinkScalarsAreWrittenUnderTheHead.lean beside this file) pays.

Hypotheses that remain. The head. hA: that `onlineProverFromPublicFiles` returns.

Every one of the fifty. On the 25 calls the first scalar is 0 (`place_lay`, `place_att`, `place_head`,
Johnson/Desc/First/Look/K3PlaceLetters.lean); on the digits of the head's link 24 it is 2168 in the goals' scope (`digits_place`,
Johnson/Desc/Kinds/Law/K6PubInScope.lean); on the digits of the links 0 to 23 it is the link's written number of scalars less
the lookup's own. The forms on the links' scalars do not speak of the head's link: it needs none of them.

Limits. THE MASK ROW's OWNER r' IS WHAT `ownerOf` RETURNS AT THE WRITTEN DESCRIPTION AND THE WRITTEN SENDINGS, NOT AT A's OWN
DESCRIPTION. All limits of the files called hold here. The full size and the format's second hash function alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.Term.LinkScalarsAreWrittenUnderTheHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law ProofFile.Honest.K3.Term
open Johnson.AtFull.Lots.K3 (sortOf firstW)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

variable {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Every site's first scalar is the written one, under the head alone.** -/
theorem lookupFirstScalarIsWrittenUnderTheHead (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (s : Site) (hs : s ∈ lookSites Zp) : s.p.first = firstW (sortOf s.link) s.digits :=
  lookupFirstScalarIsWrittenAtASite h s hs fun _ _ => linkScalarsAreWrittenUnderTheHead h

/-- **THE THREE TESTS AT EVERY SITE, UNDER THE HEAD ALONE.** Conditional: the head; hA, at any filling. r' is what `ownerOf`
returns at the WRITTEN description and the written sendings, not at A's own description. -/
theorem lookupThreeTestsUnderTheHeadAlone (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ s ∈ lookSites Zp, ∃ r' : MsgAt,
      ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
        s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
      bookFits A.B (A.B.rowsOf 0) (dueAt A.B.first) s.at_ = true ∧
      startsFit A.B s.at_ s.p.first r'.owner r'.base = true ∧
      placeFits A.B (A.B.rowsOf 0) s.at_ = true :=
  lookupThreeTestsUnderTheHead h hA (linkScalarsAreWrittenUnderTheHead h)

/-- **The book lends the mask row at every site, under the head alone.** Conditional: the head; hA. r' is what `ownerOf`
returns at the WRITTEN description and the written sendings, not at A's own description. -/
theorem bookLendsTheMaskRowUnderTheHeadAlone (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ s ∈ lookSites Zp, ∃ r' : MsgAt,
      ProofFile.Honest.ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1
        (WP.second.blocksInOrder.flatMap (·.rounds)) s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
      bookFits A.B (A.B.rowsOf 0) (dueAt A.B.first) s.at_ = true ∧
      startsFit A.B s.at_ s.p.first r'.owner r'.base = true :=
  bookLendsTheMaskRowAtEverySite h hA (linkScalarsAreWrittenUnderTheHead h)

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.lookupFirstScalarIsWrittenUnderTheHead
#print axioms AtFullSide.Honest.K3.Term.lookupThreeTestsUnderTheHeadAlone
#print axioms AtFullSide.Honest.K3.Term.bookLendsTheMaskRowUnderTheHeadAlone
