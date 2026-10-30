-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/K3/FitsAtPure.lean: the kind "lookup" (K3): under the library's one hypothesis at
the full size (`P5J.AtMgA`, "the head") at each of the goals' two named sets of public files, and
where `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns A at these files, at whichever
filling: at every site of `lookSites Zp` the three public tests on the frame's book (`bookFits`,
`startsFit`, `placeFits`) accept A's own book. One theorem; no definition; nothing is evaluated
here.

What still lacks, first. `hA`: that `onlineProverFromPublicFiles` returns at any filling at these files is shown in no
file that the writers of this one know. That the book of a thread's letters is A.B is not said here.
Of the premises of the laws over these tests (`DigitsRunAll`, `DictAt`, Honest/K3/Law/Thread/) the
two tests alone are met by this: the law of the part that sends the mask rows, the clauses on the
coins and the field half stay premises there. These laws stand at the elder row `proverSideOfLookupInChainAtOneOwner`.

How the proof goes. `bookWhole_returns_written` (AtFullSide/K14/BookWholeWritten.lean) has a book B
at the written description. A.B is B: both are what `bookWhole` returns at the head's description
and the public part's own three lists of sendings: `atPure_book_at_head`
(Honest/K14/AtPureBookAtHead.lean) and `bookWhole_same_at_made` (Honest/K14/BookForAtPure.lean).
Then `k3Fits_at_sites` (FitsAtSites.lean). The equation A.B = B stands
inside the proof: it is no named theorem here.

Hypotheses that remain. `hZ`, `h`: as in FitsAtSites.lean. `hA`: the return of `onlineProverFromPublicFiles`.


Limits, after those of the files called, which all hold here. At the two named sets alone; at the
earlier hash. At the stages that send nothing, 4 + v + d of a site's 37 + 2 (v + d), `bookFits` and
`startsFit` say only that no entry names the part. Nothing on a sender's text or a run. The merges
are a guess off names.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import AtFullSide.Honest.K3.FitsAtSites
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **THE TIE, AT THE BOOK OF WHATEVER `onlineProverFromPublicFiles` RETURNS**, general in the filling. r' is what
`ownerOf` returns at the WRITTEN description and the written sendings, not at A's own description.
-/
theorem k3Fits_at_atPure {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.NamedFiles Z)
    {D r Zp Np cF x} (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ s ∈ lookSites Zp, ∃ r' : MsgAt,
      ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
        s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
      bookFits A.B (A.B.rowsOf 0) (dueAt A.B.first) s.at_ = true ∧
      startsFit A.B s.at_ s.p.first r'.owner r'.base = true ∧
      placeFits A.B (A.B.rowsOf 0) s.at_ = true := by
  obtain ⟨B, hB⟩ := AtFullSide.K14.bookWhole_returns_written
  have e : A.B = B := Except.ok.inj
    ((ProofFile.Honest.K14.atPure_book_at_head h hA).symm.trans
      (ProofFile.Honest.K14.bookWhole_same_at_made hB h))
  rw [e]
  exact k3Fits_at_sites hZ h hB

end AtFullSide.Honest.K3

#print axioms AtFullSide.Honest.K3.k3Fits_at_atPure
