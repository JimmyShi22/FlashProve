-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/MakersBookOne.lean: NO KIND IS NAMED IN ITS STATEMENTS. ("Honest/" stands for
Johnson/Desc/ProofFile/Honest/ throughout.) Under the library's one hypothesis at the full size
(P5J.AtMgA), at the format's second hash function, WITH NO OTHER PREMISE: **THE BOOK OF COINS THAT THE
FRAME's MAKER bookWhole (Honest/BookWhole.lean) RETURNS IS ONE BOOK AT THREE SPELLINGS OF ITS CALL
THAT FILES OF THE LIBRARY USE; ITS ENTRIES ARE THE NAMED LIST rawAheadW
(AtFullSide/K14/RawAheadWritten.lean: ten pieces: eight written lists and two makers' terms that are
not spelled); AND WHEREVER THE FRAME's MAKER onlineProverFromPublicFiles (Honest/AtPure.lean) YIELDS A, AT WHATEVER
FILLING, A's BOOK IS THAT BOOK AND A's DESCRIPTION IS THE HEAD's.** Two theorems; no definition;
calls alone; nothing is evaluated anew. PUBLIC DATA ALONE: no coin, no input, no run, no measure.

What it is not. CONDITIONAL ON THE HEAD h; that h has a member is not shown here. THAT onlineProverFromPublicFiles YIELDS
IS NOT SHOWN HERE: in makers_book_one it stands in front of an arrow, under "for all fillings", and
that clause says nothing wherever onlineProverFromPublicFiles yields at no filling; in makers_ahead_at_atPure it is the
premise hA. That onlineProverFromPublicFiles yields at one filling is shown in no file that this one imports. WHAT THE
BOOK HOLDS IS SAID BY "B.ahead = rawAheadW" ALONE, and at two of rawAheadW's ten pieces by a maker's
term: what their members hold is said by no statement here; of the book's rows (B.first, B.shared,
B.second) and cuts (B.cuts) nothing. THAT bookWhole RETURNS SAYS THAT THE BOOK's ELEVEN OWN TESTS
ACCEPT, AND NO MORE: nothing on the frame's test over a list of owners (ownersClearBy), on
carriesWhole, on a budget of positions; the eleven read entries, rows, cuts and the description, not
the parts' texts. OF A THREAD, A SIDE OR A SCRIPT AT A NOTHING IS SAID; that A's prover can play is
not said. Which masked sumchecks are merges is the frame's guess (mergesByName), in all three
spellings. The return at the written description rests on evaluations in Lean's kernel at written
values, in the files that AtFullSide/K14/BookWholeWritten.lean's head names. The full size and the
earlier hash alone. In the side library. All limits on what is proved in the files named hold here.
No test that can fail stands here: those stand where the book's entries are evaluated. No property
is claimed. Nothing on soundness, completeness or hiding.

Why. Laws of several kinds speak of "the maker's book" at one or another of these spellings, and
several proofs retype the one line by which A.B is that book. Here it is one name. Nothing calls the
two theorems yet (the second calls the first).

The three spellings. (s1) at the library's written description WP
(Johnson/AtFull/ProofPlan/WP.lean), the library's written lists of sendings
(Johnson.G.proofSendsFull) and the merges by name of WP's first chain. (s2) at the proof file's IOP
as written in Lean, which is the head's description (P5J.F0T), at the written lists and the merges
by name of that description's first chain. (s3) at the same description, at the public part's own
three lists (Zp.made.proof) and the merges by name of cF: the call to which onlineProverFromPublicFiles's own comes under
the head (atPure_book_at_head); onlineProverFromPublicFiles's text calls bookWhole at what onlineDescription returns and at the
last three of what the library's list of sendings returns. (The two lists of merges in (s2) and (s3)
are one by unfolding; the lists of sendings are not.)

  makers_book_one **there is one B that all three calls return; B.ahead = rawAheadW; and for every
                  filling P and every A that onlineProverFromPublicFiles yields at the head's files and P: A.B = B and
                  A.F is the head's description**
  makers_ahead_at_atPure the same read at one A: from hA: A.B.ahead = rawAheadW, and A.F is the
                  head's description

How. B and its entries: bookWhole_returns_written_ahead (AtFullSide/K14/BookWholeWritten.lean).
(s2): bookWhole_same_at_head (Honest/K14/BookWholeAtHead.lean). (s3): bookWhole_same_at_made
(Honest/K14/BookForAtPure.lean). A.B = B: atPure_book_at_head (Honest/K14/AtPureBookAtHead.lean) and
bookWhole_same_at_made are equations on one and the same call, so their right sides are one. A.F:
the frame's atPure_ok (Honest/AtPureLaw.lean) and the head's field on the value, as in
atPure_book_at_head's own proof.
-/
import AtFullSide.K14.BookWholeWritten
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure
import Johnson.Desc.ProofFile.Honest.K14.BookWholeAtHead
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open VerifiableInference.Desc (Chain)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.K14

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **UNDER THE HEAD, AT THE EARLIER HASH: THE MAKER's BOOK IS ONE**: one B is returned at the three
spellings of bookWhole's call; its entries are the named list; and whatever onlineProverFromPublicFiles yields at the
head's files, at whatever filling, has that book and the head's description. That onlineProverFromPublicFiles yields at
any filling is not said. CONDITIONAL on h. -/
theorem makers_book_one {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
        (mergesByName WP.first.blocksInOrder) = .ok B ∧
      bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
        proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B ∧
      bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
        Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok B ∧
      B.ahead = rawAheadW ∧
      ∀ (W₀ Rc Tr X₀ X : Type) (P : OnlineProverParts W₀ Rc Tr X₀ X) (A : OnlineProverWithDescription W₀ Rc Tr X₀ X),
        onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A →
          A.B = B ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := by
  obtain ⟨B, hB, ha⟩ := bookWhole_returns_written_ahead
  refine ⟨B, hB, bookWhole_same_at_head hB h, bookWhole_same_at_made hB h, ha,
    fun _ _ _ _ _ P A hA => ⟨Except.ok.inj ((atPure_book_at_head h hA).symm.trans
      (bookWhole_same_at_made hB h)), ?_⟩⟩
  obtain ⟨-, -, hF, -⟩ := atPure_ok hA
  exact Except.ok.inj (hF.symm.trans h.laid.value)

/-- hA (onlineProverFromPublicFiles YIELDS A, at the head's files) IS A PREMISE. **Under the head: the entries of A's
book are the named list, and A's description is the head's.** General in the filling.
CONDITIONAL on h. -/
theorem makers_ahead_at_atPure {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.B.ahead = rawAheadW ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := by
  obtain ⟨B, -, -, -, ha, hall⟩ := makers_book_one h
  obtain ⟨e, eF⟩ := hall _ _ _ _ _ P A hA
  exact ⟨e ▸ ha, eF⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.makers_book_one
#print axioms AtFullSide.K14.makers_ahead_at_atPure
