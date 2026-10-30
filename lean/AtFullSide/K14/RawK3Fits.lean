-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawK3Fits.lean: WHATEVER BOOK bookWhole (Honest/BookWhole.lean) RETURNS AT THE
WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN SENDINGS AND THE
MERGES THAT mergesByName GUESSES: THE LOOKUPS' THREE PUBLIC TESTS ON THE BOOK (bookFits, placeFits:
Honest/K3/Law/RowLends.lean; startsFit: Honest/K3/Law/MasksBook.lean) ACCEPT IT AT EACH OF THE FIFTY
PLACES OF THE KIND K3, AT EVERY RECORD a : At WITH THAT PLACE AND A FACE WITH THE FIVE WRITTEN
NUMBERS; AND THERE IS SUCH A BOOK. Statements with their proofs: calls, and two light evaluations.
Written by the authors of the honest side of the linear claim's shared rounds (K14); the three tests
are the lookups' authors' and are called, not written anew.

Limits.
  * THAT THE LOOKUPS' OWN SITES (lookSites, Honest/K3/Lot.lean) AT ANY PUBLIC PART HAVE THESE
    NUMBERS IS NO THEOREM: at each of the fifty, v (the one member of parts), d and first were
    printed by Lean's evaluator at the library's stored full-size files and laid into
    AtFullSide/K14/RawK3Sites.lean by a program. What Lean's kernel holds of them: that AT THESE
    NUMBERS the tests accept, and that at others they need not (k3Cuts_bent, k3Wants_bent).
    Whoever would call these statements at a site owes: its place; its face's five numbers; its
    first scalar.
  * AT THE STAGES THAT SEND NOTHING (shift, alpha, join, the lines, zero): 4 + v + d OF
    37 + 2 (v + d), SOME TWO FIFTHS OF A PLACE's STAGES: bookFits AND startsFit SAY ONLY THAT NO
    ENTRY NAMES THE PART AND THAT IT HAS NO COIN OF ITS OWN. The weight lies at the others.
  * A BOOK's NUMBER IS A CLAIM ON A SENDER's TEXT: that the sender lays its mask row at the coins
    from r.base on is not said here; the book's tests and these three see entries, not texts.
  * The laws over these tests are the lookups'; at which row of the lookup they stand is theirs to
    say.
  * THE MERGES ARE A GUESS; the sendings are found by labels that rest on one print; WP's values
    were printed by Lean's evaluator. The full size, the format's second hash function alone.
  * Numbers and addresses on public data: nothing on soundness, completeness or hiding.

  k3Entries_written   **the law's first premise at the raw book**: its entries whose spender stands
                  at one of the fifty places are the parts' stated runs, place by place, stage by
                  stage (k3Stated k3SitesW). CONDITIONAL: that bookRaw returns W
  k3Fits_written  **the statement of the first sentence.** CONDITIONAL: that bookWhole returns B.
                  "THERE ARE l AND r": BOTH ARE PINNED: l by the place's own link; r by the return
                  of ownerOf, whose term is the lookups' rowAt written out
  k3Fits_closed   **there is such a book: NO PREMISE**: with bookWhole_returns_written
                  (AtFullSide/K14/BookWholeWritten.lean)
  k3Places_are    the fifty places are the library's IM.k3Place l false, IM.k3Place l true
                  (Johnson/IMR/K3Seat.lean), l = 0, …, 24, in that order

The road: rawAhead_written, rawAhead_split, stated_of_wants at k3Wants_written and k3Seg_none: the
first premise; k3Places_nodup, k3NoRow_written, k3Inside_written, k3CutsAt: the four others;
fits_at_every_face (AtFullSide/K14/K3FitsOfStated.lean): the law; k3Rows_written: owner and base.
Kin. That the book which bookWhole returns is one that bookRaw returns stands as rawWhole_is_raw in
AtFullSide/K14/RawMineAtK13.lean; its three lines are written once more inside a proof here, so that
this file need not stand on that one's evaluations.
AN OPTION IS RAISED in front of two light evaluations: maxRecDepth to 1000000.
What is assumed. Nothing.
-/
import AtFullSide.K14.RawK3Wants
import AtFullSide.K14.RawK3Seg
import AtFullSide.K14.RawK3Rest
import AtFullSide.K14.BookWholeWritten
import Johnson.IMR.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **THE RAW BOOK's ENTRIES AT THE FIFTY PLACES ARE THE PARTS' STATED RUNS.** CONDITIONAL: that
bookRaw returns W. -/
theorem k3Entries_written (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    W.ahead.filter (fun e => k3SitesW.any fun s => s.at_.place == e.spender.place) =
      k3Stated k3SitesW := by
  rw [rawAhead_written W h, rawAhead_split]
  exact stated_of_wants k3Wants_written (k3Rest_none k3Seg_none)

set_option maxRecDepth 1000000 in
/-- **WHATEVER BOOK bookWhole RETURNS AT WP: AT EACH OF THE FIFTY PLACES, AT EVERY RECORD WITH THAT
PLACE AND A FACE WITH THE FIVE NUMBERS, THE LOOKUPS' THREE TESTS ACCEPT**, with the owner and the
base of the link's mask row as ownerOf returns it. CONDITIONAL: hB. -/
theorem k3Fits_written {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) :
    ∀ s ∈ k3SitesW, ∃ (l : Nat) (r : MsgAt), s.at_.place.link = some l ∧
      ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some r ∧
      ∀ a : At, a.place = s.at_.place → a.face.shifted = true → a.face.mu = 5 →
        a.face.planes = 32 → a.face.parts = s.at_.face.parts → a.face.d = s.at_.face.d →
        bookFits B (B.rowsOf 0) (dueAt B.first) a = true ∧
          startsFit B a s.first r.owner r.base = true ∧
          placeFits B (B.rowsOf 0) a = true := by
  have hW : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B := by
    unfold bookWhole at hB
    obtain ⟨W, hW, hc⟩ := BookShared.ex_bindE hB
    obtain rfl := checked_ok hc
    exact hW
  have hf : B.first = rawRowsFirstW := (rawBookRows_written _ B hW).1
  have hr0 : B.rowsOf 0 = rawRowsFirstW := hf
  have hc : B.cuts = cutsOf WP := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := bookRaw_rows hW
    exact hc
  have H := fits_at_every_face (rows := B.rowsOf 0) (due := dueAt B.first)
    (k3Entries_written B hW) k3Places_nodup (by rw [hr0]; exact k3NoRow_written)
    (by rw [hf]; exact k3Inside_written) (k3CutsAt hc)
  have h3 : ∀ s ∈ k3SitesW, s.at_.face.shifted = true ∧ s.at_.face.mu = 5 ∧
      s.at_.face.planes = 32 := by decide +kernel
  intro s hs
  obtain ⟨l, r, hl, hr, ho, hb⟩ := k3Rows_written s hs
  refine ⟨l, r, hl, hr, fun a hp h1 h2 h4 h5 h6 => ?_⟩
  obtain ⟨p, f, n⟩ := a
  obtain rfl : p = s.at_.place := hp
  obtain ⟨e1, e2, e3⟩ := h3 s hs
  rw [ho, hb]
  exact H s hs f n (h1.trans e1.symm) (h2.trans e2.symm) (h4.trans e3.symm) h5 h6

/-- **THERE IS A BOOK THAT bookWhole RETURNS AT WP, AND THE LOOKUPS' THREE TESTS ACCEPT IT AT THE
FIFTY PLACES: NO PREMISE.** -/
theorem k3Fits_closed :
    ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
        (mergesByName WP.first.blocksInOrder) = .ok B ∧
      ∀ s ∈ k3SitesW, ∃ (l : Nat) (r : MsgAt), s.at_.place.link = some l ∧
        ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 (WP.second.blocksInOrder.flatMap (·.rounds))
          s!"link {l}, moment 0" isMaskRowMsg = some r ∧
        ∀ a : At, a.place = s.at_.place → a.face.shifted = true → a.face.mu = 5 →
          a.face.planes = 32 → a.face.parts = s.at_.face.parts → a.face.d = s.at_.face.d →
          bookFits B (B.rowsOf 0) (dueAt B.first) a = true ∧
            startsFit B a s.first r.owner r.base = true ∧
            placeFits B (B.rowsOf 0) a = true := by
  obtain ⟨B, hB⟩ := bookWhole_returns_written
  exact ⟨B, hB, k3Fits_written hB⟩

set_option maxRecDepth 1000000 in
/-- The fifty places are the library's own addresses of the kind K3, link by link, the lookup on the
calls first. -/
theorem k3Places_are : k3SitesW.map (·.at_.place) =
    (List.range 25).flatMap fun l => [IM.k3Place l false, IM.k3Place l true] := by
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.k3Entries_written
#print axioms AtFullSide.K14.k3Fits_written
#print axioms AtFullSide.K14.k3Fits_closed
#print axioms AtFullSide.K14.k3Places_are
