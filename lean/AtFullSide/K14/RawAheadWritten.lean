-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawAheadWritten.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean), AT
mergesByName's MERGES: WHATEVER BOOK THE FRAME's bookRaw
(Johnson/Desc/ProofFile/Honest/BookWhole.lean) RETURNS, ITS ENTRIES ARE rawAheadW: AN APPEND OF TEN
PIECES IN THE MAKER's OWN ORDER: EIGHT WRITTEN LISTS AND TWO MAKERS' TERMS; AND THE TWO TERMS ARE
WHAT THEIR MAKERS RETURN. Four definitions; statements with their proofs; no evaluation in this
file.

  rawLinksW, rawWantsW   the stretches as spendingBook (Honest/BookAll.lean) has them: the makers'
                  terms at its own arguments, which are those of rawWantsL
                  (AtFullSide/K14/RawWantsWritten.lean)
  rawSegW         the carrying entries of the chain of segments: the maker's term at the written
                  messages sentFirstW (Honest/BookWritten/SentFirst.lean)
  rawAheadW       **the ten pieces**
  rawLinks_ok, rawSeg_ok   each term is what its maker returns, wherever that returns
  rawLinks_returns, rawSeg_returns   **each maker returns its term**: no premise
  rawAhead_written   **bookRaw WP … = .ok W → W.ahead = rawAheadW**

How it follows. The frame's bookRaw_ahead (Honest/BookSharedLaw.lean) and spendingBook_open
(Honest/BookRowStretch.lean) open W.ahead into its pieces, each with its maker's equation; each
piece is the written value, since a maker returns one thing: sentIn_first_written,
sentIn_shared_written (Honest/BookWritten/), foldEntries_first_written, foldEntries_second_written
(AtFullSide/K14/FoldsWritten.lean), rawIdx_written (AtFullSide/K14/RawFactsWritten.lean) and the
small facts of AtFullSide/K14/RawSmallWritten.lean. That the two makers return:
rawLinksWants_returns (RawWantsWritten.lean); bookRaw_returns_written
(AtFullSide/K14/RawReturnsWritten.lean) with bookRaw_ahead.

No option is raised. The file lies in the side library because it imports files of it.

Limits. rawAhead_written IS AN IMPLICATION FROM "bookRaw RETURNS W": that it does is
bookRaw_returns_written's to say. A fact on written values: WP's own limit and the written sendings'
stand. THE MERGES ARE mergesByName's, WHICH THE FRAME's OWN TEXT CALLS A GUESS: that they are the
format's merges is said nowhere. rawWantsW AND rawSegW ARE NOT SPELLED: what their members hold is
said by no statement here; how many they are: AtFullSide/K14/RawLengthsWritten.lean. rawSegW stands
over segmentCarries (Honest/BookCarry.lean): its value is that maker's. rawSeg_returns' proof names
the fifteen places of bookRaw_ahead's conclusion. Nothing on any test of the book's own. Nothing on
soundness, on completeness or on what is hidden; no property.
-/
import AtFullSide.K14.RawSmallWritten
import AtFullSide.K14.RawWantsWritten
import AtFullSide.K14.RawReturnsWritten
import Johnson.Desc.ProofFile.Honest.BookRowStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- What linksWants returns at spendingBook's own arguments. At a rejection ([], 0) would stand
here: it does not reject: rawLinks_returns. -/
def rawLinksW : List Want × Nat :=
  (linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW (mergesByName WP.first.blocksInOrder).ends
    (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0).toOption.getD ([], 0)

/-- The stretches, as spendingBook has them: the links', then the lone sumchecks'. -/
def rawWantsW : List Want :=
  rawLinksW.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
    ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) rawLinksW.2).1

/-- The carrying entries of the chain of segments, at the written messages. At a rejection [] would
stand here: the maker does not reject: rawSeg_returns. -/
def rawSegW : List Ahead := (segmentCarries (planOf WP.first.blocksInOrder) sentFirstW).toOption.getD []

/-- **The raw book's entries: ten pieces, in the maker's own order.** -/
def rawAheadW : List Ahead :=
  rawWantsW.map (·.entry) ++ foldsFirstW ++ foldsSharedW ++ [] ++ [splitEntryWritten] ++
    rawSegW ++ rawCarriesFoldedW ++ rawCarriesOmegaW ++ rawCarriesWW ++ rawOwnCarryW

/-- The term is what linksWants returns. -/
theorem rawLinks_ok {a : List Want × Nat}
    (h : linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
      (mergesByName WP.first.blocksInOrder).ends
      (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a) : rawLinksW = a := by
  unfold rawLinksW
  rw [h]
  rfl

/-- The term is what segmentCarries returns. -/
theorem rawSeg_ok {seg : List Ahead}
    (h : segmentCarries (planOf WP.first.blocksInOrder) sentFirstW = .ok seg) : rawSegW = seg := by
  unfold rawSegW
  rw [h]
  rfl

/-- **linksWants RETURNS rawLinksW.** -/
theorem rawLinks_returns :
    linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
      (mergesByName WP.first.blocksInOrder).ends
      (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok rawLinksW := by
  obtain ⟨a, ha⟩ := rawLinksWants_returns
  rw [rawLinks_ok ha]
  exact ha

/-- **segmentCarries RETURNS rawSegW.** -/
theorem rawSeg_returns :
    segmentCarries (planOf WP.first.blocksInOrder) sentFirstW = .ok rawSegW := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  obtain ⟨_, m0, _, seg, _, _, _, _, _, _, _, hm0, _, hseg, _⟩ := bookRaw_ahead hW
  obtain rfl : sentFirstW = m0 := Except.ok.inj (sentIn_first_written.symm.trans hm0)
  rw [rawSeg_ok hseg]
  exact hseg

/-- **WHATEVER BOOK bookRaw RETURNS AT THE WRITTEN DESCRIPTION, AT mergesByName's MERGES: ITS
ENTRIES ARE rawAheadW.** CONDITIONAL: that it returns W. -/
theorem rawAhead_written (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    W.ahead = rawAheadW := by
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, hm1, hseg, hiF, hcF, hiO, hcO, hpq,
    htail, hW⟩ := bookRaw_ahead h
  obtain ⟨idx, a, f0, f1, f2, hidx, ha, -, hf0, hf1, hf2, hB0⟩ := spendingBook_open hB
  obtain rfl : sentFirstW = m0 := Except.ok.inj (sentIn_first_written.symm.trans hm0)
  obtain rfl : sentSharedW = m1 := Except.ok.inj (sentIn_shared_written.symm.trans hm1)
  obtain rfl : 1 = iF := Except.ok.inj (rawFoldedAt_written.symm.trans hiF)
  obtain rfl : rawCarriesFoldedW = cF := Except.ok.inj (rawCarriesFolded_written.symm.trans hcF)
  obtain rfl : 39 = iO := Except.ok.inj (rawLastSwitch_written.symm.trans hiO)
  obtain rfl : rawCarriesOmegaW = cO := Except.ok.inj (rawCarriesOmega_written.symm.trans hcO)
  obtain rfl : ((⟨⟨3, none, 2, .K12⟩, 0⟩, ⟨⟨3, none, 2, .K12⟩, 1⟩) : Addr × Addr) = pq :=
    Except.ok.inj (rawSecondFold_written.symm.trans hpq)
  obtain rfl : 152 = tail := Except.ok.inj (rawTail_written.symm.trans htail)
  obtain rfl : rawIdxW = idx := Option.some.inj (rawIdx_written.symm.trans hidx)
  obtain rfl : foldsFirstW = f0 := Except.ok.inj (foldEntries_first_written.symm.trans hf0)
  obtain rfl : foldsSharedW = f1 := Except.ok.inj (foldEntries_shared_written.symm.trans hf1)
  obtain rfl : [] = f2 := Except.ok.inj (foldEntries_second_written.symm.trans hf2)
  obtain rfl := rawLinks_ok ha
  obtain rfl := rawSeg_ok hseg
  rw [hW, hB0, rawSplit_written, rawOwnCarry_written]
  show _ ++ carryPair ⟨⟨3, none, 2, .K12⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 1⟩ _ _ ++ _ = _
  rw [rawCarriesW_written]
  rfl

end AtFullSide.K14

#print axioms AtFullSide.K14.rawLinks_ok
#print axioms AtFullSide.K14.rawSeg_ok
#print axioms AtFullSide.K14.rawLinks_returns
#print axioms AtFullSide.K14.rawSeg_returns
#print axioms AtFullSide.K14.rawAhead_written
