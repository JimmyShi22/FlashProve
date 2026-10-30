-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/BookAtW.lean: THE SHARED "SENDING" (the kind K1): THE BOOK's SIDE AT W's SENDING PART
(the owner ⟨⟨1, none, 4, .K1⟩, 0⟩; number 356 of the first chain): OF THE WRITTEN LIST rawAheadW
(AtFullSide/K14/RawAheadWritten.lean) THE ENTRIES WITH THAT OWNER ARE FOUR, WRITTEN
HERE; SO AT EVERY BOOK WHOSE ENTRIES ARE rawAheadW, AT EVERY ORDER OF PLACES, AT p := ⟨⟨3, none, 2,
.K12⟩, 0⟩: ProverCoinCounts.spentBy IS ONE ENTRY: ⟨0, 3882⟩ · ⟨0, 11⟩; ProverCoinCounts.knownBy IS ONE ENTRY: ⟨0, 0⟩ · ⟨0,
3882⟩; AND UNDER THE LIBRARY's HEAD SUCH A BOOK IS WHAT THE FRAME's MAKER bookWhole RETURNS AT THE
DESCRIPTION, THE ORDER BEING orderOf OF THE DESCRIPTION, BY NAME. PUBLIC DATA ALONE: entries,
addresses, numbers. Ten theorems; no definition.

- wants_not_w, seg_not_w: TWO EVALUATIONS IN LEAN's KERNEL: of the two pieces of rawAheadW that are
    their makers' terms (the stretches' entries; the carrying entries of the chain of segments) no
    entry has that owner. The second behind the library's equations for String.splitOn and toNat?
    (Johnson/Unfolds/), as in AtFullSide/K14/RawLengthsWritten.lean.
- wants_bite, seg_bite: THE TWO TESTS CAN FAIL: at the owner ⟨⟨1, some 0, 1, .K1⟩, 0⟩ each says no.
- short_at_w: an evaluation: of the eight written pieces (rawShortW,
    AtFullSide/K14/RawEntriesKit.lean) the entries with that owner, as tuples (aheadView,
    Honest/K14/SharedAheadWritten.lean), are the four written entries' tuples, in the list's order.
    short_bent: with the LAST entry's count 122 for 121 the comparison says no.
- none_of_all: a tool: a list of which no entry has an owner is emptied by the filter at that owner.
- aheadW_four: so rawAheadW's entries with that owner ARE the four.
- book_at_w: at every book B with B.ahead = rawAheadW and every order ord: what p spends of the
    owner's coins is one entry e, with e.count = ⟨0, 11⟩ and e.start = ⟨0, 3882⟩; what is known at p
    is one entry x, with x.start = ⟨0, 0⟩ and x.count = ⟨0, 3882⟩. The two other entries go to part
    1 of p's place: Addr.before ord ‹part 1› ‹part 0› is false at every ord.
- book_at_w_head: UNDER THE HEAD (h) ALONE: bookWhole returns a book B at the description, at the
    written lists of sendings and the guessed merges, and the two clauses hold at B and orderOf of
    the description.

ON THE TWO PIECES THAT ARE NOT SPELLED. rawWantsW and rawSegW are their makers' terms behind
"toOption.getD": at a rejection an empty list would stand there, and "no entry has that owner" would
hold of nothing. NOT SO HERE: rawLinks_returns and rawSeg_returns
(RawAheadWritten.lean): each maker returns its term; its RawLengthsWritten.lean: 7,940 and 5,130
members; wants_bite and seg_bite find an owner in each. And book_at_w_head does not rest on the
default: B.ahead = rawAheadW is a theorem at a book that bookWhole RETURNS
(bookWhole_returns_at_head_ahead, AtFullSide/K14/WholeAheadAtHead.lean).

Kin. wants_first, seg_first, filter_off, ahead_at (AtFullSide/K12/TiesAtLaid.lean: a third house's):
the like BY THE RECEIVER's chain: their form is followed; what is known at p wants the filter BY THE
OWNER. MaskFourAt, known_of_four (Honest/K14/BookAtU.lean): the same form of four entries at another
owner, which is written into that definition: not called. knownBy_of_aheadAt
(Honest/K14/OwnerAt.lean): general in the owner: called.

Limits. ALL LIMITS OF THE FILES NAMED HOLD HERE: THAT B IS THE BOOK BY WHICH ANY PLAY OF THE FRAME's
PROVER GOES, OR THE BOOK OF WHAT onlineProverFromPublicFiles YIELDS, IS NOT SAID; the merges are the frame's guess; the
written lists rest on prints held by Lean's kernel against their makers. Entries alone: nothing on
the book's rows or cuts. THE FULL SIZE ALONE. OPTIONS ARE RAISED in front of the evaluations:
maxRecDepth to 1000000; maxHeartbeats is lifted at the four over the makers' terms. In the side
library, because it imports files of it. No property is claimed.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K14.WholeAheadAtHead
import AtFullSide.K14.RawEntriesKit
import Johnson.Desc.ProofFile.Honest.K14.OwnerAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open VerifiableInference.Desc (Chain Place)
open Johnson.G (proofSendsFull)
open P5J (F0T TS)
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Of the stretches' entries none has the owner ⟨⟨1, none, 4, .K1⟩, 0⟩. -/
theorem wants_not_w :
    ((rawWantsW.map (·.entry)).all fun e => e.owner != (⟨⟨1, none, 4, .K1⟩, 0⟩ : Addr)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail: at the opening's sender it says no. -/
theorem wants_bite :
    ((rawWantsW.map (·.entry)).all fun e => e.owner != (⟨⟨1, some 0, 1, .K1⟩, 0⟩ : Addr)) =
      false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Of the carrying entries of the chain of segments none has that owner. -/
theorem seg_not_w : (rawSegW.all fun e => e.owner != (⟨⟨1, none, 4, .K1⟩, 0⟩ : Addr)) = true := by
  unfold rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail: at the opening's sender it says no. -/
theorem seg_bite :
    (rawSegW.all fun e => e.owner != (⟨⟨1, some 0, 1, .K1⟩, 0⟩ : Addr)) = false := by
  unfold rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Of the eight written pieces the entries with that owner are the four. -/
theorem short_at_w :
    decide ((rawShortW.filter (·.owner == (⟨⟨1, none, 4, .K1⟩, 0⟩ : Addr))).map aheadView =
    ([⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
      ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩] : List Ahead).map aheadView) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: the last entry's count 122 for 121. -/
theorem short_bent :
    decide ((rawShortW.filter (·.owner == (⟨⟨1, none, 4, .K1⟩, 0⟩ : Addr))).map aheadView =
    ([⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
      ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 122⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩] : List Ahead).map aheadView) = false := by
  decide +kernel

/-- A list of which no entry has the owner o is emptied by the filter at o. -/
theorem none_of_all (l : List Ahead) (o : Addr) (h : (l.all fun e => e.owner != o) = true) :
    l.filter (·.owner == o) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he h2
  have h1 := List.all_eq_true.1 h e he
  simp [bne, h2] at h1

/-- **rawAheadW's entries with the owner ⟨⟨1, none, 4, .K1⟩, 0⟩ are the four.** -/
theorem aheadW_four :
    rawAheadW.filter (·.owner == (⟨⟨1, none, 4, .K1⟩, 0⟩ : Addr)) =
    [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
      ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩] := by
  have hs : rawShortW.filter (·.owner == (⟨⟨1, none, 4, .K1⟩, 0⟩ : Addr)) =
    [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
      ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩] :=
    List.map_injective_iff.2 aheadView_inj (of_decide_eq_true short_at_w)
  rw [← hs]
  unfold rawAheadW rawShortW
  simp only [List.filter_append, none_of_all _ _ wants_not_w, none_of_all _ _ seg_not_w,
    List.nil_append, List.append_nil]

/-- **What p spends, and what is known at p**, at every book with these entries, at every order. -/
theorem book_at_w {B : ProverCoinCounts} (hB : B.ahead = rawAheadW) (ord : List Place) :
    (∃ e, B.spentBy ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ = [e] ∧
      e.count = ⟨0, 11⟩ ∧ e.start = ⟨0, 3882⟩) ∧
    ∃ x, B.knownBy ord ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ = [x] ∧
      x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, 3882⟩ := by
  have h4 : aheadAt B ⟨⟨1, none, 4, .K1⟩, 0⟩ =
    [⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
      ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
      ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 121⟩,
        ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩] := by
    unfold aheadAt
    rw [hB]
    exact aheadW_four
  have hsp : B.spentBy ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ =
      (aheadAt B ⟨⟨1, none, 4, .K1⟩, 0⟩).filter fun e =>
        e.spender == (⟨⟨3, none, 2, .K12⟩, 0⟩ : Addr) && e.once := by
    unfold ProverCoinCounts.spentBy aheadAt
    rw [List.filter_filter]
    congr 1
    funext e
    simp only [Bool.and_comm, Bool.and_left_comm]
  have hb : (⟨⟨3, none, 2, .K12⟩, 1⟩ : Addr).before ord ⟨⟨3, none, 2, .K12⟩, 0⟩ = false := by
    simp [Addr.before]
  have e1 : ((⟨⟨3, none, 2, .K12⟩, 1⟩ : Addr) == ⟨⟨3, none, 2, .K12⟩, 0⟩) = false := by decide
  have e2 : ((⟨⟨3, none, 2, .K12⟩, 0⟩ : Addr) == ⟨⟨3, none, 2, .K12⟩, 0⟩) = true := by decide
  refine ⟨⟨⟨"the fold's fresh mask to 3.-.2.0: fold", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 3882⟩, ⟨0, 11⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, true⟩, ?_, rfl, rfl⟩,
    ⟨⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3882⟩,
        ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩, ?_, rfl, rfl⟩⟩
  · rw [hsp, h4]
    simp [List.filter_cons, e1, e2]
  · rw [knownBy_of_aheadAt, h4]
    simp [List.filter_cons, e1, e2, hb]

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Under the head: at the book that bookWhole returns at the description**, the order being
orderOf of the description. -/
theorem book_at_w_head {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) :
    ∃ B, bookWhole (F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
        (mergesByName (F0T o Zp Np cF).first.blocksInOrder) = .ok B ∧
      (∃ e, B.spentBy ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩ = [e] ∧
        e.count = ⟨0, 11⟩ ∧ e.start = ⟨0, 3882⟩) ∧
      ∃ x, B.knownBy (orderOf (F0T o Zp Np cF)) ⟨⟨1, none, 4, .K1⟩, 0⟩
          ⟨⟨3, none, 2, .K12⟩, 0⟩ = [x] ∧ x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, 3882⟩ := by
  obtain ⟨B, hB, hA⟩ := bookWhole_returns_at_head_ahead h
  exact ⟨B, hB, book_at_w hA _⟩

end AtFullSide.K1

#print axioms AtFullSide.K1.wants_not_w
#print axioms AtFullSide.K1.wants_bite
#print axioms AtFullSide.K1.seg_not_w
#print axioms AtFullSide.K1.seg_bite
#print axioms AtFullSide.K1.short_at_w
#print axioms AtFullSide.K1.short_bent
#print axioms AtFullSide.K1.none_of_all
#print axioms AtFullSide.K1.aheadW_four
#print axioms AtFullSide.K1.book_at_w
#print axioms AtFullSide.K1.book_at_w_head
