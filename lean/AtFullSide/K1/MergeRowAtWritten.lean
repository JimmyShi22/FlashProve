-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/MergeRowAtWritten.lean: AT THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN SENDINGS AND THE MERGES THAT mergesByName
(Johnson/Desc/ProofFile/Honest/BookWhole.lean) GUESSES: WHATEVER BOOK bookWhole RETURNS THERE: WHAT
A ROW SPENDS WHOSE LAST SPENDING PART IS A MERGE: ALL ITS SPENDING ENTRIES BUT THE LAST ARE ONE
BLOCK OF THE SEGMENT's MASK ROW, WITH A WRITTEN OWNER, FIRST COIN AND COUNT; THE LAST IS THE
MERGE's ENTRY OF THE INDEX-MASK MESSAGE, WITH A WRITTEN NUMBER AND COUNT: WHEREVER ONE PUBLIC TEST
WITH CODE ACCEPTS THE PLACE WITH THESE NUMBERS. THE SISTER OF ANOTHER HOUSE's rawRowOk |
rawRowStretch_of_ok (AtFullSide/K14/RawRowStretch.lean), which serve the rows without a merge:
after its pattern, on its authors' word: "a sister test in a new file
is the right form". PUBLIC DATA ALONE: places, parts, numbers of scalars, where a run of coins
begins: never what stands in it. One definition with code; one theorem. A TRIAL THAT COUNTS IN NO
COLUMN.
NO PROPERTY IS CLAIMED.

mergeRowOk p n i o st ct t e THE TEST: the first chain has a sub-protocol at the place p, of a link
l: none of its rounds is named "FOLD epsilon"; planParts lays n parts for it; none of the parts in
front of number i is among the merges' ends; the part number i has the address ⟨p, i⟩, is among
them, is a sum by the frame's test PartAt.isSum, and has e end values, e not 0; no part behind it
has a scalar of its own; the own scalars of the parts in front, with the merge's own less its end
values, add up to ct, which is not 0; the merges' end values in front of the place, by the maker's
order, add up to t; and rawRowsW (AtFullSide/K14/RawFactsWritten.lean) has at l a mask row with the
owner o, whose entries begin, in the second number, at st less the own scalars of the segment's
parts in front of p. It reads the description, the merges and the written rows: NOT the stretches.
mergeRow_of_ok WHERE IT ACCEPTS: rowEntries B p n 0 = es₁ ++ [the entry of the stretch ⟨⟨p, i⟩,
"ends", rawIdxW, t, e⟩], and oneStretch es₁ = some (o, st, ct): by the frame's
bookWhole_merge_stretch (Johnson/Desc/ProofFile/Honest/BookMergeStretch.lean), the library's
wp_placesOk, rawRows_written and rawIdx_written.

Limits. AN IMPLICATION: that bookWhole returns there is not said here (bookWhole_returns_written,
AtFullSide/K14/BookWholeWritten.lean, has it). THAT ANY DESCRIPTION BUT WP HAS THESE VALUES is not
said; the sendings are found by labels that rest on one print; THE MERGES ARE A GUESS (these three
are the limits of the files called). Coins of the extension field alone, as oneStretch. Nothing on
a sender's text, on a run, or on what any coin is. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K14.RawFactsWritten
import Johnson.Desc.ProofFile.Honest.BookMergeStretch
import Johnson.AtFull.ProofPlan.At.PlacesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest
open AtFullSide.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The test on a place, a number of parts, the merge's number, an owner, a first coin and a
count, and the number and the count of the merge's entry of the index-mask message.** -/
def mergeRowOk (p : Place) (n i : Nat) (o : Addr) (st ct t e : Nat) : Bool :=
  match p.link with
  | none => false
  | some l =>
    WP.first.blocksInOrder.any fun b => b.place == p &&
      (b.rounds.all fun r => r.entry.name != "FOLD epsilon") &&
      (planParts b).length == n &&
      (((planParts b).take i).all fun q =>
        !(mergesByName WP.first.blocksInOrder).ends.contains q.addr) &&
      (((planParts b).drop (i + 1)).all fun q => q.ownScalars == 0) &&
      (match (planParts b)[i]? with
        | none => false
        | some m =>
          m.addr == ⟨p, i⟩ && (mergesByName WP.first.blocksInOrder).ends.contains m.addr && m.isSum &&
            m.endScalars != 0 && m.endScalars == e &&
            ownScalarsOf ((planParts b).take i) + (m.ownScalars - m.endScalars) != 0 &&
            ownScalarsOf ((planParts b).take i) + (m.ownScalars - m.endScalars) == ct) &&
      mergeEndsOf (mergesByName WP.first.blocksInOrder).ends
        (linksInFront WP.first.blocksInOrder l ++ partsInFront WP.first.blocksInOrder l p) == t &&
      rawRowsW.any fun x => x.1 == l && x.2.owner == o &&
        x.2.base.e + ownScalarsOf (partsInFront WP.first.blocksInOrder l p) == st

/-- **WHERE THE TEST ACCEPTS: WHATEVER BOOK bookWhole RETURNS AT WP: ONE BLOCK OF THE MASK ROW, THEN
THE MERGE's ENTRY OF THE INDEX-MASK MESSAGE.** -/
theorem mergeRow_of_ok {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) {p : Place} {n i : Nat} {o : Addr}
    {st ct t e : Nat} (h : mergeRowOk p n i o st ct t e = true) :
    ∃ es₁, rowEntries B p n 0 =
        es₁ ++ [(⟨⟨p, i⟩, "ends", rawIdxW, t, e⟩ : Want).entry] ∧
      oneStretch es₁ = some (o, st, ct) := by
  unfold mergeRowOk at h
  cases hl : p.link with
  | none =>
    rw [hl] at h
    cases h
  | some l =>
    rw [hl] at h
    obtain ⟨b, hb, h1⟩ := List.any_eq_true.1 h
    cases hm : (planParts b)[i]? with
    | none =>
      rw [hm] at h1
      simp at h1
    | some m =>
      rw [hm] at h1
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
      obtain ⟨⟨⟨⟨⟨⟨⟨rfl, hF⟩, hn⟩, hA⟩, hC⟩, hmm⟩, ht⟩, hr⟩ := h1
      obtain ⟨⟨⟨⟨⟨⟨ea, hme⟩, hS⟩, hN⟩, he⟩, hpos⟩, hc⟩ := hmm
      obtain ⟨x, hx, h2⟩ := List.any_eq_true.1 hr
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨e1, e2⟩, e3⟩ := h2
      obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.1 hm
      have hrow : planParts b = (planParts b).take i ++ m :: (planParts b).drop (i + 1) := by
        rw [← hv, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
      obtain ⟨row, idx, es₁, hrw, hix, hE, hO⟩ := bookWhole_merge_stretch hB
        P2Law.ProofPlan.wp_placesOk hb hl
        (fun r hr' => bne_iff_ne.1 (List.all_eq_true.1 hF r hr')) hrow
        (fun q hq hq' => by
          have := List.all_eq_true.1 hA q hq
          rw [List.contains_iff_mem.2 hq'] at this
          cases this)
        (List.contains_iff_mem.1 hme) hS hN
        (fun q hq => beq_iff_eq.1 (List.all_eq_true.1 hC q hq)) hpos
      have hw := rawRows_written x hx
      rw [e1] at hw
      obtain rfl : x.2 = row := Option.some.inj (hw.symm.trans hrw)
      obtain rfl : rawIdxW = idx := Option.some.inj (rawIdx_written.symm.trans hix)
      refine ⟨es₁, ?_, ?_⟩
      · rw [← hn, hE, ea, ht, he]
      · rw [hO, e2, e3, hc]

end AtFullSide.K1

#print axioms AtFullSide.K1.mergeRowOk
#print axioms AtFullSide.K1.mergeRow_of_ok
