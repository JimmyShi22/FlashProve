-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecYes.lean: at the small files of the setting "record with work": a yes of the
program's link gives the yes in the field; and, UNDER THE THEOREM ON CODES, TAKEN AS GIVEN
(`Cb.BCHKS46At`: a hypothesis, which this file does not prove), the written link at a decision
whose yes gives the yes of the program's link is round-by-round sound record by record, for a
language with three ways out and with error counts that are not evaluated here.

`sr_link_joh` (OnBytes/Slice/SmallRecLink.lean) asks a tie to the decision, `hsem`: a yes of the
written decision gives the chain's yes in the field, at the claim that the batching makes of
`srRows`. `yes_in_field_manyR` (OnBytes/Slice/ManyBlkWrittenRec.lean) proves such a tie for the
program's link (OnBytes/Iop/Link.lean: `linkVerify`) at two keys with a record, from public facts on
sizes, codes, shapes, rounds and trees and from `HeadKeepsR`. This file supplies them at the typed
parameter bytes `smallRecordRead` (OnBytes/Slice/SmallRecBlkFacts.lean, SmallRecKeeps.lean) and
joins the two.

Main theorems.
 `sr_yes`          whenever the written link accepts a transcript, the chain's yes in the field
                  holds: the hypothesis `hsem` of `sr_link_joh`. For any two keys that name the
                  items 0 and 1, any pair of records r that the keys hold, and any decision whose
                  yes on a view gives the yes of the program's link at these keys there (`hdec`; the
                  decision of the program's link is one; the port's check of an entry file goes by
                  `Proof.judge`, and that its yes gives this yes is not shown here).
 `sr_link_sound`   `sr_link_joh` without `hsem`.

WHAT `sr_link_sound` STILL ASKS. `Cb.BCHKS46At`; `hdec`; that the keys name the items 0 and 1; that
the keys hold the records of r (`KeyHasR`, OnBytes/Slice/BlkRecRow.lean), asked only of keys whose
sizes fit the tables' shape and of which no seed's factor is the program's 0 (`isZeroE`: three words
0), since the program tests both. That each factor reads as no 0 in the field is part of `KeyHasR`
(a record's factors are not 0); from the program's test it follows only where the factor's words are
below the prime. Keys that meet all four hypotheses on keys exist: the written keys
(`keyHasR_keyOf`, OnBytes/Slice/BlkRecRow.lean), with the items 0 and 1. The keys that the program
makes of two tables' roots and answers meet them wherever `tableKey` returns them
(OnBytes/Slice/SmallRecTable.lean).

Not claimed. THIS IS NO PROOF OF SOUNDNESS OF AN ENTRY FILE'S CHECK. The written link is an
interactive protocol; nothing here is on hashes, on bytes, or on the reader that makes a view and
the keys of a file. No error count is evaluated here: with large counts the statement is true for
free. No transcript is shown here that the program's link accepts at two keys with a record: if it
accepts none, both theorems are true for free (a test that is not in this library evaluates the
decision on a made-up view: a test, no theorem). The language (`Sz.LangE2T`) has three ways out: the
first table does not decode with its record, and at each table a collision at its record's seed;
where one is open the theorem says nothing. How often a collision occurs, and where a key's record
and seeds come from, is not said. That `smallRecordRead` is what a program reads of any file:
OnBytes/Params/EntryDryRecordSmall.lean says what is tied; its digest is typed. All that the heads
of OnBytes/Slice/SmallRecLink.lean, LinkChainJoh.lean and ManyBlkWrittenRec.lean do not claim, but
for `hsem`.

-/
import OnBytes.Slice.ManyBlkWrittenRec
import OnBytes.Slice.SmallRecKeeps

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open Params (smallRecordRead)

section
variable (first further : TableKey) (hi0 : first.item = 0) (hi1 : further.item = 1)
  (xs : List PQ.XO) (dec : PQ.View → Bool)
  (hdec : ∀ V, dec V = true →
    (linkVerify smallRecordRead.link first further).decides (Entry.start smallRecordRead) V = true)
  (r : (srS.lkR srZ).X0)
  (hK0 : first.fits smallRecordRead.link.table = true →
    (first.seeds.all fun x => !isZeroE x.beta) = true →
    KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index first r.1)
  (hK1 : further.fits smallRecordRead.link.table = true →
    (further.seeds.all fun x => !isZeroE x.beta) = true →
    KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index further r.2)

include hi0 hi1 hdec hK0 hK1

/-- **A yes of the program's link gives the yes in the field**: whenever the written link, at a
decision whose yes gives the yes of the program's link at the two keys, accepts a transcript, the
chain's yes in the field holds, at the claim that the batching makes of `srRows` at the pair of
records r, and at the first tree read by `srW` and `srF`. -/
theorem sr_yes (y : (srS.lkR srZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : srC.Bl)
    (hacc : (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4)
        (srRd 5 :: srC.rds) xs dec).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, srC.trL b) = true) :
    srC.Acc (sumStmR srN 97
        (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
          c5).1).1
        (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
          c5).1).2 (drawnE (srRd 5) cA))
      (srW m2.1) (srF m2.1) (srW m2.1) b := by
  obtain ⟨hW, hmems, hE, hm0, hst, hf1, hk, hR, h3, hz, hfm, hfz⟩ := sr_groupFacts
  exact yes_in_field_manyR srS 97 19 1 smallRecordRead.link first further srSt1 srRest sr_test
    sr_rest_len sr_ride.1 (Entry.start smallRecordRead) smallRecordRead.codes (srRd 0) (srRd 1)
    (srRd 2) (srRd 3) (srRd 4) (srRd 5) srC xs dec hdec sr_h0 sr_pub sr_headTrees sr_trees sr_len
    (rowShape smallRecordRead.link) (maskShape smallRecordRead.link) hW _ hmems hE hm0 _ hst hf1 hk
    hR h3 hz hfm hfz sr_start.2.1 hi0 hi1 sr_pads r hK0 hK1 sr_linkSizesR sr_linkFitR sr_batDrawsS
    rfl rfl (fun V => sr_headKeeps first further V) srW y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA
    b hacc

/-- **Under `Cb.BCHKS46At`: at the small files of the setting "record with work", the written link
at a decision whose yes gives the yes of the program's link at the two keys, its batching and its
chain are round-by-round sound at the pair of records r that the keys hold if they pass the
program's two tests, for `Sz.LangE2T`**, which has three ways out. The head lists what is asked and
what is not claimed. -/
theorem sr_link_sound (hA : BCHKS46At GF GE) :
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs dec).Sound
      (fun _ y => srS.LangE2T srZ 524285 r y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  sr_link_joh hA xs dec r fun y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc =>
    sr_yes first further hi0 hi1 xs dec hdec r hK0 hK1 y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b
      hacc

end

end OnBytes.Slice
