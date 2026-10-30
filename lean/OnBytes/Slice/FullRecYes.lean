-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecYes.lean: at the full-size files of the setting "record with work": a yes of
the program's link gives the yes in the field; and, UNDER THE THEOREM ON CODES, TAKEN AS GIVEN
(`Cb.BCHKS46At`: a hypothesis, which this file does not prove), the written link at a decision
whose yes gives the yes of the program's link is round-by-round sound record by record, for a
language with three ways out and with error counts that are not evaluated here.

`fr_link_joh` (OnBytes/Slice/FullRecLink.lean) asks a tie to the decision, `hsem`: a yes of the
written decision gives the chain's yes in the field, at the claim that the batching makes of
`frRows`. `yes_in_field_manyR` (OnBytes/Slice/ManyBlkWrittenRec.lean) proves such a tie for the
program's link (OnBytes/Iop/Link.lean: `linkVerify`) at two keys with a record, from public facts on
sizes, codes, shapes, rounds and trees and from `HeadKeepsR`. This file supplies them at the typed
parameter bytes `recordRead` (OnBytes/Slice/FullRecBlkFacts.lean, FullRecKeeps.lean) and joins the
two.

Main theorems.
 `fr_yes`          whenever the written link accepts a transcript, the chain's yes in the field
                  holds: the hypothesis `hsem` of `fr_link_joh`. For any two keys that name the
                  items 0 and 1, any pair of records r that the keys hold, and any decision whose
                  yes on a view gives the yes of the program's link at these keys there (`hdec`; the
                  decision of the program's link is one; the port's check of an entry file goes by
                  `Proof.judge`, and that its yes gives this yes is not shown here).
 `fr_link_sound`   `fr_link_joh` without `hsem`.

WHAT `fr_link_sound` STILL ASKS. `Cb.BCHKS46At`; `hdec`; that the keys name the items 0 and 1; that
the keys hold the records of r (`KeyHasR`, OnBytes/Slice/BlkRecRow.lean), asked only of keys whose
sizes fit the tables' shape and of which no seed's factor is the program's 0 (`isZeroE`: three words
0), since the program tests both. That each factor reads as no 0 in the field is part of `KeyHasR`
(a record's factors are not 0); from the program's test it follows only where the factor's words are
below the prime. Keys that meet all four hypotheses on keys exist: the written keys
(`keyHasR_keyOf`, OnBytes/Slice/BlkRecRow.lean), with the items 0 and 1. The keys that the program
makes of two tables' roots and answers meet them wherever `tableKey` returns them
(OnBytes/Slice/FullRecTable.lean).

Not claimed. THIS IS NO PROOF OF SOUNDNESS OF AN ENTRY FILE'S CHECK. The written link is an
interactive protocol; nothing here is on hashes, on bytes, or on the reader that makes a view and
the keys of a file. No error count is evaluated here: with large counts the statement is true for
free. No transcript is shown here that the program's link accepts at two keys with a record: if it
accepts none, both theorems are true for free. The language (`Sz.LangE2T`) has three ways out: the
first table does not decode with its record, and at each table a collision at its record's seed;
where one is open the theorem says nothing. How often a collision occurs, and where a key's record
and seeds come from, is not said. That `recordRead` is what a program reads of any file:
OnBytes/Params/EntryDryRecord.lean says what is tied; its digest is typed. All that the heads of
OnBytes/Slice/FullRecLink.lean, LinkChainJoh.lean and ManyBlkWrittenRec.lean do not claim, but for
`hsem`.

-/
import OnBytes.Slice.ManyBlkWrittenRec
import OnBytes.Slice.FullRecKeeps

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open Params (recordRead)

section
variable (first further : TableKey) (hi0 : first.item = 0) (hi1 : further.item = 1)
  (xs : List PQ.XO) (dec : PQ.View → Bool)
  (hdec : ∀ V, dec V = true →
    (linkVerify recordRead.link first further).decides (Entry.start recordRead) V = true)
  (r : (frS.lkR frZ).X0)
  (hK0 : first.fits recordRead.link.table = true →
    (first.seeds.all fun x => !isZeroE x.beta) = true →
    KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index first r.1)
  (hK1 : further.fits recordRead.link.table = true →
    (further.seeds.all fun x => !isZeroE x.beta) = true →
    KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index further r.2)

include hi0 hi1 hdec hK0 hK1

/-- **A yes of the program's link gives the yes in the field**: whenever the written link, at a
decision whose yes gives the yes of the program's link at the two keys, accepts a transcript, the
chain's yes in the field holds, at the claim that the batching makes of `frRows` at the pair of
records r, and at the first tree read by `frW` and `frF`. -/
theorem fr_yes (y : (frS.lkR frZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : frC.Bl)
    (hacc : (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4)
        (frRd 5 :: frC.rds) xs dec).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, frC.trL b) = true) :
    frC.Acc (sumStmR frN 97
        (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
          c5).1).1
        (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
          c5).1).2 (drawnE (frRd 5) cA))
      (frW m2.1) (frF m2.1) (frW m2.1) b := by
  obtain ⟨hW, hmems, hE, hm0, hst, hf1, hk, hR, h3, hz, hfm, hfz⟩ := fr_groupFacts
  exact yes_in_field_manyR frS 97 29 1 recordRead.link first further frSt1 frRest fr_test
    fr_rest_len fr_ride.1 (Entry.start recordRead) recordRead.codes (frRd 0) (frRd 1) (frRd 2)
    (frRd 3) (frRd 4) (frRd 5) frC xs dec hdec fr_h0 fr_pub fr_headTrees fr_trees fr_len
    (rowShape recordRead.link) (maskShape recordRead.link) hW _ hmems hE hm0 _ hst hf1 hk hR h3 hz
    hfm hfz fr_start.2.1 hi0 hi1 fr_pads r hK0 hK1 fr_linkSizesR fr_linkFitR fr_batDrawsS rfl rfl
    (fun V => fr_headKeeps first further V) frW y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc

/-- **Under `Cb.BCHKS46At`: at the full-size files of the setting "record with work", the written
link at a decision whose yes gives the yes of the program's link at the two keys, its batching and
its chain are round-by-round sound at the pair of records r that the keys hold if they pass the
program's two tests, for `Sz.LangE2T`**, which has three ways out. The head lists what is asked and
what is not claimed. -/
theorem fr_link_sound (hA : BCHKS46At GF GE) :
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs dec).Sound
      (fun _ y => frS.LangE2T frZ 402653181 r y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  fr_link_joh hA xs dec r fun y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc =>
    fr_yes first further hi0 hi1 xs dec hdec r hK0 hK1 y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b
      hacc

end

end OnBytes.Slice
