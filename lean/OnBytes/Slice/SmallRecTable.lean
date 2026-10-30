-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecTable.lean: at the small files of the setting "record with work", UNDER THE
THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a hypothesis, which this file does not prove):
the written link, at a decision whose yes gives the yes of the program's link AT THE TWO KEYS THAT
THE PROGRAM MAKES OF TWO TABLES' ROOTS AND ANSWERS (`Params.TableName`), is round-by-round sound at
the pair of records that is read off these keys.

`sr_link_sound` (OnBytes/Slice/SmallRecYes.lean) asks of the two keys that they name the items 0 and
1 and that they hold the records of r. The reader of an entry file makes its keys by `tableKey`
(OnBytes/Entry/Table.lean; OnBytes/Entry/File.lean, `read`), at the items 0 and 1. Such keys name
their items (`Params.tableKey_fits`) and hold what is read off them (OnBytes/Slice/KeyTableRec.lean;
`recsAtR`, OnBytes/Slice/ManyBlkKeysRec.lean). So of the keys nothing is asked but that `tableKey`
has returned them.

Main theorems.
 `sr_keys_hold`         the two keys hold the pair of records that is read off them; by
                         `KeyHasR.unique` they hold no other.
 `sr_link_sound_table`  `sr_link_sound` at these keys and that pair.
 `sr_link_sound_own`    the same at the decision of the program's link itself.

WHAT THEY STILL ASK. `Cb.BCHKS46At`; that `tableKey` has returned the two keys (the reader refuses a
file where it does not); in the first, `hdec`. The digest cfg and the two tables' roots and answers
are letters.

Not claimed. THIS IS NO PROOF OF SOUNDNESS OF AN ENTRY FILE'S CHECK. The written link is an
interactive protocol; nothing here is on hashes, on bytes, or on the reader that makes a view of a
file. The seeds in the records are those that `recordSeeds` gives at the format's names of the two
tables (root, digest and shape, without the answers): that they are drawn after the tables are
fixed, and how often a record then fails to single one table out, is not said; the language
(`Sz.LangE2T`) has three ways out, and where one is open the theorems say nothing. No error count is
evaluated here. All that the heads of OnBytes/Slice/SmallRecYes.lean and KeyTableRec.lean do not
claim.

-/
import OnBytes.Slice.KeyTableRec
import OnBytes.Slice.ManyBlkKeysRec
import OnBytes.Slice.SmallRecYes

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open Params (smallRecordRead)

section
variable (cfg : ByteArray) (first further : Params.TableName) (k0 k1 : TableKey)
  (h0 : tableKey .two cfg smallRecordRead.link.table first 0 = some k0)
  (h1 : tableKey .two cfg smallRecordRead.link.table further 1 = some k1)
include h0 h1

/-- The two keys hold the pair of records that is read off them. -/
theorem sr_keys_hold :
    KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index k0 (recsAtR srS 19 1 k0 k1).1 ∧
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index k1 (recsAtR srS 19 1 k0 k1).2 :=
  ⟨keyHasR_recAtR srS.P.v 19 1 _ k0 sr_linkSizesR.v sr_recordShape.1 sr_recordShape.2
      (Params.tableKey_fits h0).1 (tableKey_nz h0) (tableKey_okE h0),
    keyHasR_recAtR srS.P.v 19 1 _ k1 sr_linkSizesR.v sr_recordShape.1 sr_recordShape.2
      (Params.tableKey_fits h1).1 (tableKey_nz h1) (tableKey_okE h1)⟩

/-- **Under `Cb.BCHKS46At`: the written link, at a decision whose yes gives the yes of the program's
link at the keys of two tables' roots and answers, is round-by-round sound at the pair of records
that is read off the keys**, for `Sz.LangE2T`, which has three ways out. The head lists what is
asked and what is not claimed. -/
theorem sr_link_sound_table (xs : List PQ.XO) (dec : PQ.View → Bool)
    (hdec : ∀ V, dec V = true →
      (linkVerify smallRecordRead.link k0 k1).decides (Entry.start smallRecordRead) V = true)
    (hA : BCHKS46At GF GE) :
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        dec).Sound
      (fun _ y => srS.LangE2T srZ 524285 (recsAtR srS 19 1 k0 k1) y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  sr_link_sound k0 k1 (Params.tableKey_fits h0).2 (Params.tableKey_fits h1).2 xs dec hdec
    (recsAtR srS 19 1 k0 k1) (fun _ _ => (sr_keys_hold cfg first further k0 k1 h0 h1).1)
    (fun _ _ => (sr_keys_hold cfg first further k0 k1 h0 h1).2) hA

/-- The same at the decision of the program's link itself. -/
theorem sr_link_sound_own (xs : List PQ.XO) (hA : BCHKS46At GF GE) :
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        ((linkVerify smallRecordRead.link k0 k1).decides (Entry.start smallRecordRead))).Sound
      (fun _ y => srS.LangE2T srZ 524285 (recsAtR srS 19 1 k0 k1) y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  sr_link_sound_table cfg first further k0 k1 h0 h1 xs _ (fun _ h => h) hA

end

end OnBytes.Slice

#print axioms OnBytes.Slice.sr_keys_hold
#print axioms OnBytes.Slice.sr_link_sound_table
#print axioms OnBytes.Slice.sr_link_sound_own
