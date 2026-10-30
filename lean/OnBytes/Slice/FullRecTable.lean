-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecTable.lean: at the full-size files of the setting "record with work", UNDER THE
THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a hypothesis, which this file does not prove):
the written link, at a decision whose yes gives the yes of the program's link AT THE TWO KEYS THAT
THE PROGRAM MAKES OF TWO TABLES' ROOTS AND ANSWERS (`Params.TableName`), is round-by-round sound at
the pair of records that is read off these keys.

`fr_link_sound` (OnBytes/Slice/FullRecYes.lean) asks of the two keys that they name the items 0 and
1 and that they hold the records of r. The reader of an entry file makes its keys by `tableKey`
(OnBytes/Entry/Table.lean; OnBytes/Entry/File.lean, `read`), at the items 0 and 1. Such keys name
their items (`Params.tableKey_fits`) and hold what is read off them (OnBytes/Slice/KeyTableRec.lean;
`recsAtR`, OnBytes/Slice/ManyBlkKeysRec.lean). So of the keys nothing is asked but that `tableKey`
has returned them.

Main theorems.
 `fr_keys_hold`         the two keys hold the pair of records that is read off them; by
                         `KeyHasR.unique` they hold no other.
 `fr_link_sound_table`  `fr_link_sound` at these keys and that pair.
 `fr_link_sound_own`    the same at the decision of the program's link itself.

WHAT THEY ASK. `Cb.BCHKS46At`; that `tableKey` has returned the two keys (the reader refuses a
file where it does not); in the first, `hdec`. The digest cfg and the two tables' roots and answers
are letters.

Not claimed. THIS IS NO PROOF OF SOUNDNESS OF AN ENTRY FILE'S CHECK. The written link is an
interactive protocol; nothing here is on hashes, on bytes, or on the reader that makes a view of a
file. The seeds in the records are those that `recordSeeds` gives at the format's names of the two
tables (root, digest and shape, without the answers): that they are drawn after the tables are
fixed, and how often a record then fails to single one table out, is not said; the language
(`Sz.LangE2T`) has three ways out, and where one is open the theorems say nothing. No error count is
evaluated here. All that the heads of OnBytes/Slice/FullRecYes.lean and KeyTableRec.lean do not
claim.

-/
import OnBytes.Slice.KeyTableRec
import OnBytes.Slice.ManyBlkKeysRec
import OnBytes.Slice.FullRecYes

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open Params (recordRead)

section
variable (cfg : ByteArray) (first further : Params.TableName) (k0 k1 : TableKey)
  (h0 : tableKey .two cfg recordRead.link.table first 0 = some k0)
  (h1 : tableKey .two cfg recordRead.link.table further 1 = some k1)
include h0 h1

/-- The two keys hold the pair of records that is read off them. -/
theorem fr_keys_hold :
    KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index k0 (recsAtR frS 29 1 k0 k1).1 ∧
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index k1 (recsAtR frS 29 1 k0 k1).2 :=
  ⟨keyHasR_recAtR frS.P.v 29 1 _ k0 fr_linkSizesR.v fr_recordShape.1 fr_recordShape.2
      (Params.tableKey_fits h0).1 (tableKey_nz h0) (tableKey_okE h0),
    keyHasR_recAtR frS.P.v 29 1 _ k1 fr_linkSizesR.v fr_recordShape.1 fr_recordShape.2
      (Params.tableKey_fits h1).1 (tableKey_nz h1) (tableKey_okE h1)⟩

/-- **Under `Cb.BCHKS46At`: the written link, at a decision whose yes gives the yes of the program's
link at the keys of two tables' roots and answers, is round-by-round sound at the pair of records
that is read off the keys**, for `Sz.LangE2T`, which has three ways out. The head lists what is
asked and what is not claimed. -/
theorem fr_link_sound_table (xs : List PQ.XO) (dec : PQ.View → Bool)
    (hdec : ∀ V, dec V = true →
      (linkVerify recordRead.link k0 k1).decides (Entry.start recordRead) V = true)
    (hA : BCHKS46At GF GE) :
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        dec).Sound
      (fun _ y => frS.LangE2T frZ 402653181 (recsAtR frS 29 1 k0 k1) y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  fr_link_sound k0 k1 (Params.tableKey_fits h0).2 (Params.tableKey_fits h1).2 xs dec hdec
    (recsAtR frS 29 1 k0 k1) (fun _ _ => (fr_keys_hold cfg first further k0 k1 h0 h1).1)
    (fun _ _ => (fr_keys_hold cfg first further k0 k1 h0 h1).2) hA

/-- The same at the decision of the program's link itself. -/
theorem fr_link_sound_own (xs : List PQ.XO) (hA : BCHKS46At GF GE) :
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        ((linkVerify recordRead.link k0 k1).decides (Entry.start recordRead))).Sound
      (fun _ y => frS.LangE2T frZ 402653181 (recsAtR frS 29 1 k0 k1) y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  fr_link_sound_table cfg first further k0 k1 h0 h1 xs _ (fun _ h => h) hA

end

end OnBytes.Slice

#print axioms OnBytes.Slice.fr_keys_hold
#print axioms OnBytes.Slice.fr_link_sound_table
#print axioms OnBytes.Slice.fr_link_sound_own
