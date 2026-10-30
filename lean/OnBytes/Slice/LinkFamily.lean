-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkFamily.lean: the written link of an entry as ONE verifier on pairs of records, at
the full-size and at the small files of the setting "record with work", and its round-by-round
soundness for all pairs at once, UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a
hypothesis, which this file does not prove).

`fr_link_sound` and `sr_link_sound` (OnBytes/Slice/FullRecYes.lean, SmallRecYes.lean) speak of the
written link at a decision and two keys that are letters, record by record. Here the keys are those
that are written of the pair of records (`keyOf`, OnBytes/Slice/KeyOfRec.lean, with the items 0 and
1), and the decision is the program's link's at these keys. So the pair of records becomes an
argument of one verifier, on one list of rounds, with one list of error counts.

Main definitions: `frKeys`, `frDec`, `frRds`, `frShape`, `accFull`, `frErr`; `srKeys`, `srDec`,
`srRds`, `srShape`, `accSmall`, `srErr`.
Main theorems.
 `fr_shape`      the rounds hang neither on the decision nor on the openings: by rfl.
 `fr_reads`      what the written verifier reads hangs on the verifier's messages alone: by rfl.
 `frKeys_hold`   the written keys hold the records.
 `fr_family`     the family's soundness. The small twins: `sr_..`.
`frDec` and `srDec` are marked irreducible, so that Lean does not evaluate the program's link where
two decisions are compared; `frDec_eq`, `srDec_eq` say what they are.

Not claimed. All that the heads of OnBytes/Slice/FullRecYes.lean and SmallRecYes.lean do not claim.
No error count is evaluated here: with large counts the statements are true for free. The language
(`Sz.LangE2T`) has three ways out. That the written keys are those that a program makes of a file
is not said: the program's keys hang on the public files' digest through the seeds' name. No
transcript is shown that the family accepts.

-/
import OnBytes.Slice.FullRecYes
import OnBytes.Slice.SmallRecYes

set_option autoImplicit false

noncomputable section

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open Params (recordRead smallRecordRead)

/-! ## The full-size files -/

/-- The two keys that are written of a pair of records: `keyOf` (OnBytes/Slice/KeyOfRec.lean) of the
first, with the item 0, and of the second, with the item 1. -/
def frKeys (r : (frS.lkR frZ).X0) : TableKey × TableKey :=
  ({ keyOf (fun β : NZ => β.val) (r.1 : RecP NZ frS.P.v 29 1) with item := 0 },
    { keyOf (fun β : NZ => β.val) (r.2 : RecP NZ frS.P.v 29 1) with item := 1 })

/-- The decision of the program's link at the keys written of a pair of records. -/
def frDec (r : (frS.lkR frZ).X0) : PQ.View → Bool :=
  (linkVerify recordRead.link (frKeys r).1 (frKeys r).2).decides (Entry.start recordRead)

/-- What it is. -/
theorem frDec_eq (r : (frS.lkR frZ).X0) : frDec r =
    (linkVerify recordRead.link (frKeys r).1 (frKeys r).2).decides (Entry.start recordRead) := rfl

attribute [irreducible] frDec

/-- The data of the written link's rounds. -/
abbrev frRds : List PQ.RD :=
  frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds

/-- The written link's rounds: the round in front, then one for each entry of the data. -/
abbrev frShape : Shape := Twin.up (PQ.SOf (ckP .two) frRds)

section
variable (xs : List PQ.XO)

/-- The rounds hang neither on the decision nor on the openings of stored tables. -/
theorem fr_shape (dec : PQ.View → Bool) :
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs dec).shape =
      frShape := rfl

/-- What the written verifier reads of the stored tables and of the prover's oracles hangs on the
verifier's messages alone: not on the decision, the instance or the plain parts. -/
theorem fr_reads (dec dec' : PQ.View → Bool) (ρ : Rho frShape) (pl pl' : Plains frShape) :
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        dec).extReads () ρ =
      (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        dec').extReads () ρ ∧
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        dec).reads () ρ pl =
      (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        dec').reads () ρ pl' := ⟨rfl, rfl⟩

/-- THE FAMILY: the written link's verifier, with the pair of records in the decision. -/
def accFull (r : (frS.lkR frZ).X0) (y : (twoExternalStrings (2 ^ frS.P.T.a) PQ.SgX).Str) (τ : Tr frShape) :
    Bool :=
  (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
    (frDec r)).accept () y τ

end

/-- The list of error counts: that of `fr_link_sound`. -/
def frErr : Err frShape :=
  (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
    (frS.badJ frS.e1)
    (fun _ => listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
    (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL))

/-- The written keys hold the records of which they are written. -/
theorem frKeys_hold (r : (frS.lkR frZ).X0) :
    KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index (frKeys r).1 r.1 ∧
    KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index (frKeys r).2 r.2 :=
  ⟨keyHasR_keyOf r.1 _ fr_linkSizes_par.2.2.2.2.2.2.1 fr_recordNumbers.1 fr_recordNumbers.2.1 0,
    keyHasR_keyOf r.2 _ fr_linkSizes_par.2.2.2.2.2.2.1 fr_recordNumbers.1 fr_recordNumbers.2.1 1⟩

/-- **THE FAMILY's SOUNDNESS, under `Cb.BCHKS46At`**: for every pair of records r and every pair of
stored tables y outside `Sz.LangE2T` at r, the prover has lost, at the start, towards "the written
verifier at r rejects", with one list of error counts for all r. -/
theorem fr_family (hA : BCHKS46At GF GE) (xs : List PQ.XO) (r : (frS.lkR frZ).X0)
    (y : (twoExternalStrings (2 ^ frS.P.T.a) PQ.SgX).Str) (hn : ¬ frS.LangE2T frZ 402653181 r y) :
    Doomed frShape frErr (fun τ => accFull xs r y τ = false) :=
  fr_link_sound (frKeys r).1 (frKeys r).2 rfl rfl xs (frDec r)
    (fun V h => (congrFun (frDec_eq r) V).symm.trans h) r
    (fun _ _ => (frKeys_hold r).1) (fun _ _ => (frKeys_hold r).2) hA () y hn

/-! ## The small files -/

/-- The two keys that are written of a pair of records: `keyOf` (OnBytes/Slice/KeyOfRec.lean) of the
first, with the item 0, and of the second, with the item 1. -/
def srKeys (r : (srS.lkR srZ).X0) : TableKey × TableKey :=
  ({ keyOf (fun β : NZ => β.val) (r.1 : RecP NZ srS.P.v 19 1) with item := 0 },
    { keyOf (fun β : NZ => β.val) (r.2 : RecP NZ srS.P.v 19 1) with item := 1 })

/-- The decision of the program's link at the keys written of a pair of records. -/
def srDec (r : (srS.lkR srZ).X0) : PQ.View → Bool :=
  (linkVerify smallRecordRead.link (srKeys r).1 (srKeys r).2).decides (Entry.start smallRecordRead)

/-- What it is. -/
theorem srDec_eq (r : (srS.lkR srZ).X0) : srDec r =
    (linkVerify smallRecordRead.link (srKeys r).1 (srKeys r).2).decides
      (Entry.start smallRecordRead) := rfl

attribute [irreducible] srDec

/-- The data of the written link's rounds. -/
abbrev srRds : List PQ.RD :=
  srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds

/-- The written link's rounds: the round in front, then one for each entry of the data. -/
abbrev srShape : Shape := Twin.up (PQ.SOf (ckP .two) srRds)

section
variable (xs : List PQ.XO)

/-- The rounds hang neither on the decision nor on the openings of stored tables. -/
theorem sr_shape (dec : PQ.View → Bool) :
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs dec).shape =
      srShape := rfl

/-- What the written verifier reads of the stored tables and of the prover's oracles hangs on the
verifier's messages alone: not on the decision, the instance or the plain parts. -/
theorem sr_reads (dec dec' : PQ.View → Bool) (ρ : Rho srShape) (pl pl' : Plains srShape) :
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        dec).extReads () ρ =
      (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        dec').extReads () ρ ∧
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        dec).reads () ρ pl =
      (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        dec').reads () ρ pl' := ⟨rfl, rfl⟩

/-- THE FAMILY: the written link's verifier, with the pair of records in the decision. -/
def accSmall (r : (srS.lkR srZ).X0) (y : (twoExternalStrings (2 ^ srS.P.T.a) PQ.SgX).Str) (τ : Tr srShape) :
    Bool :=
  (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
    (srDec r)).accept () y τ

end

/-- The list of error counts: that of `sr_link_sound`. -/
def srErr : Err srShape :=
  (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
    (srS.badJ srS.e1)
    (fun _ => listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
    (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL))

/-- The written keys hold the records of which they are written. -/
theorem srKeys_hold (r : (srS.lkR srZ).X0) :
    KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index (srKeys r).1 r.1 ∧
    KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index (srKeys r).2 r.2 :=
  ⟨keyHasR_keyOf r.1 _ sr_linkSizes_par.2.2.2.2.2.2.1 sr_recordNumbers.1 sr_recordNumbers.2.1 0,
    keyHasR_keyOf r.2 _ sr_linkSizes_par.2.2.2.2.2.2.1 sr_recordNumbers.1 sr_recordNumbers.2.1 1⟩

/-- **THE FAMILY's SOUNDNESS, under `Cb.BCHKS46At`**: for every pair of records r and every pair of
stored tables y outside `Sz.LangE2T` at r, the prover has lost, at the start, towards "the written
verifier at r rejects", with one list of error counts for all r. -/
theorem sr_family (hA : BCHKS46At GF GE) (xs : List PQ.XO) (r : (srS.lkR srZ).X0)
    (y : (twoExternalStrings (2 ^ srS.P.T.a) PQ.SgX).Str) (hn : ¬ srS.LangE2T srZ 524285 r y) :
    Doomed srShape srErr (fun τ => accSmall xs r y τ = false) :=
  sr_link_sound (srKeys r).1 (srKeys r).2 rfl rfl xs (srDec r)
    (fun V h => (congrFun (srDec_eq r) V).symm.trans h) r
    (fun _ _ => (srKeys_hold r).1) (fun _ _ => (srKeys_hold r).2) hA () y hn

end OnBytes.Slice

#print axioms OnBytes.Slice.fr_reads
#print axioms OnBytes.Slice.frKeys_hold
#print axioms OnBytes.Slice.fr_family
#print axioms OnBytes.Slice.sr_reads
#print axioms OnBytes.Slice.srKeys_hold
#print axioms OnBytes.Slice.sr_family
