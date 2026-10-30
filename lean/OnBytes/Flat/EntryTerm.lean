-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/EntryTerm.lean: the two types of records `RecFull`, `RecSmall`, which the three files'
description takes from here; and an entry's link, WHICH IS NOT THE DESCRIPTION's ENTRY PROTOCOL (see
"Where the term stands"), as ONE term of the type of the field `link` of Hiop/RecSubs.lean's
`SubsR`, made by the maker of OnBytes/Maker/Terminal.lean, at the full-size and at the small files
of the setting "record with work"; and that its rounds and its verifier are those of the family of
OnBytes/Slice/LinkFamily.lean.

How the term stands to the maker's own. `iorLink C a key p r` (OnBytes/Maker/Link.lean) takes the
tables' depth a from its caller and the rounds' data `(linkData p r).ds` from the rounds r;
`linkValue C a key p` (OnBytes/Maker/LinkValue.lean) is `iorLink` at the rounds `linkRounds p` that
the dry run of the link's block states. The family, its soundness and its list of error counts are
stated at the letters `frRds`. `linkData recordRead recordRounds` is `frD` by `rfl`
(`linkData_full`), and `frD.ds = frRds` is a theorem (`fr_ds_C`) that rests on evaluations by Lean's
kernel (`decide +kernel`); Lean's elaborator does not take `rfl` for it. So the term is laid at the
letters `frRds`, by the same maker (`iorBlkX`), so that the list of error counts types over its
rounds; and it is proved equal to `iorLink` and to `linkValue` at the depth `frS.P.T.a`.

Where the term stands. `threeProtocolsFromDryRunAtFullSize` | `threeProtocolsFromDryRunAtSmallSize` (OnBytes/Flat/FilesAt.lean) do not hold
`entryFull` | `entrySmall`: their entry is the written link `linkSibFull` | `linkSibSmall`
(OnBytes/Flat/LinkSibAt.lean), at the same rounds' entries carried by `PQ.ofLib` into another type
(`dsFull`, `dsSmall`; `dsFull_eq`, `dsSmall_eq`), the same depth and openings, and a decision that
at `recX rr` is the verifier program's `linkVerify` at the keys of the two records
(`decFullX_recX`). What the description takes from this file is the two types alone. No theorem of
this library says that the two verifiers decide alike. SO EVERY CONCLUSION AT `entryFull` |
`entrySmall` STANDS AT ANOTHER OBJECT THAN THE DESCRIPTION's ENTRY.

Main definitions: `RecFull`, `entryFull`; `RecSmall`, `entrySmall`. Main theorems. `linkData_full`,
`linkData_small` the maker's description is the line's: by rfl. `entryFull_shape` its rounds are
`frShape`: by rfl. `entryFull_out` its verifier outputs something exactly where `accFull frD.xs`
says yes. `linkRounds_full` the rounds that the dry run states are `recordRounds`. `entryFull_is`
`iorLink (ckP .two) frS.P.T.a keyOf recordRead recordRounds = entryFull`. `entryFull_value`
`linkValue (ckP .two) frS.P.T.a keyOf recordRead = entryFull`. `fr_depth` the depth in the maker's
description is `frS.P.T.a`. `linkOk_full` the dry run at keys of zeros returns. The small twins:
`entrySmall_..`, `linkRounds_small`, `linkOk_small`, `sr_depth`. Of the sixteen theorems only
`entryFull_out` and `entrySmall_out` have a caller in another file of this library.

Not claimed. No soundness is stated here. That `recordRounds` are the rounds that the dry run of the
block gives at every pair of records. All that the heads of OnBytes/Slice/LinkFamily.lean and
OnBytes/Maker/Link.lean do not claim.

-/
import OnBytes.Slice.LinkFamily
import OnBytes.Maker.LinkValueLaws

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood _root_.Run Blocks OnBytes.Slice OnBytes.Maker
open Params (recordRead recordRounds smallRecordRead smallRecordRounds)

/-- The maker's description of the chain is the line's. -/
theorem linkData_full : linkData recordRead recordRounds = frD := rfl

/-- The same at the small files. -/
theorem linkData_small : linkData smallRecordRead smallRecordRounds = srD := rfl

/-- The rounds that the dry run of the link's block states are `recordRounds`. -/
theorem linkRounds_full : linkRounds recordRead = recordRounds := by
  unfold linkRounds
  rw [Params.record_rounds]
  rfl

/-- The same at the small files. -/
theorem linkRounds_small : linkRounds smallRecordRead = smallRecordRounds := by
  unfold linkRounds
  rw [Params.small_record_rounds]
  rfl

/-- The dry run of the link's block at keys of zeros succeeds. -/
theorem linkOk_full : OnBytes.Maker.linkOk recordRead = true := by
  unfold OnBytes.Maker.linkOk
  rw [Params.record_rounds]
  rfl

/-- The same at the small files. -/
theorem linkOk_small : OnBytes.Maker.linkOk smallRecordRead = true := by
  unfold OnBytes.Maker.linkOk
  rw [Params.small_record_rounds]
  rfl

/-! ## The full-size files -/

/-- A record at this size, in plain letters. -/
abbrev RecFull : Type := RecP NZ frS.P.v 29 1

/-- **The entry's link at this size, made by the maker of OnBytes/Maker/Terminal.lean** from the
block of the program's link at the keys written of a pair of records, at the rounds' data `frRds`,
the depth of the tables' code and the description's openings of stored tables. -/
abbrev entryFull : IOR (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) PQ.SgX) Unit extNone :=
  iorBlkX (ckP .two) frRds frS.P.T.a frD.xs
    (linkBlock (keyOf (fun β : NZ => β.val) : RecFull → TableKey) recordRead)
    (Entry.start recordRead)

/-- Its rounds are the written link's. -/
theorem entryFull_shape : entryFull.shape = frShape := rfl

/-- Its verifier is the family's. -/
theorem entryFull_out (r : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) PQ.SgX).Str)
    (τ : Tr frShape) :
    entryFull.out r y τ = if accFull frD.xs r y τ then some () else none := by
  unfold accFull
  rw [frDec_eq]
  rfl

/-- **It is the maker's `iorLink`** at the typed parameter bytes, the dry run's rounds and the depth
of the tables' code. -/
theorem entryFull_is :
    iorLink (ckP .two) frS.P.T.a (keyOf (fun β : NZ => β.val) : RecFull → TableKey) recordRead
      recordRounds = entryFull :=
  congrArg (fun ds => iorBlkX (ckP .two) ds frS.P.T.a frD.xs
    (linkBlock (keyOf (fun β : NZ => β.val) : RecFull → TableKey) recordRead)
    (Entry.start recordRead)) fr_ds_C

/-- **It is the maker's `linkValue`**: `iorLink` at the rounds that the parameter bytes give. -/
theorem entryFull_value :
    linkValue (ckP .two) frS.P.T.a (keyOf (fun β : NZ => β.val) : RecFull → TableKey) recordRead =
      entryFull := by
  rw [linkValue_of_ok _ _ _ _ linkOk_full, linkRounds_full]
  exact entryFull_is

/-- The depth of the stored tables in the maker's description is that of the tables' code. -/
theorem fr_depth : linkDepth recordRead = frS.P.T.a := by
  unfold linkDepth
  rw [linkRounds_full]
  exact fr_a

/-! ## The small files -/

/-- A record at this size, in plain letters. -/
abbrev RecSmall : Type := RecP NZ srS.P.v 19 1

/-- **The entry's link at this size, made by the maker of OnBytes/Maker/Terminal.lean** from the
block of the program's link at the keys written of a pair of records, at the rounds' data `srRds`,
the depth of the tables' code and the description's openings of stored tables. -/
abbrev entrySmall : IOR (RecSmall × RecSmall) (twoExternalStrings (2 ^ srS.P.T.a) PQ.SgX) Unit extNone :=
  iorBlkX (ckP .two) srRds srS.P.T.a srD.xs
    (linkBlock (keyOf (fun β : NZ => β.val) : RecSmall → TableKey) smallRecordRead)
    (Entry.start smallRecordRead)

/-- Its rounds are the written link's. -/
theorem entrySmall_shape : entrySmall.shape = srShape := rfl

/-- Its verifier is the family's. -/
theorem entrySmall_out (r : RecSmall × RecSmall) (y : (twoExternalStrings (2 ^ srS.P.T.a) PQ.SgX).Str)
    (τ : Tr srShape) :
    entrySmall.out r y τ = if accSmall srD.xs r y τ then some () else none := by
  unfold accSmall
  rw [srDec_eq]
  rfl

/-- **It is the maker's `iorLink`** at the typed parameter bytes, the dry run's rounds and the depth
of the tables' code. -/
theorem entrySmall_is :
    iorLink (ckP .two) srS.P.T.a (keyOf (fun β : NZ => β.val) : RecSmall → TableKey) smallRecordRead
      smallRecordRounds = entrySmall :=
  congrArg (fun ds => iorBlkX (ckP .two) ds srS.P.T.a srD.xs
    (linkBlock (keyOf (fun β : NZ => β.val) : RecSmall → TableKey) smallRecordRead)
    (Entry.start smallRecordRead)) sr_ds_C

/-- **It is the maker's `linkValue`**: `iorLink` at the rounds that the parameter bytes give. -/
theorem entrySmall_value :
    linkValue (ckP .two) srS.P.T.a (keyOf (fun β : NZ => β.val) : RecSmall → TableKey)
      smallRecordRead = entrySmall := by
  rw [linkValue_of_ok _ _ _ _ linkOk_small, linkRounds_small]
  exact entrySmall_is

/-- The depth of the stored tables in the maker's description is that of the tables' code. -/
theorem sr_depth : linkDepth smallRecordRead = srS.P.T.a := by
  unfold linkDepth
  rw [linkRounds_small]
  exact sr_a

end OnBytes.Flat

#print axioms OnBytes.Flat.entryFull_out
#print axioms OnBytes.Flat.entryFull_is
#print axioms OnBytes.Flat.entryFull_value
#print axioms OnBytes.Flat.fr_depth
#print axioms OnBytes.Flat.entrySmall_out
#print axioms OnBytes.Flat.entrySmall_is
#print axioms OnBytes.Flat.entrySmall_value
#print axioms OnBytes.Flat.sr_depth
