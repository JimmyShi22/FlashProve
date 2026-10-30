-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecKeeps.lean: what the link's steps and the batching keep and leave, at
the small files of the setting "record with work".

`headKeepsR_entry` (OnBytes/Slice/BlkHeadKeepsRec.lean) proves `HeadKeepsR` from the start of an
entry's chain under any parameter bytes, from a few closed facts. This file proves these facts at
the typed parameter bytes `smallRecordRead` (OnBytes/Params/EntryDryRecordSmall.lean), three by an
evaluation in the kernel and three by rfl, and applies the theorem at the sizes `srS`
(OnBytes/Slice/SmallRecLink.lean). How the link's three oracle messages are placed is `sr_layTrees1`
of OnBytes/Slice/SmallRecBlkSizes.lean.

Main definitions: `srLinkTree`, the one tree of the link's message; `srTie0`, the tie before the
first fold.
Main theorems: `sr_mainSymbols`, `sr_maskSymbols`, `sr_headKeeps`.
Not claimed. Nothing for other parameter bytes. Nothing on what the tree's columns hold. Nothing on
the dry run. Nothing on soundness.

-/
import OnBytes.Slice.BlkHeadKeepsRec
import OnBytes.Slice.SmallRecBlkFacts

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (smallRecordRead)

/-- The shape of the one tree of the link's message. -/
def srLinkTree : TreeShape :=
  { logN := 17, logNzk := 13, mainSymbols := #[54, 54, 0], maskSymbols := #[0, 0, 3] }

/-- The words of main rows in a column are those of the three shapes. -/
theorem sr_mainSymbols : srLinkTree.mainSymbols =
    (((linkMessage smallRecordRead.link 1).toList.map (·.shape)).map fun s =>
      s.mainRows * s.mainDeg).toArray := by
  decide +kernel

/-- The words of mask rows in a column are those of the three shapes. -/
theorem sr_maskSymbols : srLinkTree.maskSymbols =
    (((linkMessage smallRecordRead.link 1).toList.map (·.shape)).map fun s =>
      s.maskRows * 3).toArray := by
  decide +kernel

/-- The tie before the first fold: the first tree holds the two folded rows' oracle messages and
the fresh mask. -/
abbrev srTie0 : Ctx → GroupRow → GroupLayout → Nat → Prop :=
  GroupTie (srS.sg 97) 0
    [rowShape smallRecordRead.link, rowShape smallRecordRead.link, maskShape smallRecordRead.link]
    #[some 0, some (2 ^ ceilLog2 smallRecordRead.link.rows)] #[none, none]

/-- What the link's steps and the batching keep and leave, at any two keys and any view. -/
theorem sr_headKeeps (first further : TableKey) (V : Fmt.View) :
    HeadKeepsR smallRecordRead.link first further (startCtx (Entry.start smallRecordRead) V) V
      smallRecordRead.codes srS.P.Z.l srTie0 :=
  headKeepsR_entry smallRecordRead first further V (srS.sg 97) srS.P.Z.l srLinkTree rfl rfl
    sr_layTrees1 sr_mainSymbols sr_maskSymbols rfl (by decide +kernel)

end OnBytes.Slice
