-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecKeeps.lean: what the link's steps and the batching keep and leave, at
the full-size files of the setting "record with work".

`headKeepsR_entry` (OnBytes/Slice/BlkHeadKeepsRec.lean) proves `HeadKeepsR` from the start of an
entry's chain under any parameter bytes, from a few closed facts. This file proves these facts at
the typed parameter bytes `recordRead` (OnBytes/Params/EntryDryRecord.lean), three by an evaluation
in the kernel and three by rfl, and applies the theorem at the sizes `frS`
(OnBytes/Slice/FullRecLink.lean). How the link's three oracle messages are placed is `fr_layTrees1`
of OnBytes/Slice/FullRecBlkSizes.lean.

Main definitions: `frLinkTree`, the one tree of the link's message; `frTie0`, the tie before the
first fold.
Main theorems: `fr_mainSymbols`, `fr_maskSymbols`, `fr_headKeeps`.
Not claimed. Nothing for other parameter bytes. Nothing on what the tree's columns hold. Nothing on
the dry run. Nothing on soundness.

-/
import OnBytes.Slice.BlkHeadKeepsRec
import OnBytes.Slice.FullRecBlkFacts

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (recordRead)

/-- The shape of the one tree of the link's message. -/
def frLinkTree : TreeShape :=
  { logN := 24, logNzk := 13, mainSymbols := #[321, 321, 0], maskSymbols := #[0, 0, 3] }

/-- The words of main rows in a column are those of the three shapes. -/
theorem fr_mainSymbols : frLinkTree.mainSymbols =
    (((linkMessage recordRead.link 1).toList.map (·.shape)).map fun s =>
      s.mainRows * s.mainDeg).toArray := by
  decide +kernel

/-- The words of mask rows in a column are those of the three shapes. -/
theorem fr_maskSymbols : frLinkTree.maskSymbols =
    (((linkMessage recordRead.link 1).toList.map (·.shape)).map fun s =>
      s.maskRows * 3).toArray := by
  decide +kernel

/-- The tie before the first fold: the first tree holds the two folded rows' oracle messages and
the fresh mask. -/
abbrev frTie0 : Ctx → GroupRow → GroupLayout → Nat → Prop :=
  GroupTie (frS.sg 97) 0
    [rowShape recordRead.link, rowShape recordRead.link, maskShape recordRead.link]
    #[some 0, some (2 ^ ceilLog2 recordRead.link.rows)] #[none, none]

/-- What the link's steps and the batching keep and leave, at any two keys and any view. -/
theorem fr_headKeeps (first further : TableKey) (V : Fmt.View) :
    HeadKeepsR recordRead.link first further (startCtx (Entry.start recordRead) V) V
      recordRead.codes frS.P.Z.l frTie0 :=
  headKeepsR_entry recordRead first further V (frS.sg 97) frS.P.Z.l frLinkTree rfl rfl
    fr_layTrees1 fr_mainSymbols fr_maskSymbols rfl (by decide +kernel)

end OnBytes.Slice
