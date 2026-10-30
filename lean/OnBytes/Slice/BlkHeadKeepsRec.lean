-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkHeadKeepsRec.lean: what the link's steps and the batching keep and leave, from the
start of an entry's chain, for tables with a record and any parameter bytes.

`yes_in_field_manyR` (OnBytes/Slice/ManyBlkWrittenRec.lean) asks `HeadKeepsR`
(OnBytes/Slice/BlkHeadRec.lean) at the tie before the first fold (OnBytes/Slice/BlkTies.lean:
`GroupTie`). This file proves `HeadKeepsR` once, for a run from the start of an entry's chain under
any parameter bytes p, with a few closed facts on the setting as hypotheses.



Main theorem.
 `headKeepsR_entry`   `HeadKeepsR` at any two keys and any view. Asked: the plan has one answer to a
                      sample; the fresh mask is sent with the folded rows; the link's three oracle
                      messages are placed in one tree sh, in the order of sending (`hlay`); a column
                      of sh has each message's symbols in turn (`hmain`, `hmask`); sh has as many
                      leaves as the stage's main code has positions; nZ entries have room in a row
                      of the group's mask code.
Not claimed. That the hypotheses hold at any parameter bytes. Nothing for a link whose fresh mask is
not sent with the folded rows. Nothing on the dry run. Nothing on soundness.

-/
import OnBytes.Slice.BlkHeadRec
import OnBytes.Slice.BlkHeadTieRec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (LinkShape)

/-- What the link's steps and the batching keep and leave, from the start of an entry's chain under
the parameter bytes p, at any two keys and any view. s: the first stage. sh: the one tree of the
link's message. nZ: the number of entries of a mask row of the first stage. -/
theorem headKeepsR_entry (p : Params.Link) (first further : TableKey) (V : Fmt.View) (s : Sg)
    (nZ : ℕ) (sh : TreeShape) (hs : (Entry.start p).samples = 1)
    (hm : p.link.masksAhead = true)
    (hlay : layTrees p.codes (linkMessage p.link 1) =
      some { tree := #[0, 0, 0], part := #[0, 1, 2], shapes := #[sh] })
    (hmain : sh.mainSymbols =
      (((linkMessage p.link 1).toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols =
      (((linkMessage p.link 1).toList.map (·.shape)).map fun s => s.maskRows * 3).toArray)
    (ha : sh.logN = s.C.a)
    (hnZ : nZ ≤ 2 ^ (p.codes.mask.getD p.link.maskCode default).logEll) :
    HeadKeepsR p.link first further (startCtx (Entry.start p) V) V p.codes nZ
      (GroupTie s 0 [rowShape p.link, rowShape p.link, maskShape p.link]
        #[some 0, some (2 ^ ceilLog2 p.link.rows)] #[none, none]) := by
  refine headKeeps_ofR p.link first further (Entry.start p) V p.codes nZ _ rfl rfl hs ?_ hm ?_ ?_
  · intro lay hl
    have hl' : layTrees p.codes (linkMessage p.link 1) = some lay := hl
    rw [hlay] at hl'
    obtain rfl := Option.some.inj hl'
    rfl
  · rw [(linkLay_k _ _).2, Nat.zero_add]
    exact hnZ
  · intro x D c' cd G0 L θ row cf hR hB hn
    have hl : D.lay = { tree := #[0, 0, 0], part := #[0, 1, 2], shapes := #[sh] } := by
      have h : layTrees p.codes (linkMessage p.link 1) = some D.lay := hR.laid
      rw [hlay] at h
      exact (Option.some.inj h).symm
    have hsz : (linkMessage p.link 1).size = 3 := by simp [linkMessage, hm]
    have ht : ∀ i, i < (linkMessage p.link 1).size →
        D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i := by
      intro i hi
      rw [hsz] at hi
      rw [hl]
      have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases h3 with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
    have h := hR.bat_tie hB hm s sh (by rw [hl]) ht hmain hmask ha cf hn
    obtain ⟨e1, -, e3⟩ := start_entry p V
    rw [e1, e3] at h
    exact h

end OnBytes.Slice
