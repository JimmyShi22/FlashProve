-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Ends/PiecesFTail.lean: TailOK and its Bool test tailTest
(OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean) at every record that HTailF2.piecesF
(OnBytes/Model/Tail.lean), a routine of the Lean verifier under OnBytes/, returns.

The one premise of each theorem is that piecesF has returned the record, on any argument.

How it is proved. piecesF runs Forest.shape on the record's two lookup calls and Forest.pubAsk on
that shape with the counts of padding keys, and keeps the shape with these counts as f9
(`piecesF_tail_port_cut`). Where both return, the shape passes FoNums.ok (Cb.Fo.shape_ok), which
gives Port.OK (Cb.Fo.ok_portOK); the number of calls is the length of the list of calls
(Cb.Fo.shape_more). These are the fields port and nc. The fields pc, rows and one are
piecesF_tail_lay (OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailLay.lean), and the field cnt is
piecesF_tail_cnt (OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailCnt.lean).

Main names:
  `piecesF_tail_port`: the fields port and nc of TailOK.
  `piecesF_tailOK`: TailOK, all six fields.
  `piecesF_tailTest`: tailTest is true.

What is not claimed: that piecesF returns a record at any input; anything on a record that is made
otherwise or that a later routine has turned. piecesF ends with heard := none, and Fo.tail_four_law
(OnBytes/Tie/Pv/Lookup/Ends/FoTailLaw.lean), which has TailOK as a premise, asks for a record with
heard = some g: to use that law, TailOK must first be carried to such a later record, which is not
done here. That TailOK is the right thing to ask of a record is not shown. Nothing on soundness,
completeness or hiding.
-/
import OnBytes.Model.Tail
import OnBytes.Tie.Pv.Lookup.Digits.PortLaws
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTailCnt
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTailLay
import OnBytes.Tie.Pv.Lookup.Ends.ShapePrem
import OnBytes.Tie.Pv.Lookup.Forest.FoHole
import OnBytes.Tie.Pv.Lookup.Port.FoShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PiecesF
open OnBytes OnBytes.Model OnBytes.DgP Cb.LdLkp Cb.Lkp

/-- What the value of piecesF holds of the routine's calls of Forest.shape and Forest.pubAsk: both
have returned, at the record's own two calls, and f9 is that shape with the counts that were
asked. -/
theorem piecesF_tail_port_cut {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) :
    ∃ f9 pub, Forest.shape #[tl.z1.call, tl.z2.call] tl0.lidb = .ok f9 ∧
      Forest.pubAsk f9 pub = .ok () ∧ tl.f9 = { f9 with pub := pub } := by
  unfold HTailF2.piecesF at h
  obtain ⟨_, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨f9, hs, h⟩ := Ends.ok_of_bind h
  obtain ⟨pub, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, hp, h⟩ := Ends.ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨f9, pub, hs, hp, rfl⟩

/-- Wherever piecesF returns a record, the record meets the fields port and nc of TailOK. -/
theorem piecesF_tail_port :
  ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl → Port.OK tl.f9 ∧ tl.f9.NC = 2 := by
  intro tl0 tl h
  obtain ⟨f9, pub, hs, hp, ef⟩ := piecesF_tail_port_cut h
  rw [ef]
  exact ⟨Cb.Fo.ok_portOK (Cb.Fo.shape_ok hs hp), (Cb.Fo.shape_more hs).2.1⟩

/-- Wherever piecesF returns a record, the record meets TailOK. -/
theorem piecesF_tailOK :
  ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl → TailOK tl := by
  intro tl0 tl h
  obtain ⟨hport, hnc⟩ := piecesF_tail_port tl0 tl h
  obtain ⟨hpc, hrows, hone⟩ := piecesF_tail_lay tl0 tl h
  exact ⟨hport, hnc, hpc, hrows, hone, piecesF_tail_cnt tl0 tl h⟩

/-- Wherever piecesF returns a record, the record passes tailTest. -/
theorem piecesF_tailTest :
  ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl → tailTest tl = true := by
  intro tl0 tl h
  have H := piecesF_tailOK tl0 tl h
  simp only [tailTest, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨H.port, H.nc⟩, H.pc⟩, H.rows⟩, H.one⟩, H.cnt⟩

end Fo.PiecesF
