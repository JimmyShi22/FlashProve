-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/BatRan.lean: where the Lean verifier's routine that draws the element whose
powers weigh a sub-proof's linear claims ends well on a view, it has taken one round off the view,
and the element that it lays into the sub-proof's state is the one that this round draws.

OnBytes/Tie/Pv/Tail/EndFirst.lean says what that routine (t2Batch, OnBytes/Model/Trees.lean) keeps
of the state. Here: what it takes off a view, and which element it lays. Then, as in
OnBytes/Tie/Pv/Tail/RngView.lean for the draw of the matrix: if the rounds not yet begun are the
view that is made of a written transcript (rvT, OnBytes/Maker/Trees.lean), the element, read in
the library's field, is the one element among the typed values of the first written verifier
message (elemsV, valsOf, OnBytes/Slice/Draws.lean). Statements and proofs.

Main names:
  `batOpen_round`: the call that closes the round and returns the one drawn element, from a context
    without an open message: exactly one round is taken; nothing was received; it draws that
    element and no other.
  `t2Batch_view`: the routine: the mark that the element is drawn is set; exactly one round is
    taken; nothing was received; the round draws the state's element theta and no other.
  `elems_read`: the elements that a round of the view draws, read in the library's field, are the
    elements among the typed values of the written verifier message.
  `t2Batch_rvT`: on the view of a written transcript: the elements among the typed values of the
    first written verifier message are just the reading of theta, and the rounds not yet begun are
    the view of the rest.

Limits: nothing on a dry run or on a run that fails. That a run reaches the routine with just these
rounds not yet begun, and that the file's accept has passed the round's test of work, is for whoever
cuts the file's run. No map to a typed round is laid here.
-/
import OnBytes.Tie.Pv.Tail.EndFirst
import OnBytes.Tie.Pv.Tail.RngView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Tail.Port

/-- The call that closes the round and returns the one drawn element. -/
theorem batOpen_round (x : E) (c c' : Ctx) (hc : PscRun.Clean c)
    (h : trBatchOpen c = .ok (x, c')) :
    ∃ rv, PscRun.Round c rv c' ∧ PscRun.sentOf rv = [] ∧ PscRun.drawnOf rv = [x] := by
  unfold trBatchOpen at h
  rw [PscRun.bindB_ok] at h
  obtain ⟨d, c2, h2, h⟩ := h
  obtain ⟨hx, rfl⟩ := PscRun.oneOf_ok _ _ _ _ h
  obtain ⟨rv, t, hp, hv, rfl, -, hcl, hl⟩ := PscRun.closeAs_view _ _ _ _ _ _ _ _ hc.1 h2
  have hpc : PscRun.pending c = c.ch.left := by
    unfold PscRun.pending Chan.pending
    rw [hc.2]
  rw [hpc] at hp
  refine ⟨rv, ⟨hc, hcl, by rw [hp, hl]⟩, ?_, hx⟩
  unfold PscRun.sentOf
  rw [hv]
  rfl

/-- The routine that draws the batching element, on a view. -/
theorem t2Batch_view (used : Nat) (L L' : LinkCtx) (F G : Fork) (c c' : Ctx) (u : Unit)
    (hc : PscRun.Clean c) (h : t2Batch used L F c = .ok (((u, L'), G), c')) :
    G.thetaDrawnF = true ∧
      ∃ rv, PscRun.Round c rv c' ∧ PscRun.sentOf rv = [] ∧ PscRun.drawnOf rv = [G.theta] := by
  unfold t2Batch at h
  simp only [bindL_ok, subL_ok, getL_ok, setL_ok, LinkM.mustAs, lift_ok, mustAs_ok, ask_ok,
    change_ok, SubM.batchBy, Option.some.injEq] at h
  obtain ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, a1, _, _, _, ⟨⟨ha1, rfl, rfl⟩, rfl⟩,
    _, _, _, _, ⟨⟨⟨_, rfl⟩, rfl⟩, rfl⟩, _, _, _, _, ⟨⟨⟨_, rfl⟩, rfl⟩, rfl⟩,
    _, _, Ff, _, ⟨⟨hfill, rfl⟩, rfl⟩, dr, _, Fo, co, ⟨hopen, rfl⟩, _, _, Fb, _, ⟨⟨hb, rfl⟩, rfl⟩,
    _, _, _, _, ⟨⟨⟨hnz, rfl⟩, rfl⟩, rfl⟩, _, _, Fk, _, ⟨⟨hk, rfl⟩, rfl⟩, _, rfl, rfl⟩ := h
  obtain ⟨hopen', rfl⟩ := (lift_ok trBatchOpen _ _ _ _ _).1 hopen
  unfold Fork.batchBy at hb
  split_ifs at hb
  obtain rfl := Option.some.inj hb
  subst hfill hk ha1
  exact ⟨rfl, batOpen_round dr _ _ hc hopen'⟩

/-- The elements that a round of the view draws, read in the library's field. -/
theorem elems_read (d : RDT) (w : (roundT (Run.ckP .two) d).up.Chal) :
    (((Run.ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) w)).elems.map
      E.ofTriple).map Reading.gl.val = elemsV _ (valsOf (rdOf d) w) := by
  rw [← collect_elems, List.map_map]
  rfl

/-- The routine on the view of a written transcript. -/
theorem t2Batch_rvT (used : Nat) (L L' : LinkCtx) (F G : Fork) (x x' : Ctx) (u : Unit)
    (hc : PscRun.Clean x) (h : t2Batch used L F x = .ok (((u, L'), G), x')) (d : RDT)
    (ds : List RDT) (m : (roundT (Run.ckP .two) d).up.Msg)
    (w : (roundT (Run.ckP .two) d).up.Chal) (τ : Tr (uLT (Run.ckP .two) ds))
    (hl : x.ch.left =
      rvT (Run.ckP .two) (d :: ds) ((m, w, τ) : Tr (uLT (Run.ckP .two) (d :: ds)))) :
    elemsV _ (valsOf (rdOf d) w) = [Reading.gl.val G.theta] ∧
      x'.ch.left = rvT (Run.ckP .two) ds τ := by
  obtain ⟨-, rv, hR, -, hd⟩ := t2Batch_view used L L' F G x x' u hc h
  obtain ⟨rfl, h2⟩ := List.cons.inj (hl.symm.trans hR.2.2)
  refine ⟨?_, h2.symm⟩
  rw [← elems_read d w]
  exact congrArg (List.map Reading.gl.val) hd

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.batOpen_round
#print axioms OnBytes.Tie.Pv.Tail.t2Batch_view
#print axioms OnBytes.Tie.Pv.Tail.elems_read
#print axioms OnBytes.Tie.Pv.Tail.t2Batch_rvT
