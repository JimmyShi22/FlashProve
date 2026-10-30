-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTiedA.lean.
The attention sub-proof's whole check, cut at its named routines.

`a_run_tied`: if Attention.run P returns r from the link's state Lc, the state F and the context c,
then these routines have returned, in this order, each with its arguments written out as terms of P
and of what the earlier ones returned, and EACH FROM THE STATES AND THE CONTEXT IN WHICH THE ONE
BEFORE IT ENDED: Attention.hear, from the state F.fillL.slots P.ns and the context c; rootInH;
Attention.tables (a block: it has the context alone); closeFuns (a function); transcriptF of the
smallness test; Seam.batch, with the number of planned claims set to P.nLin in the state;
Attention.claims, for the record `aHeard P f t`; objectsF; Seam.finish; countsHeld, which ends in
the run's own end state r.1.2 and context r.2. The lines of the run between these turn neither the
states nor the context.
What each of these runs says is said by the statements on that routine. Nothing is said of a run
that does not return.
Dropped, though the run has them: that the tests between these routines passed (under the names
internal-f-fun-closed, internal-slot-count, internal-f-fun-moved, and the test of noFreeSlot).
Attention.claims is not cut: from which states Forest.join and Forest.planeLins run inside it, and
on which key forms, is said by no statement here.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPass

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The record that the attention sub-proof's claims read. -/
def aHeard (P : Attention.Plan) (f : Attention.First) (t : Attention.Tables) : Attention.Heard :=
  { S := P.S, g := f.g, planes := f.planes, scores := f.scores, d := f.d, x := f.x, t := t,
    iU3 := P.iU3 }

theorem a_run_tied (P : Attention.Plan) (Lc : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((Unit × LinkCtx) × Fork) × Ctx) (h : Attention.run P Lc F c = .ok r) :
    ∃ (f : Attention.First) (t : Attention.Tables) (Fh : Fork) (ch : Ctx) (L2 : LinkCtx)
      (Ft : Fork) (ct cr : Ctx) (tl1 tl2 tl3 : HTailF2) (Lt : LinkCtx) (Gt : Fork) (cr' : Ctx)
      (Lb : LinkCtx) (Gb : Fork) (cb : Ctx) (Gc : Fork) (cc : Ctx) (Go : Fork) (co : Ctx)
      (Gf : Fork) (cf : Ctx),
      Attention.hear P (F.fillL.slots P.ns) c = .ok ((f, Fh), ch) ∧
      rootInH [P.iU3] Lc Fh ch = .ok ((((), L2), Ft), ct) ∧
      Attention.tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x ct = .ok (t, cr) ∧
      ({ P.seam.tl with funClosed := false, foldDrawn := 0 } : HTailF2).closeFuns t.funs =
        some tl1 ∧
      tl1.transcriptF L2 Ft cr = .ok (((tl2, Lt), Gt), cr') ∧
      Attention.Seam.batch Gt.next Lt { Gt with planClaimsF := P.nLin } cr' =
        .ok ((((), Lb), Gb), cb) ∧
      Attention.claims P (aHeard P f t) Gb cb = .ok (((), Gc), cc) ∧
      tl2.objectsF t.funs Gc cc = .ok ((tl3, Go), co) ∧
      Attention.Seam.finish tl3 P.seam.nU Lb Go co = .ok ((((), r.1.1.2), Gf), cf) ∧
      Attention.countsHeld P tl3 Gf cf = .ok (((), r.1.2), r.2) := by
  obtain ⟨⟨⟨u, Lr⟩, Gr⟩, cq⟩ := r
  unfold Attention.run at h
  rw [linkBind_ok'] at h
  obtain ⟨tl, L1, A0, e0, h0, h⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl⟩ : tl = { P.seam.tl with funClosed := false, foldDrawn := 0 } ∧
      L1 = Lc ∧ A0 = F.fillL.slots P.ns ∧ e0 = c := by
    unfold Attention.Seam.start at h0
    rw [linkBind_ok'] at h0
    obtain ⟨_, _, B, d, a1, a2⟩ := h0
    obtain ⟨b1, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 a1
    obtain ⟨_, hG, e⟩ := (change_ok _ _ _ _).1 b1
    obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
    obtain rfl := Option.some.inj hG
    have e := (linkPure_ok _ _ _ _ _).1 a2
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
    exact ⟨rfl, rfl, rfl, rfl⟩
  rw [linkBind_ok'] at h
  obtain ⟨f, _, _, _, h1, h⟩ := h
  obtain ⟨k1, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h1
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h2, h⟩ := h
  rw [linkBind_ok'] at h
  obtain ⟨_, _, _, _, h3, h⟩ := h
  obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h3
  rw [linkBind_ok'] at h
  obtain ⟨t, _, _, _, h4, h⟩ := h
  obtain ⟨k4, rfl, rfl⟩ := (linkBlk_ok _ _ _ _ _ _ _ _).1 h4
  cases hcf : ({ P.seam.tl with funClosed := false, foldDrawn := 0 } : HTailF2).closeFuns
      t.funs with
  | none =>
    simp only [hcf] at h
    cases h
  | some tl1 =>
    simp only [hcf] at h
    rw [linkBind_ok'] at h
    obtain ⟨tl2, _, _, _, h5, h⟩ := h
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h6, h⟩ := h
    obtain ⟨k6, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h6
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using (slot_ok _ _ _).1 k6
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h7, h⟩ := h
    obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h7
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h8, h⟩ := h
    obtain ⟨k8, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h8
    obtain ⟨_, hG8, e8⟩ := (change_ok _ _ _ _).1 k8
    obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e8
    obtain rfl := Option.some.inj hG8
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h9, h⟩ := h
    obtain ⟨k9, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h9
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using (slot_ok _ _ _).1 k9
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h10, h⟩ := h
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h11, h⟩ := h
    obtain ⟨k11, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h11
    rw [linkBind_ok'] at h
    obtain ⟨tl3, _, _, _, h12, h⟩ := h
    obtain ⟨k12, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h12
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h13, h⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ :=
      subLine (IdleS.bind IdleS.get fun _ => IdleS.lift (IdleB.testAs _ _)) h13
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h14, h⟩ := h
    obtain ⟨rfl, rfl, rfl, -⟩ := blkLine (IdleB.mustAs _ _) h14
    rw [linkBind_ok'] at h
    obtain ⟨_, _, _, _, h15, h⟩ := h
    obtain ⟨kE, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h
    exact ⟨f, t, _, _, _, _, _, _, tl1, tl2, tl3, _, _, _, _, _, _, _, _, _, _, _, _,
      k1, h2, k4, hcf, h5, h10, k11, k12, h15, kE⟩

end Fo
