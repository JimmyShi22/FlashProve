-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/RngRan.lean: where the Lean verifier's routine that draws the matrix of a
smallness test ends well on a view, it has taken one round off the view, and the list that it lays
into its record is the list of the typed challenge of that round.

OnBytes/Tie/Pv/Psc/PscView.lean says what the channel's calls take off a view, a round at a time,
for the kinds of round of a lookup. Here the same is said of the call that returns the drawn matrix
(trTrits, OnBytes/Model/Rounds.lean) and of the routine drawMatrixF (OnBytes/Model/Tail.lean).
OnBytes/Tie/Pv/Tail/CarryRng.lean says that the record of what was drawn that the kit with hash
blocks makes of a written verifier message holds the list of the typed challenge. Both together:
the routine's record holds the matrix that the typed block puts out on the image of the written
round. Statements and proofs.

Main names:
  `trTrits_view`: the call takes a round without items off the view and returns its list of entries.
  `round_trits`: from a context without an open message: exactly one round; nothing was received.
  `drawMatrix_view`: the routine leaves the sub-proof's state as it was, takes exactly one round,
    and its record is the old one with that round's list of entries, and the list of the matrices'
    first columns.
  `drawMatrix_typed`: if that round's record of what was drawn is the one that the kit with hash
    blocks makes of the written verifier message c of a round d that draws the matrix's entries and
    nothing else: the routine's list is listOf of the typed challenge matOf s d h (valsOf d c).

Limits: nothing on a dry run or on a run that fails. That the view's round is made of the written
round's verifier message is a premise: it is what the function that makes a view of a written
transcript says. The sizes s are a letter in `drawMatrix_typed`: that the round d draws
columns * tau entries at the record's own sizes is the premise OnlyTrits.
-/
import OnBytes.Tie.Pv.Psc.PscView
import OnBytes.Tie.Pv.Tail.CarryRng
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open OnBytes OnBytes.Model OnBytes.PscRun Cb.Pv.Tail

/-- The call that returns the drawn matrix. -/
theorem trTrits_view (columns combinations : Nat) (v : Array Int) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : trTrits columns combinations c = .ok (v, c')) :
    ∃ rv t, pending c = rv :: t ∧ rv.vals = [] ∧ v = rv.drawn.trits.toArray ∧ Clean c' ∧
      c'.ch.left = t := by
  unfold trTrits at h
  rw [bindB_ok] at h
  obtain ⟨_, c1, h1, h⟩ := h
  rw [mustB_ok] at h1
  obtain ⟨-, e1⟩ := h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj e1
  rw [bindB_ok] at h
  obtain ⟨d, c2, h2, h⟩ := h
  rw [pureB_ok] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  obtain ⟨rv, t, hp, hv, rfl, -, hcl, hl⟩ := closeAs_view _ _ _ _ _ _ _ _ hd h2
  exact ⟨rv, t, hp, hv, rfl, hcl, hl⟩

/-- From a context without an open message: exactly one round, in which nothing was received. -/
theorem round_trits (columns combinations : Nat) (v : Array Int) (c c' : Ctx) (hc : Clean c)
    (h : trTrits columns combinations c = .ok (v, c')) :
    ∃ rv, Round c rv c' ∧ sentOf rv = [] ∧ v = rv.drawn.trits.toArray := by
  obtain ⟨rv, t, hp, hv, hx, hcl, hl⟩ := trTrits_view columns combinations v c c' hc.1 h
  have hpc : pending c = c.ch.left := by
    unfold pending Chan.pending
    rw [hc.2]
  rw [hpc] at hp
  refine ⟨rv, ⟨hc, hcl, by rw [hp, hl]⟩, ?_, hx⟩
  unfold sentOf
  rw [hv]
  rfl

/-- The routine that draws the matrix. -/
theorem drawMatrix_view (tl tl' : HTailF2) (F F' : Fork) (c c' : Ctx) (hc : Clean c)
    (h : tl.drawMatrixF F c = .ok ((tl', F'), c')) :
    F' = F ∧ ∃ rv, Round c rv c' ∧ sentOf rv = [] ∧
      tl' = { tl with
        cfF := rv.drawn.trits.toArray
        cfFirst := tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] } := by
  unfold HTailF2.drawMatrixF at h
  rw [bind_ok] at h
  obtain ⟨_, G1, c1, h1, h⟩ := h
  rw [must_ok] at h1
  obtain ⟨-, e1⟩ := h1
  obtain ⟨e1', rfl⟩ := Prod.mk.inj e1
  obtain ⟨-, rfl⟩ := Prod.mk.inj e1'
  rw [bind_ok] at h
  obtain ⟨v, G2, c2, h2, h⟩ := h
  unfold SubM.trits at h2
  rw [lift_ok] at h2
  obtain ⟨v', c3, h3, e2⟩ := h2
  obtain ⟨e2', rfl⟩ := Prod.mk.inj e2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2'
  rw [pure_ok] at h
  obtain ⟨e3, rfl⟩ := Prod.mk.inj h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e3
  obtain ⟨rv, hr, hs, rfl⟩ := round_trits _ _ _ _ _ hc h3
  exact ⟨rfl, rv, hr, hs, rfl⟩

/-- The routine's list is the list of the typed challenge. -/
theorem drawMatrix_typed (tl tl' : HTailF2) (F F' : Fork) (c c' : Ctx) (hc : Clean c)
    (h : tl.drawMatrixF F c = .ok ((tl', F'), c')) (s : Size) (d : Run.PQ.RD)
    (ho : OnlyTrits d (s.columns * s.tau)) (w : (OnBytes.Slice.wRound d).Chal)
    (hv : ∀ rv, Round c rv c' →
      rv.drawn = (Run.ckP .two).dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) w)) :
    tl'.cfF = listOf (matOf s d ho (OnBytes.Slice.valsOf d w)) := by
  obtain ⟨-, rv, hr, -, rfl⟩ := drawMatrix_view tl tl' F F' c c' hc h
  show rv.drawn.trits.toArray = _
  rw [hv rv hr]
  exact drawn_view s d ho w

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.round_trits
#print axioms OnBytes.Tie.Pv.Tail.drawMatrix_view
#print axioms OnBytes.Tie.Pv.Tail.drawMatrix_typed
