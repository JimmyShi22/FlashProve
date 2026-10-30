-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/HearPoint.lean: how many elements the round that draws a point has drawn.

Main names:
  close_last: a round that Blk.close (OnBytes/Iop/Ground.lean) has closed has drawn as many elements
    as its entry of the plan says, and that entry is the channel's last one.
  closeAs_elems: so a round that closeAs (OnBytes/Model/Rounds.lean) has closed for n elements has
    drawn n.
  point_said: SubM.point .zero n, where it succeeds: the state is untouched; the open message's
    round is closed under the name ZERO; n elements were drawn, and they are returned.

Limits: one direction: from a call's success. On a view and in the dry run alike.
-/
import OnBytes.Tie.Pv.Att.HearKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Road

theorem close_last (name : String) (kind : Fmt.Kind) (nz : Nat) (d : Fmt.Drawn) (c c' : Ctx)
    (h : (Blk.close name kind nz).Yields c d c') :
    ∃ e : Fmt.Entry, c'.ch.last = some e ∧ d.elems.length = e.drawE := by
  rw [Blk.yields_iff] at h
  unfold Blk.close at h
  split at h
  · cases h
  · rename_i e es he
    split at h
    · cases h
    · split at h
      · obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨e, by rw [← h2], by rw [← h1]; simp [Blk.dryDrawn]⟩
      · simp only at h
        split at h
        · cases h
        · rename_i r t hl
          split at h
          · rename_i hc
            obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            exact ⟨e, by rw [← h2], by rw [← h1]; exact hc.1.1.2⟩
          · cases h

theorem closeAs_elems (name : String) (kind : Fmt.Kind) (elems nz entries : Nat) (d : Fmt.Drawn)
    (c c' : Ctx) (h : (closeAs name kind elems nz entries).Yields c d c') :
    d.elems.length = elems := by
  unfold closeAs at h
  obtain ⟨_, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨d1, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨e, c3, h3, k3⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
  obtain ⟨_, c4, h4, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
  obtain ⟨m4, _⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨e5, _⟩ := (Blk.yields_pure _ _ _ _).1 k4
  obtain ⟨e', l1, l2⟩ := close_last _ _ _ d1 c1 c2 h2
  have he : e = e' := by
    rw [Blk.yields_iff] at h3
    unfold Blk.lastEntry at h3
    rw [l1] at h3
    exact (congrArg Prod.fst (Except.ok.inj h3)).symm
  simp only [Bool.and_eq_true, beq_iff_eq] at m4
  rw [e5, l2, ← he]
  exact m4.1.1

/-- The round that draws a point. -/
theorem point_said (n : Nat) (F G : Fork) (c c' : Ctx) (pts : Array E)
    (h : SubM.point .zero n F c = .ok ((pts, G), c')) :
    G = F ∧ ∃ d : Fmt.Drawn, (Blk.close RoundName.zero.name .elems 0).Yields c d c' ∧
      pts = (d.elems.map E.ofTriple).toArray ∧ d.elems.length = n := by
  unfold SubM.point at h
  obtain ⟨y, e⟩ := (liftY_ok _ _ _ _ _ _).1 h
  unfold trPoint at y
  obtain ⟨_, c0, h0, k0⟩ := (Blk.yields_bind _ _ _ _ _).1 y
  obtain ⟨_, m2⟩ := (mustAs_ok _ _ _ _ _).1 ((Blk.yields_iff _ _ _ _).1 h0)
  obtain ⟨d, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 k0
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k1
  rw [m2] at h1
  refine ⟨e, d, ?_, e1, closeAs_elems _ _ _ _ _ _ _ _ h1⟩
  rw [e2]
  exact closeAs_close _ _ _ _ _ _ _ _ h1

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.close_last
#print axioms OnBytes.Tie.Pv.Att.closeAs_elems
#print axioms OnBytes.Tie.Pv.Att.point_said
