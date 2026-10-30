-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Att/HearView.lean: on a view, the stages that the port's routines for an attention
sub-proof's own messages have heard (OnBytes/Tie/Pv/Att/HearStages.lean) are rounds of the view,
taken off it one by one, and the lists heard are what these rounds hold.

Main names:
  StageH.rounds: the lists of a stage, round by round, each with what was sent and what was drawn:
    for a sumcheck: the riders and mu, with eps; each variable's scalars, with its challenge; the
    scalars of the further variable, with beta; the end values, of whose round's draw nothing is
    said. For a round that batches rows: its scalars, with the element drawn. For the round that
    draws a point: no scalar, with the elements drawn.
  heard_view: if the stages were heard from a view's context c to c', then c.ch.pending = rv ++
    c'.ch.pending for rounds rv that hold the stages' lists (RoundsAre,
    OnBytes/Tie/Pv/Psc/Run/ViewRounds.lean); c' is a view's context; and if no message is open at c,
    none is open at c'.
  heard_took: from a context without an open message, in the form Took c rv c'
    (OnBytes/Tie/Pv/Psc/PscView.lean).

Limits: those of OnBytes/Tie/Pv/Psc/Run/ViewRounds.lean.
-/
import OnBytes.Tie.Pv.Att.HearStages
import OnBytes.Tie.Pv.Psc.Run.ViewRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.PscRun (Clean Took drawnOf)

/-- The lists of a stage, round by round. -/
def StageH.rounds : StageH → List RoundH
  | .sum riders _ _ H => partsRounds riders H.mu H.eps H.rs H.sentY H.beta H.v
  | .bat sent _ x => [(sent, some [x])]
  | .point d => [([], some (d.elems.map E.ofTriple))]

/-- The stages heard on a view are rounds of the view. -/
theorem heard_view : ∀ (st : List StageH) (c c' : Ctx), c.ch.dry = false → HeardAs st c c' →
    ∃ rv : List Fmt.RoundView, c.ch.pending = rv ++ c'.ch.pending ∧
      RoundsAre (st.flatMap StageH.rounds) rv ∧ c'.ch.dry = false ∧ (Clean c → Clean c')
  | [], c, c', hd, h => by
    rw [show c' = c from h]
    exact ⟨[], rfl, trivial, hd, id⟩
  | .sum riders ws dY H :: l, c, c', hd, h => by
    obtain ⟨c1, c2, h1, h2⟩ := h
    obtain ⟨rv, a1, a2, a3⟩ := parts_view hd h1
    obtain ⟨rv', b1, b2, b3, b4⟩ := heard_view l c2 c' a3.1 h2
    exact ⟨rv ++ rv', by rw [a1, b1, List.append_assoc], RoundsAre.append a2 b2, b3,
      fun _ => b4 a3⟩
  | .bat sent rows x :: l, c, c', hd, h => by
    obtain ⟨c1, c2, c3, h1, h2, h3, h4⟩ := h
    obtain ⟨d, y, k1, k2, k3⟩ := closeOne_close h2
    obtain ⟨r, a1, a2, a3, a4⟩ := round_view hd h1 k1
    have e3 : c3.ch.pending = c2.ch.pending ∧ Clean c3 := by
      rw [Blk.yields_iff] at h3
      unfold Blk.requireRows at h3
      split at h3
      · split at h3
        · obtain ⟨_, e⟩ := Prod.mk.inj (Except.ok.inj h3)
          rw [← e]
          exact ⟨rfl, a4⟩
        · cases h3
      · cases h3
    obtain ⟨rv', b1, b2, b3, b4⟩ := heard_view l c3 c' e3.2.1 h4
    refine ⟨r :: rv', by rw [a1, ← e3.1, b1]; rfl, ⟨⟨a2, fun l' hl => ?_⟩, b2⟩, b3,
      fun _ => b4 e3.2⟩
    rw [← Option.some.inj hl, drawnOf, ← a3, k2, k3]
    rfl
  | .point d :: l, c, c', hd, h => by
    obtain ⟨c1, h1, h2⟩ := h
    obtain ⟨r, a1, a2, a3, a4⟩ := round_view hd (recvEs_zero c) h1
    obtain ⟨rv', b1, b2, b3, b4⟩ := heard_view l c1 c' a4.1 h2
    refine ⟨r :: rv', by rw [a1, b1]; rfl, ⟨⟨a2, fun l' hl => ?_⟩, b2⟩, b3, fun _ => b4 a4⟩
    rw [← Option.some.inj hl, a3]
    rfl

/-- The same from a context without an open message. -/
theorem heard_took (st : List StageH) (c c' : Ctx) (hc : Clean c) (h : HeardAs st c c') :
    ∃ rv : List Fmt.RoundView, Took c rv c' ∧ RoundsAre (st.flatMap StageH.rounds) rv := by
  obtain ⟨rv, a1, a2, _, a4⟩ := heard_view st c c' hc.1 h
  rw [pending_clean hc, pending_clean (a4 hc)] at a1
  exact ⟨rv, ⟨hc, a4 hc, a1⟩, a2⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.heard_view
#print axioms OnBytes.Tie.Pv.Att.heard_took
