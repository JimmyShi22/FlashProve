-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttSeam.lean.
The attention sub-proof: which key forms its routine hands to the lookup's join.

States:
  claims_join: if a run of Attention.claims (OnBytes/Model/Attention.lean) returns, then the record
    of key forms Fo.joinsA h P.NC has as many forms as the lookup's shape has calls, the lookup's
    record has as many weights, and every call's form has been set once. These are tests that the
    run has passed; no state of the run is named.
  claims_kf: for every NC: the key forms of Fo.joinsA h NC are as many as NC, and the form of call q
    below NC is Fo.kfA h q.
Not here: that the join at these key forms is among the claims that the run has added, and at which
place: OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttAll.lean (claims_added).
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that a run returns, or
that a key form reads the extension of the call's key vector.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttKfVal
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinRun
import OnBytes.Model.Attention

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

/-- What a returning run of the attention sub-proof's claims has tested of the key forms. -/
theorem claims_join (P : Plan) (h : Attention.Heard) (F G : Fork) (c c' : Ctx)
    (hr : Attention.claims P h F c = .ok (((), G), c')) :
    (joinsA h P.NC).kf.size = h.g.shape.calls.size ∧ h.g.e.size = h.g.shape.calls.size ∧
      ((joinsA h P.NC).joined.all (· == 1)) = true := by
  unfold Attention.claims at hr
  rw [bind_ok] at hr
  obtain ⟨_, A0, a0, _, hr⟩ := hr
  rw [bind_ok] at hr
  obtain ⟨j3, A1, a1, h3, hr⟩ := hr
  obtain rfl := claim3_gives h _ _ _ _ _ _ h3
  rw [bind_ok] at hr
  obtain ⟨j4, A2, a2, h4, hr⟩ := hr
  obtain rfl := claim4_gives h _ _ _ _ _ _ h4
  rw [bind_ok] at hr
  obtain ⟨j5, A3, a3, h5, hr⟩ := hr
  obtain rfl := claim5_gives h _ _ _ _ _ _ h5
  rw [bind_ok] at hr
  obtain ⟨_, A4, a4, h6, hr⟩ := hr
  unfold allJoined at h6
  obtain ⟨hall, _⟩ := (mustAs_ok _ _ _ _ _).1 h6
  rw [bind_ok] at hr
  obtain ⟨_, A5, a5, _, hr⟩ := hr
  rw [bind_ok] at hr
  obtain ⟨r, A6, a6, h8, _⟩ := hr
  obtain ⟨k1, k2, _, _, _⟩ := join_ok _ _ _ _ _ _ _ h8
  exact ⟨k1, k2, hall⟩

/-- The key forms that the join is run on. -/
theorem claims_kf (h : Attention.Heard) (NC : ℕ) :
    (joinsA h NC).kf.size = NC ∧
      ∀ q, q < NC → (joinsA h NC).kf.getD q (Aff.ofConst zeroE) = kfA h q :=
  ⟨kf_size h NC, fun q hq => kf_at h NC q hq⟩

end Fo
