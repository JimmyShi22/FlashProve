-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPayCaller.lean.
Premises of the statements on the sub-proofs' lookup that follow from a success which the caller
holds: no number of a parameter file enters.

Main names:
  `shapeOf_ok`: ShapeOf calls pub lid h gives FoNums.ok h = true.
  `pad_ok`: where Forest.pad returns the record g, from a state whose arrays have their sizes and a
    context on a view with no message open: FoNums.ok g.shape = true.
  `planeCols_bounds`, `planeCols_bounds'`: where Forest.planeCols h lm returns (or its toBool is
    true): 5 ≤ lm and lm ≤ h.kT + 5. Who holds that success: in the run, at the very record and
    lm, Forest.planeClaims itself (OnBytes/Tie/Pv/Lookup/Peel/FoPayRun.lean); before the run, the
    three layouts (OnBytes/Tie/Pv/Lookup/Peel/FoPayPlan.lean); Attention.tables tests it too.
  `join_size`: where Forest.join g KF returns and FoNums.ok g.shape: KF.size = g.shape.NC: the
    clause nKF of Fo.CallerOk.
  `Same x`: where the routine x returns, the state and the context are as they were; its rules;
    `same_uEnt`.
  `quiet_u3at`, `quiet_U3at`, `quiet_headCol`: the routines by which attention and the head read the
    columns of the planes are Quiet: the clauses quietB and quietP of Fo.CallerOk at these callers.
Quiet is Cb.Fo.PlaneClaims.Quiet (the state and the context are as they were), not Fo.Quiet of
OnBytes/Tie/Pv/Lookup/Ends/FoAdds.lean (no claim is added). No statement here lays these routines
into Fo.CallerOk.
Said elsewhere too: OnBytes/Tie/Pv/Lookup/Port/FoReads.lean has Quiet of the three sites' own
routines inside Fo.ReadsAt (readsAt_layer, readsAt_attention, readsAt_head: bitQ, pin), tied to the
sites' text; the conclusion of pad_ok is the first clause of a lemma that is not in this library
(Fo.pad_view, OnBytes/Tie/Pv/Lookup/Ends/FoPassKit.lean). The lemmas here say the same of the
routines alone.
Does not say: that any of these routines returns.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieProof
import OnBytes.Model.Attention
import OnBytes.Model.Head

set_option autoImplicit false

namespace Fo.Pay
open Cb Cb.Fo Cb.Fo.PlaneClaims TwV OnBytes OnBytes.Model OnBytes.PscRun

/-! ### the one test on the public numbers -/

theorem shapeOf_ok {calls : Array Call} {pub : Array Nat} {lid : ℕ} {h : Forest.Shape}
    (hS : ShapeOf calls pub lid h) : FoNums.ok h = true := by
  obtain ⟨h0, hs0, hp0, he⟩ := hS
  rw [he]
  exact shape_ok hs0 hp0

theorem pad_ok {calls : Array Call} {pub : Array Nat} {lid : ℕ} {Fk F' : Fork} {c c' : Ctx}
    {g : Forest.Heard} (hr : Forest.pad calls pub lid Fk c = .ok ((g, F'), c')) (hF : Sized Fk)
    (hc : Clean c) : FoNums.ok g.shape = true :=
  shapeOf_ok (hcOut2V Cb.Gl.E Reading.gl calls pub lid 5 Fk F' c c' g hr hF hc).1

/-! ### the rows of the planes' matrix -/

theorem planeCols_bounds {h : Forest.Shape} {lm n : ℕ} (e : Forest.planeCols h lm = .ok n) :
    5 ≤ lm ∧ lm ≤ h.kT + 5 := by
  unfold Forest.planeCols at e
  split at e
  · cases e
  · rename_i hq
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hq
    exact hq

theorem planeCols_bounds' {h : Forest.Shape} {lm : ℕ}
    (e : (Forest.planeCols h lm).toBool = true) : 5 ≤ lm ∧ lm ≤ h.kT + 5 := by
  cases hn : Forest.planeCols h lm with
  | error _ =>
    rw [hn] at e
    cases e
  | ok n => exact planeCols_bounds hn

/-! ### routines that leave the state and the context -/

/-- Where the routine returns, the state and the context are as they were. -/
def Same {α : Type} (x : SubM α) : Prop := ∀ F c r, x F c = .ok r → r.1.2 = F ∧ r.2 = c

section
variable {α β : Type}

theorem Same.pure (a : α) : Same (Pure.pure a : SubM α) := fun F c r h => by
  rw [pure_ok] at h
  rw [h]
  exact ⟨rfl, rfl⟩

theorem Same.bind {x : SubM α} {f : α → SubM β} (hx : Same x) (hf : ∀ a, Same (f a)) :
    Same (x >>= f) := fun F c r h => by
  rw [bind_ok] at h
  obtain ⟨a, G, c1, h1, h2⟩ := h
  obtain ⟨e1, e2⟩ := hx F c _ h1
  obtain rfl : G = F := e1
  obtain rfl : c1 = c := e2
  exact hf a _ _ r h2

theorem Same.mustAs (name : String) (b : Bool) :
    Same (liftM (OnBytes.Model.mustAs name b) : SubM Unit) := fun F c r h => by
  have h2 : (StateT.lift (OnBytes.Model.mustAs name b) : SubM Unit) F c = .ok r := h
  rw [lift_ok] at h2
  obtain ⟨a, c1, h3, rfl⟩ := h2
  unfold OnBytes.Model.mustAs at h3
  split at h3
  · cases h3
    exact ⟨rfl, rfl⟩
  · cases h3

theorem Same.get : Same (MonadState.get : SubM Fork) := fun F c r h => by
  have e : ((F, F), c) = r := Except.ok.inj h
  rw [← e]
  exact ⟨rfl, rfl⟩

end

theorem same_uEnt (t x : ℕ) : Same (uEnt t x) := by
  unfold uEnt
  exact Same.get.bind fun _ => (Same.mustAs _ _).bind fun _ => Same.pure _

/-- Attention's routine for an entry of a table. -/
theorem quiet_u3at (h : Attention.Heard) (t i : ℕ) : Quiet (Attention.u3at h t i) := by
  unfold Attention.u3at
  exact (Same.mustAs _ _).bind fun _ => same_uEnt _ _

/-- The head's routine for an entry of a table. -/
theorem quiet_U3at (R : Head.Run) (t i : ℕ) : Quiet (Head.U3at R t i) := by
  unfold Head.U3at
  exact (Same.mustAs _ _).bind fun _ => same_uEnt _ _

/-- The head's routine for a column of the planes, as Head.claimPlanes writes it. -/
theorem quiet_headCol (R : Head.Run) (t x : ℕ) :
    Quiet (do mustAs "internal-h-table-index" (x < R.L.kb); Head.U3at R t x : SubM Aff) :=
  (Same.mustAs _ _).bind fun _ => quiet_U3at R t x

/-! ### the number of the key forms -/

theorem join_size {g : Forest.Heard} {KF : Array Aff} {F : Fork} {c : Ctx}
    {r : (Aff × Fork) × Ctx} (e : Forest.join g KF F c = .ok r)
    (H : FoNums.ok g.shape = true) : KF.size = g.shape.NC := by
  unfold Forest.join at e
  rw [bind_ok] at e
  obtain ⟨_, G, c1, h1, -⟩ := e
  have h2 : (StateT.lift (OnBytes.Model.mustAs "internal-forest-join"
      (KF.size == g.shape.calls.size && g.e.size == g.shape.calls.size)) : SubM Unit) F c =
      .ok (((), G), c1) := h1
  rw [lift_ok] at h2
  obtain ⟨a, c2, h3, -⟩ := h2
  unfold OnBytes.Model.mustAs at h3
  split at h3
  · rename_i hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact hb.1.trans (ok_parts H).1.2.2.2.2.2.2
  · cases h3

end Fo.Pay
