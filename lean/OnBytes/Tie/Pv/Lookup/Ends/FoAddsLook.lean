-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAddsLook.lean.
The lookup's own routines of the second pass: which claims they add.

States:
  hideRun_fields: filling slots turns none of the fields that the total and the numbering read.
  quiet_hideRun, quiet_pscRow, quiet_planesAt, quiet_join, quiet_planesAdded: these add no claim
    (quiet_planesAt: if the caller's routine bit adds none).
  planeClaims_three: Forest.planeClaims adds no claim and returns three forms, if the caller's
    routines bit and pin add none.
  added_forms: SubM.lin over a list of forms adds these forms, in their order.
  objects_added: Forest.objects adds the record's rows, in their order.
  planeLins_added: Forest.planeLins adds the three forms that Forest.planeClaims returns from the
    same state and context, if the caller's routines bit and pin add no claim.
  The last three ask that the run returns, from a state with one coefficient for each slot. "Adds"
  is Fo.Added (OnBytes/Tie/Pv/Lookup/Ends/FoAdded.lean): an identity of values.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAdds
import OnBytes.Tie.Pv.Lookup.Forest.FoObjRun
import OnBytes.Model.Look

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem hide_fields {F G : Fork} {j : ℕ} {y f : E} (h : F.hide j y f = some G) :
    G.trees = F.trees ∧ G.LS = F.LS ∧ G.c0 = F.c0 ∧ G.nClaim = F.nClaim ∧ G.theta = F.theta ∧
      G.ns = F.ns := by
  unfold Fork.hide at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hideSteps_fields (f : E) : ∀ (l : List E) (first : ℕ) (F : Fork) (x : ℕ × Fork),
    l.foldlM (Fork.hideStep f) (first, F) = some x →
    x.2.trees = F.trees ∧ x.2.LS = F.LS ∧ x.2.c0 = F.c0 ∧ x.2.nClaim = F.nClaim ∧
      x.2.theta = F.theta ∧ x.2.ns = F.ns
  | [], first, F, x, h => by
    obtain rfl : (first, F) = x := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | y :: l, first, F, x, h => by
    rw [List.foldlM_cons] at h
    cases hh : F.hide first y f with
    | none =>
      have e : Fork.hideStep f (first, F) y = none := by
        show (F.hide first y f).map _ = none
        rw [hh]
        rfl
      rw [e] at h
      exact absurd h (by simp)
    | some H =>
      have e : Fork.hideStep f (first, F) y = some (first + 1, H) := by
        show (F.hide first y f).map _ = _
        rw [hh]
        rfl
      rw [e] at h
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hide_fields hh
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hideSteps_fields f l (first + 1) H x h
      exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

/-- Filling slots turns none of the fields that the total and the numbering read. -/
theorem hideRun_fields {F G : Fork} {first : ℕ} {v : Array E} {f : E}
    (h : F.hideRun first v f = some G) :
    G.trees = F.trees ∧ G.LS = F.LS ∧ G.c0 = F.c0 ∧ G.nClaim = F.nClaim ∧ G.theta = F.theta ∧
      G.ns = F.ns := by
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  cases hx : v.toList.foldlM (Fork.hideStep f) (first, F) with
  | none =>
    rw [hx] at h
    exact absurd h (by simp)
  | some x =>
    rw [hx] at h
    obtain rfl : x.2 = G := Option.some.inj h
    exact hideSteps_fields f v.toList first F x hx

theorem quiet_hideRun (first : ℕ) (v : Array E) (f : E) :
    Quiet (SubM.change (·.hideRun first v f)) := by
  intro F c a G c' hr hs
  obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
  have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
  rw [e2]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hideRun_fields h1
  exact ⟨trivial, [], rfl, added_same hs a1 a2 a3 a4 a5 a6⟩

theorem quiet_pscRow (p : Psc) (S0 : E) (kept : Aff) : Quiet (pscRow p S0 kept) := by
  unfold pscRow
  exact (Quiet.must _).bind fun _ => (quiet_hideRun _ _ _).bind fun _ => Quiet.pure _

theorem quiet_planesAt (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → SubM Aff)
    (hb : ∀ e col, Quiet (bit e col)) : Quiet (Forest.planesAt g lm e bit) := by
  unfold Forest.planesAt
  exact Quiet.foldlM (fun _ col => (hb e col).bind fun _ => Quiet.pure _) _ _

theorem quiet_planesAdded (g : Forest.Heard) : Quiet (Forest.planesAdded g) := Quiet.paid _

theorem quiet_join (g : Forest.Heard) (KF : Array Aff) : Quiet (Forest.join g KF) := by
  unfold Forest.join
  refine Quiet.bind ?_ fun _ => Quiet.bind (Quiet.paid _) fun _ => Quiet.pure _
  quiet

/-- Forest.planeClaims adds no claim and returns three forms. -/
theorem planeClaims_three (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col)) :
    AddsR (Forest.planeClaims g lm bit pin) 0 fun r => r.size = 3 := by
  unfold Forest.planeClaims
  refine AddsR.qbind' (Quiet.must _) fun _ => ?_
  refine AddsR.qbind' (quiet_planesAt g lm 0 bit hb) fun _ => ?_
  refine AddsR.qbind' (quiet_planesAt g lm 1 bit hb) fun _ => ?_
  refine AddsR.qbind' (Quiet.foldlM (fun _ col => (hp col).bind fun _ => Quiet.pure _) _ _)
    fun _ => ?_
  refine AddsR.qbind' (quiet_pscRow _ _ _) fun _ => ?_
  exact AddsR.pure _ rfl

/-- SubM.lin over a list of forms. -/
theorem added_forms {l : List Aff} {F G : Fork} {c c' : Ctx} {u u' : Unit}
    (h : (l.foldlM (fun _ a => SubM.lin a) u) F c = .ok ((u', G), c')) (hs : F.LS.size = F.ns) :
    Added F G (l.map fun f => (f, #[])) :=
  added_lins hs (lins_ok l F G c c' u u' h).1

/-- Forest.objects adds the record's rows. -/
theorem objects_added {g : Forest.Heard} {F G : Fork} {c c' : Ctx}
    (h : Forest.objects g F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) :
    Added F G (g.rows.toList.map fun f => (f, #[])) := by
  obtain ⟨_, G₁, h1, rfl⟩ := objects_ok g F G c c' h
  have a1 := added_lins hs h1
  have := a1.trans (added_paid a1.sized g.owedObjects)
  rwa [List.append_nil] at this

/-- Forest.planeLins adds the three forms that Forest.planeClaims returned inside it. -/
theorem planeLins_added {g : Forest.Heard} {lm : ℕ} {bit : ℕ → ℕ → SubM Aff} {pin : ℕ → SubM Aff}
    (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col)) {F G : Fork} {c c' : Ctx}
    (h : Forest.planeLins g lm bit pin F c = .ok (((), G), c')) (hs : F.LS.size = F.ns) :
    ∃ (pl : Array Aff) (F1 : Fork) (c1 : Ctx),
      Forest.planeClaims g lm bit pin F c = .ok ((pl, F1), c1) ∧ pl.size = 3 ∧
        Added F G (pl.toList.map fun f => (f, #[])) := by
  unfold Forest.planeLins at h
  obtain ⟨pl, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨u, F2, c2, h3, h4⟩ := (bind_ok _ _ _ _ _).1 h2
  obtain ⟨e3, l0, el0, a0⟩ := planeClaims_three g lm bit pin hb hp _ _ _ _ _ h1 hs
  obtain rfl := List.length_eq_zero_iff.mp el0
  have h3' : (pl.toList.foldlM (fun _ a => SubM.lin a) ()) F1 c1 = .ok ((u, F2), c2) := by
    rw [Array.foldlM_toList]
    exact h3
  have a1 := added_forms h3' a0.sized
  obtain ⟨_, l2, el2, a2⟩ := quiet_planesAdded g _ _ _ _ _ h4 a1.sized
  obtain rfl := List.length_eq_zero_iff.mp el2
  have := (a0.trans a1).trans a2
  rw [List.nil_append, List.append_nil] at this
  exact ⟨pl, F1, c1, h1, e3, this⟩

end Fo
