-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscHide.lean: laws on the slots of a sub-proof's state: what Fork.hide and
Fork.hideRun write under their slots, and what they leave alone.

The state is Fork (OnBytes/Model/Hide.lean). Under a slot it keeps a scalar that was shown, a factor
and a mark that the slot is taken.

Main names:
  `Sized F`: the three arrays on slots that Fork.hide writes have the length F.ns. `sized_slots`.
  `hide_ok`: what one successful call of Fork.hide has written.
  `Filled F G first l factor`: what a run from the slot first on has done. `hideList_ok`,
    `hideRun_ok`, `Filled.next`, `Filled.ns`.
  `Filled.world`: in the world of Fork.worldOf the value under the slot first + i is what was shown
    there minus the factor times the slot's mask entry.
  `Filled.shown`: what was shown under a slot of the run.
  `publicPart_slot`: the public part of the form of one slot is, read, what was shown there.
Limits: as in OnBytes/Model/Hide.lean, hidden is the name of a value's part in the protocol. Nothing
is said on hiding.
-/
import OnBytes.Model.HideLaws

set_option autoImplicit false

namespace OnBytes.Model.Road

/-- The three arrays on slots that Fork.hide writes have the length ns (Fork.slots makes them so).
-/
structure Sized (F : Fork) : Prop where
  vp : F.vp.size = F.ns
  mf : F.mf.size = F.ns
  got : F.gotF.size = F.ns

theorem sized_slots (F : Fork) (n : Nat) : Sized (F.slots n) :=
  ⟨by simp [Fork.slots], by simp [Fork.slots], by simp [Fork.slots]⟩

theorem getD_set_same {α : Type} (a : Array α) (j : Nat) (x d : α) (h : j < a.size) :
    (a.set! j x).getD j d = x := by
  simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, h]

theorem getD_set_other {α : Type} (a : Array α) (i j : Nat) (x d : α) (h : i ≠ j) :
    (a.set! j x).getD i d = a.getD i d := by
  simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, h.symm]

/-- One hidden value. -/
theorem hide_ok (F G : Fork) (j : Nat) (s f : E) (h : F.hide j s f = some G) :
    j < F.ns ∧ F.gotF.getD j true = false ∧
      G = { F with gotF := F.gotF.set! j true, vp := F.vp.set! j s, mf := F.mf.set! j f } := by
  unfold Fork.hide at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hc
    exact ⟨hc.1.1, hc.2, (Option.some.inj h).symm⟩
  · cases h

/-- What a run of hidden values from the slot first on has done. -/
structure Filled (F G : Fork) (first : Nat) (l : List E) (factor : E) : Prop where
  frame : G = { F with gotF := G.gotF, vp := G.vp, mf := G.mf }
  sized : Sized G
  room : first + l.length ≤ F.ns ∨ l = []
  here : ∀ i, i < l.length → G.vp.getD (first + i) zeroE = l.getD i zeroE ∧
    G.mf.getD (first + i) zeroE = factor ∧ G.gotF.getD (first + i) false = true ∧
    F.gotF.getD (first + i) true = false
  other : ∀ j, (j < first ∨ first + l.length ≤ j) → G.vp.getD j zeroE = F.vp.getD j zeroE ∧
    G.mf.getD j zeroE = F.mf.getD j zeroE ∧ ∀ d, G.gotF.getD j d = F.gotF.getD j d

theorem hideList_ok (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep factor) (first, F) = some x → Sized F → Filled F x.2 first l factor
  | [], first, F, x, h, hs => by
    simp only [List.foldlM_nil] at h
    have e : x = (first, F) := (Option.some.inj h).symm
    rw [e]
    exact ⟨rfl, hs, Or.inr rfl, fun i hi => by simp at hi, fun j _ => ⟨rfl, rfl, fun _ => rfl⟩⟩
  | y :: l, first, F, x, h, hs => by
    simp only [List.foldlM_cons] at h
    cases hh : Fork.hideStep factor (first, F) y with
    | none => rw [hh] at h; cases h
    | some z =>
      rw [hh] at h
      simp only [Fork.hideStep] at hh
      cases hH : F.hide first y factor with
      | none => rw [hH] at hh; cases hh
      | some H =>
        rw [hH] at hh
        have ez : z = (first + 1, H) := (Option.some.inj hh).symm
        rw [ez] at h
        obtain ⟨a1, a2, a3⟩ := hide_ok F H first y factor hH
        have sH : Sized H := by
          rw [a3]
          exact ⟨by simp [Array.set!_eq_setIfInBounds, hs.vp],
            by simp [Array.set!_eq_setIfInBounds, hs.mf],
            by simp [Array.set!_eq_setIfInBounds, hs.got]⟩
        have ih := hideList_ok factor l (first + 1) H x h sH
        have nsH : H.ns = F.ns := by rw [a3]
        have vH : H.vp = F.vp.set! first y := by rw [a3]
        have mH : H.mf = F.mf.set! first factor := by rw [a3]
        have gH : H.gotF = F.gotF.set! first true := by rw [a3]
        refine ⟨?_, ih.sized, Or.inl ?_, ?_, ?_⟩
        · rw [ih.frame, a3]
        · rcases ih.room with r | r
          · rw [nsH] at r; simp only [List.length_cons]; omega
          · rw [r]; simp only [List.length_cons, List.length_nil]; omega
        · intro i hi
          cases i with
          | zero =>
            obtain ⟨o1, o2, o3⟩ := ih.other first (Or.inl (by omega))
            rw [Nat.add_zero, o1, o2, o3, vH, mH, gH]
            exact ⟨getD_set_same _ _ _ _ (by rw [hs.vp]; exact a1),
              getD_set_same _ _ _ _ (by rw [hs.mf]; exact a1),
              getD_set_same _ _ _ _ (by rw [hs.got]; exact a1), a2⟩
          | succ i =>
            obtain ⟨b1, b2, b3, b4⟩ := ih.here i (by simpa using hi)
            rw [show first + (i + 1) = first + 1 + i by omega]
            refine ⟨by rw [b1]; rfl, b2, b3, ?_⟩
            rw [gH, getD_set_other _ _ _ _ _ (by omega)] at b4
            exact b4
        · intro j hj
          have hj' : j < first + 1 ∨ first + 1 + l.length ≤ j := by
            simp only [List.length_cons] at hj; omega
          have hne : j ≠ first := by
            simp only [List.length_cons] at hj; omega
          obtain ⟨o1, o2, o3⟩ := ih.other j hj'
          rw [o1, o2, vH, mH, getD_set_other _ _ _ _ _ hne, getD_set_other _ _ _ _ _ hne]
          refine ⟨rfl, rfl, fun d => ?_⟩
          rw [o3, gH, getD_set_other _ _ _ _ _ hne]

/-- Fork.hideRun. -/
theorem hideRun_ok (F G : Fork) (first : Nat) (v : Array E) (factor : E)
    (h : F.hideRun first v factor = some G) (hs : Sized F) : Filled F G first v.toList factor := by
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  split at h
  · rename_i x hx
    rw [← Option.some.inj h]
    exact hideList_ok factor v.toList first F x hx hs
  · cases h

theorem Filled.next {F G : Fork} {first : Nat} {l : List E} {factor : E}
    (a : Filled F G first l factor) : G.next = F.next := by rw [a.frame]

theorem Filled.ns {F G : Fork} {first : Nat} {l : List E} {factor : E}
    (a : Filled F G first l factor) : G.ns = F.ns := by rw [a.frame]

/-- The hidden value under a slot of the run, in the world of Fork.worldOf: what was shown minus the
factor
times the slot's mask entry. -/
theorem Filled.world {K : Type} [CommRing K] (ρ : Reading K) {F G : Fork} {first : Nat} {l : List E}
    {factor : E} (a : Filled F G first l factor) (mask : Nat → K) (entry : Nat → Nat → Nat → K)
    (i : Nat) (hi : i < l.length) :
    (G.worldOf ρ mask entry).slot (first + i) =
      ρ.val (l.getD i zeroE) - ρ.val factor * mask (first + i) := by
  obtain ⟨b1, b2, _, _⟩ := a.here i hi
  show ρ.val (G.vp.getD (first + i) zeroE) - ρ.val (G.mf.getD (first + i) zeroE) * mask (first + i)
      = _
  rw [b1, b2]

/-- What was shown under a slot of the run. -/
theorem Filled.shown {F G : Fork} {first : Nat} {l : List E} {factor : E}
    (a : Filled F G first l factor) (i : Nat) (hi : i < l.length) :
    G.shown (first + i) = some (l.getD i zeroE) := by
  obtain ⟨b1, _, b3, _⟩ := a.here i hi
  have hr : first + i < G.ns := by
    rw [a.ns]
    rcases a.room with r | r
    · omega
    · rw [r] at hi; simp at hi
  unfold Fork.shown
  rw [b3, b1]
  simp [hr]

/-- The public part of the form "the hidden value under one slot" is, read, what was shown there. -/
theorem publicPart_slot {K : Type} [CommRing K] (ρ : Reading K) (G : Fork) (j : Nat) (y τ : E)
    (hy : G.shown j = some y) (h : G.publicPart (Aff.slot j) = some τ) : ρ.val τ = ρ.val y := by
  unfold Fork.publicPart Aff.slot at h
  simp only [← Array.foldlM_toList, List.foldlM_cons, List.foldlM_nil, hy, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
  rw [← h, ρ.add, ρ.mul, ρ.one, ρ.zero]
  ring

#print axioms hideRun_ok
#print axioms Filled.world
#print axioms publicPart_slot

end OnBytes.Model.Road
