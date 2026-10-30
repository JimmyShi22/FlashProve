-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscForm.lean: what the public part of a form (`Fork.publicPart`,
OnBytes/Model/Hide.lean) reads, and what it has to do with the form's value.

Theorems with their proofs, for every reading ρ (`Reading`, OnBytes/Model/HideLaws.lean).

Main names:
  `publicPart_value`: where the public part is given, every slot that the form names is below the
    number of slots and filled, and the public part reads as the form's constant plus the sum over
    its slots of coefficient times what was shown.
  `value_public`: for a form without entries of virtual rows: its value in the world of
    `Fork.worldOf` is the public part minus the sum over its slots of coefficient times factor times
    mask entry.
  `value_later`, `value_later_public`: a form all of whose slots are filled has the same value at
    every later state (`Later`, OnBytes/Tie/Pv/Psc/PscLater.lean).
  `hideRun_slot`, `pscEnds_slot`, `pscRow_slot`: what lies under the slots of a sumcheck's end
    values and of its own scalars in the world of every later state.
  `lins_slots`, `lins_later`: adding a list of claims (`Fork.lins`) leaves what lies under the
    slots.

Limits: nothing on forms with entries of virtual rows in `value_public`. Nothing on soundness, on an
honest prover or on hiding.


-/
import OnBytes.Model.HideLaws
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The loop of `Fork.publicPart`, read. -/
theorem publicLoop_value (F : Fork) : ∀ (l : List (Nat × E)) (v t : E),
    l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y)) v =
      some t →
    (∀ x ∈ l, x.1 < F.ns ∧ Filled F x.1) ∧
      ρ.val t = ρ.val v + (l.map fun x => ρ.val x.2 * ρ.val (F.vp.getD x.1 zeroE)).sum
  | [], v, t, h => by
    obtain rfl : v = t := by simpa using h
    simp
  | x :: l, v, t, h => by
    rw [List.foldlM_cons] at h
    cases hs : F.shown x.1 with
    | none => simp [hs] at h
    | some y =>
      rw [hs] at h
      obtain ⟨h1, h2, rfl⟩ := (shown_iff F x.1 y).1 hs
      obtain ⟨a, b⟩ := publicLoop_value F l _ t h
      refine ⟨?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨h1, h2⟩
        · exact a z hz
      · rw [b, ρ.add, ρ.mul, List.map_cons, List.sum_cons]
        ring

/-- What the public part of a form reads. -/
theorem publicPart_value (F : Fork) (a : Aff) (t : E) (h : F.publicPart a = some t) :
    (∀ x ∈ a.slots.toList, x.1 < F.ns ∧ Filled F x.1) ∧
      ρ.val t = ρ.val a.const +
        (a.slots.toList.map fun x => ρ.val x.2 * ρ.val (F.vp.getD x.1 zeroE)).sum := by
  unfold Fork.publicPart at h
  rw [← Array.foldlM_toList] at h
  exact publicLoop_value ρ F _ _ _ h

/-- The value of a form without entries of virtual rows, by its public part. -/
theorem value_public (F : Fork) (a : Aff) (t : E) (h : F.publicPart a = some t)
    (he : a.ents = #[]) (mask : Nat → K) (entry : Nat → Nat → Nat → K) :
    a.value ρ (F.worldOf ρ mask entry) = ρ.val t -
      (a.slots.toList.map fun x => ρ.val x.2 * (ρ.val (F.mf.getD x.1 zeroE) * mask x.1)).sum := by
  rw [(publicPart_value ρ F a t h).2]
  unfold Aff.value
  rw [he]
  simp only [List.map_nil, List.sum_nil, zero_add]
  generalize a.slots.toList = l
  induction l with
  | nil => simp
  | cons x l ih =>
    have e : slotValue ρ (F.worldOf ρ mask entry) x =
        ρ.val x.2 * (ρ.val (F.vp.getD x.1 zeroE) - ρ.val (F.mf.getD x.1 zeroE) * mask x.1) := rfl
    simp only [List.map_cons, List.sum_cons, e]
    linear_combination ih

/-- A form all of whose slots are filled has the same value at every later state. -/
theorem value_later {F G : Fork} (h : Later F G) (a : Aff)
    (hs : ∀ x ∈ a.slots.toList, Filled F x.1) (mask : Nat → K) (entry : Nat → Nat → Nat → K) :
    a.value ρ (G.worldOf ρ mask entry) = a.value ρ (F.worldOf ρ mask entry) := by
  unfold Aff.value
  congr 1
  congr 1
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨-, h2, h3⟩ := h.keep x.1 (hs x hx)
  show ρ.val x.2 * (ρ.val (G.vp.getD x.1 zeroE) - ρ.val (G.mf.getD x.1 zeroE) * mask x.1) =
    ρ.val x.2 * (ρ.val (F.vp.getD x.1 zeroE) - ρ.val (F.mf.getD x.1 zeroE) * mask x.1)
  rw [h2, h3]

/-- So has a form whose public part is given. -/
theorem value_later_public {F G : Fork} (h : Later F G) (a : Aff) (t : E)
    (hp : F.publicPart a = some t) (mask : Nat → K) (entry : Nat → Nat → Nat → K) :
    a.value ρ (G.worldOf ρ mask entry) = a.value ρ (F.worldOf ρ mask entry) :=
  value_later ρ h a (fun x hx => ((publicPart_value ρ F a t hp).1 x hx).2) mask entry

/-- Under the slots of a run of values lies, in the world of every later state, what was shown less
the factor times the mask entry. -/
theorem hideRun_slot {F G H : Fork} {first : Nat} {v : Array E} {factor : E} (hF : Sized F)
    (h : F.hideRun first v factor = some G) (hl : Later G H) (mask : Nat → K)
    (entry : Nat → Nat → Nat → K) (i : Nat) (hi : i < v.size) :
    (H.worldOf ρ mask entry).slot (first + i) =
      ρ.val (v.getD i zeroE) - ρ.val factor * mask (first + i) := by
  obtain ⟨-, -, h3, -⟩ := hideRun_ok F G first v factor hF h
  obtain ⟨-, -, f1, f2, f3⟩ := h3 i hi
  obtain ⟨-, k2, k3⟩ := hl.keep _ f1
  show ρ.val (H.vp.getD (first + i) zeroE) -
    ρ.val (H.mf.getD (first + i) zeroE) * mask (first + i) = _
  rw [k2, k3, f2, f3]

/-- The end values of a sumcheck, in the world of every later state. -/
theorem pscEnds_slot {p : Psc} {degreeInY n : Nat} {F G H : Fork} {c c' : Ctx} {e : Nat} {p' : Psc}
    (hF : Sized F) (h : pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) (hl : Later G H)
    (mask : Nat → K) (entry : Nat → Nat → Nat → K) :
    ∃ (beta : E) (v : Array E), v.size = n ∧ p'.r.back? = some beta ∧ ∀ j, j < n →
      (H.worldOf ρ mask entry).slot (e + j) =
        ρ.val (v.getD j zeroE) - ρ.val beta * mask (e + j) := by
  obtain ⟨_, beta, v, -, -, -, -, hv, -, -, hG, rfl⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h
  refine ⟨beta, v, hv, by simp, fun j hj => ?_⟩
  exact hideRun_slot ρ (took_sized _ hF) hG hl mask entry j (by omega)

/-- Under the slots of a sumcheck's own scalars lie, once its claim is made, in the world of every
later state, the mask entries themselves: the coefficients of the hiding polynomial. -/
theorem pscRow_slot {p : Psc} {S0 : E} {kept : Aff} {F G H : Fork} {c c' : Ctx} {row : Aff}
    {p' : Psc} (hF : Sized F) (h : pscRow p S0 kept F c = .ok (((row, p'), G), c'))
    (hl : Later G H) (mask : Nat → K) (entry : Nat → Nat → Nat → K) (i : Nat)
    (hi : i < p.walk.1.length) :
    (H.worldOf ρ mask entry).slot (p.first + i) = mask (p.first + i) := by
  obtain ⟨-, -, -, -, -, hG, -, -⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h
  rw [hideRun_slot ρ hF hG hl mask entry i (by simpa using hi)]
  have e : (Array.replicate p.walk.1.length zeroE).getD i zeroE = zeroE := by
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [e, ρ.zero, ρ.sub, ρ.zero, ρ.one]
  ring

/-- Adding a list of claims leaves what lies under the slots. -/
theorem lins_slots {F G : Fork} {l : List Aff} (h : F.lins l = some G) : SlotsSame F G :=
  linsLoop_slots l F G h

/-- Adding a list of claims leads to a later state. -/
theorem lins_later {F G : Fork} {l : List Aff} (h : F.lins l = some G) : Later F G :=
  (lins_slots h).later

end OnBytes.PscRun

#print axioms OnBytes.PscRun.publicPart_value
#print axioms OnBytes.PscRun.value_public
#print axioms OnBytes.PscRun.value_later
#print axioms OnBytes.PscRun.lins_later
#print axioms OnBytes.PscRun.pscEnds_slot
#print axioms OnBytes.PscRun.pscRow_slot
