-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieKit.lean.
Small facts for the tie of a sub-proof's lookup.

States:
  slot_formIs: the hidden value under a filled slot, as a form: its public part is what was shown,
  and it has, on the mask row, the factor times the slot's mask entry.
  zero_formIs: the constant form 0.
  same_took: two states that differ in what lies under the slots alone, with more slots taken.
  shown_val: what Fork.shown returns.
  publicPart_value: the public part of a form is its value in the world in which every mask entry
    and every entry of a virtual row is 0. formIs_value: so a form is compared by its values alone.
  evalL_zero, evalL_flatMap: the value of a sparse form at the mask row 0; of a row of forms.
  tgEnd, tieGo_snoc: the flat function's steps of the tie, with the last step taken off.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoForm
import OnBytes.Tie.Pv.Lookup.Forest.FoTieIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

theorem same_took {A B : Fork} (h : Same A B) (m : ℕ) : Same (took A m) (took B m) := by
  unfold Same at *
  rw [h]
  rfl

theorem shown_val {F : Fork} {j : ℕ} {x : E} (h : F.shown j = some x) :
    j < F.ns ∧ Filled F j ∧ x = F.vp.getD j zeroE := by
  unfold Fork.shown at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The hidden value under a filled slot. -/
theorem slot_formIs {F : Fork} {j : ℕ} (hf : Filled F j) :
    FormIs ρ F (Aff.slot j) (ρ.val (F.vp.getD j zeroE))
      [(.mask j, ρ.val (F.mf.getD j zeroE))] := by
  intro G hG
  obtain ⟨_, k2, k3⟩ := hG.keep j hf
  constructor
  · intro x hx
    have e : G.publicPart (Aff.slot j) =
        (G.shown j).map fun y => addE zeroE (mulE oneE y) := by
      unfold Fork.publicPart Aff.slot
      simp
    rw [e] at hx
    cases hs : G.shown j with
    | none => rw [hs] at hx; exact absurd hx (by simp)
    | some y =>
      rw [hs] at hx
      obtain rfl : addE zeroE (mulE oneE y) = x := Option.some.inj hx
      rw [ρ.add, ρ.mul, ρ.zero, ρ.one, (shown_val hs).2.2, k2]
      ring
  · intro mask entry
    rw [Aff.value_slot]
    show ρ.val (G.vp.getD j zeroE) - ρ.val (G.mf.getD j zeroE) * mask j = _
    rw [k2, k3]
    simp [evalL, muOf]

/-- The constant form 0. -/
theorem zero_formIs (F : Fork) : FormIs ρ F (Aff.ofConst zeroE) 0 [] := by
  intro G _
  constructor
  · intro x hx
    have e : G.publicPart (Aff.ofConst zeroE) = some zeroE := by
      unfold Fork.publicPart Aff.ofConst
      simp
    rw [e] at hx
    rw [← Option.some.inj hx, ρ.zero]
  · intro mask entry
    rw [Aff.value_ofConst, ρ.zero]
    simp [evalL]

/-- The public part of a form is its value in the world in which every mask entry and every entry
of a virtual row is 0. -/
theorem publicPart_value (F : Fork) (a : Aff) (x : E) (h : F.publicPart a = some x) :
    ρ.val x = a.value ρ (F.worldOf ρ (fun _ => 0) fun _ _ _ => 0) := by
  unfold Fork.publicPart at h
  rw [← Array.foldlM_toList] at h
  have key := foldlM_adds (K := K)
    (fun (v : E) (y : ℕ × E) => (F.shown y.1).map fun z => addE v (mulE y.2 z)) (fun _ => True)
    ρ.val (slotValue ρ (F.worldOf ρ (fun _ => 0) fun _ _ _ => 0)) (by
      intro s y s' _ hs
      beta_reduce at hs
      refine ⟨trivial, ?_⟩
      cases hz : F.shown y.1 with
      | none => rw [hz] at hs; exact absurd hs (by simp)
      | some z =>
        rw [hz] at hs
        obtain rfl : addE s (mulE y.2 z) = s' := Option.some.inj hs
        rw [ρ.add, ρ.mul, (shown_val hz).2.2]
        show _ = _ + ρ.val y.2 * (ρ.val (F.vp.getD y.1 zeroE) - ρ.val (F.mf.getD y.1 zeroE) * 0)
        ring) a.slots.toList a.const x trivial h
  unfold Aff.value
  have hz : (a.ents.toList.map (Ent.value ρ (F.worldOf ρ (fun _ => 0) fun _ _ _ => 0))).sum = 0 :=
      by
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hy
    show ρ.val e.coef * 0 = 0
    ring
  rw [hz, key.2]
  ring

theorem evalL_zero (cf : List (Pl × K)) : evalL (muOf fun _ => (0 : K)) cf = 0 := by
  unfold evalL
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨pc, _, rfl⟩ := List.mem_map.mp hy
  have : muOf (fun _ => (0 : K)) pc.1 = 0 := by cases pc.1 <;> rfl
  rw [this, mul_zero]

/-- A form is compared by its values alone. -/
theorem formIs_value {F : Fork} {C : Aff} {tg : K} {inc : List (Pl × K)}
    (h : ∀ G, Later F G → ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
      C.value ρ (G.worldOf ρ mask entry) = tg - evalL (muOf mask) inc) : FormIs ρ F C tg inc :=
  fun G hG => ⟨fun x hx => by
    rw [publicPart_value ρ G C x hx, h G hG, evalL_zero, sub_zero], h G hG⟩

theorem evalL_flatMap {P : Type} (μ : P → K) (f : ℕ → List (P × K)) : ∀ l : List ℕ,
    evalL μ (l.flatMap f) = (l.map fun i => evalL μ (f i)).sum
  | [] => rfl
  | i :: l => by
    rw [List.flatMap_cons, evalL_append, evalL_flatMap μ f l, List.map_cons, List.sum_cons]

end

section
variable {K : Type} [CommRing K]

/-- The target with which the next step is entered, behind the steps scs played from step l on: tg
if there is none, else the value that the last of them shows at nxAt of its number. -/
def tgEnd (l : ℕ) (tg : K) (scs : List (Sc K)) : K :=
  match scs.getLast? with
  | none => tg
  | some s => s.v (nxAt (l + scs.length - 1))

theorem tieGo_len : ∀ (c l : ℕ) (tg : K) (rs : Rounds K), (tieGo c l tg rs).1.length = c
  | 0, _, _, _ => rfl
  | c + 1, l, tg, rs => by
    show ((takeSc rs tg [0] true).1 :: (tieGo c (l + 1) _ _).1).length = c + 1
    rw [List.length_cons, tieGo_len c]

/-- The last step taken off. -/
theorem tieGo_snoc : ∀ (c l : ℕ) (tg : K) (rs : Rounds K),
    tieGo (c + 1) l tg rs =
      ((tieGo c l tg rs).1 ++
          [(takeSc (tieGo c l tg rs).2 (tgEnd l tg (tieGo c l tg rs).1) [0] true).1],
        (takeSc (tieGo c l tg rs).2 (tgEnd l tg (tieGo c l tg rs).1) [0] true).2)
  | 0, _, _, _ => rfl
  | c + 1, l, tg, rs => by
    have ih := tieGo_snoc c (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0] true).2
    show ((takeSc rs tg [0] true).1 :: (tieGo (c + 1) (l + 1) _ _).1, (tieGo (c + 1) (l + 1) _ _).2)
        = _
    rw [ih]
    have hlen := tieGo_len c (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0]
        true).2
    have e : tgEnd l tg (tieGo (c + 1) l tg rs).1 =
        tgEnd (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l))
          (tieGo c (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0] true).2).1 := by
      show tgEnd l tg ((takeSc rs tg [0] true).1 :: (tieGo c (l + 1) _ _).1) = _
      generalize (tieGo c (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l))
        (takeSc rs tg [0] true).2).1 = q at hlen ⊢
      unfold tgEnd
      cases q with
      | nil => simp
      | cons b q =>
        rw [List.getLast?_cons_cons]
        cases hq : (b :: q).getLast? with
        | none => simp at hq
        | some s =>
          show s.v (nxAt (l + (q.length + 1 + 1) - 1)) = s.v (nxAt (l + 1 + (q.length + 1) - 1))
          congr 2
          omega
    rw [e]
    rfl

end
end Fo
