-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Ledger.lean: THE LEDGER OF HIDDEN SCALARS (bridges B2 and B3 for Lemma 2b).
`hideRun_frame`: in a ledger that has a place for each of its numbers, a run of layings writes what
was shown and the factor under its own numbers and leaves every other number as it was.
`rd_atHidden`: HeadLaw.lean's `atHidden F mask f`, read in the field, is the value of the form
(`Aff.value`) in the world in which a slot holds its hidden scalar and every entry holds 0.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Sum2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Aff Fork Reading World)

theorem getD_set! {α : Type} (a : Array α) (j i : Nat) (x z : α) (hj : j < a.size) :
    (a.set! j x).getD i z = if i = j then x else a.getD i z := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; simp [hj]
  · have h' : ¬ j = i := fun e => h e.symm
    simp [h, h']

/-- One laying. -/
theorem hide_frame {F G : Fork} {j : Nat} {x f : E} (hW : WellLaid F)
    (h : F.hide j x f = some G) :
    WellLaid G ∧ G.ns = F.ns ∧ G.next = F.next ∧
      (∀ i z, G.vp.getD i z = if i = j then x else F.vp.getD i z) ∧
      (∀ i z, G.mf.getD i z = if i = j then f else F.mf.getD i z) := by
  unfold Fork.hide at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hj : j < F.ns := hc.1.1
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨w1, w2, w3⟩ := hW
    refine ⟨⟨?_, ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
    · simp [w1]
    · simp [w2]
    · simp [w3]
    · intro i z; exact getD_set! _ _ _ _ _ (by rw [w2]; exact hj)
    · intro i z; exact getD_set! _ _ _ _ _ (by rw [w3]; exact hj)
  · cases h

/-- A run of layings, as a fold over a list. -/
theorem hideSteps_frame (f : E) : ∀ (l : List E) (j : Nat) (F : Fork) (r : Nat × Fork),
    WellLaid F → l.foldlM (Fork.hideStep f) (j, F) = some r →
    WellLaid r.2 ∧ r.2.ns = F.ns ∧ r.2.next = F.next ∧
      (∀ i z, r.2.vp.getD i z =
        if j ≤ i ∧ i < j + l.length then l.getD (i - j) z else F.vp.getD i z) ∧
      (∀ i z, r.2.mf.getD i z = if j ≤ i ∧ i < j + l.length then f else F.mf.getD i z)
  | [], j, F, r, hW, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    refine ⟨hW, rfl, rfl, ?_, ?_⟩ <;> intro i z <;> rw [if_neg] <;> simp only [List.length_nil] <;> omega
  | x :: xs, j, F, r, hW, h => by
    rw [List.foldlM_cons] at h
    cases hs : F.hide j x f with
    | none =>
      simp [Fork.hideStep, hs] at h
    | some H =>
      have hstep : Fork.hideStep f (j, F) x = some (j + 1, H) := by simp [Fork.hideStep, hs]
      rw [hstep] at h
      obtain ⟨a1, a2, an, a3, a4⟩ := hide_frame hW hs
      obtain ⟨b1, b2, bn, b3, b4⟩ := hideSteps_frame f xs (j + 1) H r a1 h
      refine ⟨b1, by rw [b2, a2], by rw [bn, an], ?_, ?_⟩
      · intro i z
        rw [b3, a3]
        simp only [List.length_cons]
        by_cases h1 : i = j
        · subst h1
          rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
          simp
        · by_cases h2 : j + 1 ≤ i ∧ i < j + 1 + xs.length
          · rw [if_pos h2, if_pos (by omega)]
            have : i - j = (i - (j + 1)) + 1 := by omega
            rw [this, List.getD_cons_succ]
          · rw [if_neg h2, if_neg h1, if_neg (by omega)]
      · intro i z
        rw [b4, a4]
        simp only [List.length_cons]
        by_cases h1 : i = j
        · subst h1
          rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
        · by_cases h2 : j + 1 ≤ i ∧ i < j + 1 + xs.length
          · rw [if_pos h2, if_pos (by omega)]
          · rw [if_neg h2, if_neg h1, if_neg (by omega)]

/-- **A run of layings.** -/
theorem hideRun_frame {F G : Fork} {first : Nat} {v : Array E} {f : E} (hW : WellLaid F)
    (h : F.hideRun first v f = some G) :
    WellLaid G ∧ G.ns = F.ns ∧ G.next = F.next ∧
      (∀ i z, G.vp.getD i z =
        if first ≤ i ∧ i < first + v.size then v.toList.getD (i - first) z else F.vp.getD i z) ∧
      (∀ i z, G.mf.getD i z = if first ≤ i ∧ i < first + v.size then f else F.mf.getD i z) := by
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  cases hr : v.toList.foldlM (Fork.hideStep f) (first, F) with
  | none => rw [hr] at h; cases h
  | some r =>
    rw [hr] at h
    simp only [Option.some.injEq] at h
    subst h
    have := hideSteps_frame f v.toList first F r hW hr
    rwa [Array.length_toList] at this

/-! ## B3 -/

/-- The world of a ledger and mask entries: a slot holds its hidden scalar; an entry holds 0. -/
def worldOf (F : Fork) (mask : Nat → E) : World K := ⟨fun j => rd (hidden F mask j), fun _ _ _ => 0⟩

theorem rd_atHidden (F : Fork) (mask : Nat → E) (f : Form) :
    rd (atHidden F mask f) = Aff.value Reading.gl (worldOf F mask) f := by
  have he : (f.ents.toList.map (OnBytes.Model.Ent.value Reading.gl (worldOf F mask))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    simp [OnBytes.Model.Ent.value, worldOf]
  have gen : ∀ (l : List (Nat × E)) (s : E),
      rd (l.foldl (fun s x => s + x.2 * hidden F mask x.1) s)
        = (l.map (OnBytes.Model.slotValue Reading.gl (worldOf F mask))).sum + rd s := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons x xs ih =>
      intro s
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, rd_add, rd_mul]
      simp only [OnBytes.Model.slotValue, worldOf]
      show _ + (rd s + rd x.2 * rd (hidden F mask x.1)) = rd x.2 * rd (hidden F mask x.1) + _ + rd s
      ring
  unfold atHidden Aff.value
  rw [← Array.foldl_toList, gen, he, zero_add]
  rfl

end VerifiableInference.Desc.Kinds.Head.Law
