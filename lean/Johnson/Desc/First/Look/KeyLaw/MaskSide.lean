-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/MaskSide.lean: the readings mfOf and valOf of Statement.lean ARE what
K3Key's own maskSide computes, read in the field; and maskSide returns on every form that names no
entry of a virtual row and only slots that are filled and have a home.

Main names:
  HomeArr homeA home: the function home is the array homeA where the array has a member.
  maskSide_reads: what maskSide returns, read: the mask form is mfOf, the value valOf; the form
    names no entry of a virtual row, and its slots are filled.
  maskSide_some: when maskSide returns.
  maskSide_slots: every mask entry of what it returns is a member of the table of homes.
  mapM_reads, mapM_mem: two lemmas on lists under mapM.

Limits. Nothing on the rows that K3Key's groupRows makes of it, nor on keyClaims.

-/
import Johnson.Desc.First.Look.KeyLaw.Forward

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Filled)

/-- The function is the array, where the array has a member. -/
def HomeArr (homeA : Array Slot) (home : ℕ → Slot) : Prop := ∀ j s, homeA[j]? = some s → home j = s

theorem maskLoop_reads (F : Fork) (homeA : Array Slot) (home : ℕ → Slot) (hh : HomeArr homeA home) :
    ∀ (l : List (ℕ × E)) (x y : MaskForm × E),
    l.foldlM (fun (x : MaskForm × E) (t : ℕ × E) =>
      match homeA[t.1]?, F.shown t.1 with
      | some s, some v => some (x.1 ++ [(s, mulE t.2 (F.mf.getD t.1 zeroE))], addE x.2 (mulE t.2 v))
      | _, _ => none) x = some y →
    readForm y.1 = readForm x.1 ++
        l.map (fun t => (home t.1, readE t.2 * readE (F.mf.getD t.1 zeroE))) ∧
      readE y.2 = readE x.2 + (l.map fun t => readE t.2 * readE (F.vp.getD t.1 zeroE)).sum ∧
      ∀ t ∈ l, t.1 < F.ns ∧ Filled F t.1
  | [], x, y, h => by
    cases h
    exact ⟨by simp, by simp, fun t ht => (by cases ht)⟩
  | t :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    cases h1 : homeA[t.1]? with
    | none => rw [h1] at h; cases h
    | some s =>
      cases h2 : F.shown t.1 with
      | none => rw [h1, h2] at h; cases h
      | some v =>
        rw [h1, h2] at h
        obtain ⟨a1, a2, a3⟩ := maskLoop_reads F homeA home hh l _ y h
        obtain ⟨b1, b2, rfl⟩ := (PscRun.shown_iff F t.1 v).1 h2
        refine ⟨?_, ?_, fun z hz => ?_⟩
        · rw [a1, List.map_cons, hh _ _ h1]
          simp [readForm, readE_mul]
        · rw [a2, readE_add, readE_mul, List.map_cons, List.sum_cons]
          ring
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact ⟨b1, b2⟩
          · exact a3 z hz

/-- **What maskSide returns, read.** -/
theorem maskSide_reads {F : Fork} {homeA : Array Slot} {home : ℕ → Slot} (hh : HomeArr homeA home)
    {a : Aff} {y : MaskForm × E} (h : maskSide F homeA a = some y) :
    readForm y.1 = mfOf F home a ∧ readE y.2 = valOf F a ∧ NoEnt a ∧ AllShown F a := by
  unfold maskSide at h
  split at h
  · cases h
  · rename_i he
    rw [← Array.foldlM_toList] at h
    obtain ⟨a1, a2, a3⟩ := maskLoop_reads F homeA home hh _ _ y h
    refine ⟨a1, a2, ?_, a3⟩
    unfold NoEnt
    simpa using he

theorem maskLoop_some (F : Fork) (homeA : Array Slot) : ∀ (l : List (ℕ × E)) (x : MaskForm × E),
    (∀ t ∈ l, t.1 < F.ns ∧ Filled F t.1 ∧ t.1 < homeA.size) →
    ∃ y, l.foldlM (fun (x : MaskForm × E) (t : ℕ × E) =>
      match homeA[t.1]?, F.shown t.1 with
      | some s, some v => some (x.1 ++ [(s, mulE t.2 (F.mf.getD t.1 zeroE))], addE x.2 (mulE t.2 v))
      | _, _ => none) x = some y
  | [], x, _ => ⟨x, rfl⟩
  | t :: l, x, h => by
    obtain ⟨h1, h2, h3⟩ := h t List.mem_cons_self
    have e1 : homeA[t.1]? = some homeA[t.1] := Array.getElem?_eq_getElem h3
    have e2 : F.shown t.1 = some (F.vp.getD t.1 zeroE) := (PscRun.shown_iff F t.1 _).2 ⟨h1, h2, rfl⟩
    obtain ⟨y, hy⟩ := maskLoop_some F homeA l
      (x.1 ++ [(homeA[t.1], mulE t.2 (F.mf.getD t.1 zeroE))],
        addE x.2 (mulE t.2 (F.vp.getD t.1 zeroE))) fun z hz => h z (List.mem_cons_of_mem _ hz)
    refine ⟨y, ?_⟩
    rw [List.foldlM_cons, e1, e2]
    exact hy

/-- **When maskSide returns.** -/
theorem maskSide_some {F : Fork} {homeA : Array Slot} {a : Aff} (h1 : NoEnt a) (h2 : AllShown F a)
    (h3 : ∀ t ∈ a.slots.toList, t.1 < homeA.size) : ∃ y, maskSide F homeA a = some y := by
  unfold maskSide
  have he : a.ents.isEmpty = true := by
    unfold NoEnt at h1
    simpa using h1
  rw [he]
  rw [← Array.foldlM_toList]
  exact maskLoop_some F homeA _ _ fun t ht => ⟨(h2 t ht).1, (h2 t ht).2, h3 t ht⟩

/-! ## The mask entries that maskSide names are homes -/

theorem maskLoop_slots (F : Fork) (homeA : Array Slot) : ∀ (l : List (ℕ × E)) (x y : MaskForm × E),
    l.foldlM (fun (x : MaskForm × E) (t : ℕ × E) =>
      match homeA[t.1]?, F.shown t.1 with
      | some s, some v => some (x.1 ++ [(s, mulE t.2 (F.mf.getD t.1 zeroE))], addE x.2 (mulE t.2 v))
      | _, _ => none) x = some y →
    (∀ p ∈ x.1, p.1 ∈ homeA.toList) → ∀ p ∈ y.1, p.1 ∈ homeA.toList
  | [], x, y, h, hx => by
    cases h
    exact hx
  | t :: l, x, y, h, hx => by
    rw [List.foldlM_cons] at h
    cases h1 : homeA[t.1]? with
    | none => rw [h1] at h; cases h
    | some s =>
      cases h2 : F.shown t.1 with
      | none => rw [h1, h2] at h; cases h
      | some v =>
        rw [h1, h2] at h
        refine maskLoop_slots F homeA l _ y h fun p hp => ?_
        rcases List.mem_append.1 hp with hp | hp
        · exact hx p hp
        · obtain rfl : p = (s, mulE t.2 (F.mf.getD t.1 zeroE)) := by simpa using hp
          exact Array.mem_toList_iff.2 (Array.mem_of_getElem? h1)

theorem maskSide_slots {F : Fork} {homeA : Array Slot} {a : Aff} {y : MaskForm × E}
    (h : maskSide F homeA a = some y) : ∀ p ∈ y.1, p.1 ∈ homeA.toList := by
  unfold maskSide at h
  split at h
  · cases h
  · rw [← Array.foldlM_toList] at h
    exact maskLoop_slots F homeA _ _ y h fun q hq => (by cases hq)

/-! ## Lists under mapM -/

/-- What mapM returns, mapped, where each member's image is known. -/
theorem mapM_reads {α β γ : Type} (f : α → Option β) (g : β → γ) (k : α → γ) : ∀ (l : List α)
    (r : List β), l.mapM f = some r → (∀ a ∈ l, ∀ b, f a = some b → g b = k a) →
    r.map g = l.map k
  | [], r, h, _ => by
    cases h
    rfl
  | a :: l, r, h, hk => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some b =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; cases h
      | some bs =>
        rw [ha, hl] at h
        cases h
        rw [List.map_cons, List.map_cons, hk a List.mem_cons_self b ha,
          mapM_reads f g k l bs hl fun x hx => hk x (List.mem_cons_of_mem _ hx)]

/-- Every member of what mapM returns comes from a member of the list. -/
theorem mapM_mem {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β), l.mapM f = some r →
    ∀ b ∈ r, ∃ a ∈ l, f a = some b
  | [], r, h, b, hb => by
    cases h
    cases hb
  | a :: l, r, h, b, hb => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some b0 =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; cases h
      | some bs =>
        rw [ha, hl] at h
        cases h
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨a', h1, h2⟩ := mapM_mem f l bs hl b hb
          exact ⟨a', List.mem_cons_of_mem _ h1, h2⟩

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.maskSide_reads
#print axioms VerifiableInference.Desc.K3.KeyLaw.maskSide_some
#print axioms VerifiableInference.Desc.K3.KeyLaw.maskSide_slots
