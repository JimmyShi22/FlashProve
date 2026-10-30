-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieSide.lean: THE SIDE
CLAUSES OF THE TABLE'S THREE SENTENCES, OFF THE LAYER'S OWN YES: the sentences on what the
kind's own block leaves (Zero, WorthPlanes, WorthKeys: Johnson/Desc/Key/KeyK3W.lean,
KeyK3Items.lean) ask of every form that it names no entry of a virtual row and that each of its
slots lies below the homes' size. Where the layer has made a row, or a claim on keys, of a form,
both hold: maskSide (Johnson/Desc/First/Look/K3Key.lean) refuses otherwise.

Main names:
  Side homeA a: the two clauses of a form a.
  maskSide_side: maskSide's yes ⊢ Side.
  mapM_all: what is made member by member was made of every member.
  group_side: groupRows' yes ⊢ Side of every object and of every plane claim's lead; three claims.
  keys_side: keyClaims' yes ⊢ Side of every part's form.

Object: maskSide, groupRows, keyClaims.
User: none yet.
Letters: F, a ledger · homeA, a table of homes.

Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Look.KeyLaw.GroupSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieSide
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw

/-- The two side clauses of a form. -/
def Side (homeA : Array Slot) (a : Aff) : Prop :=
  a.ents.isEmpty = true ∧ ∀ t ∈ a.slots, t.1 < homeA.size

theorem maskLoop_side (F : Fork) (homeA : Array Slot) : ∀ (l : List (ℕ × E)) (x y : MaskForm × E),
    l.foldlM (fun (x : MaskForm × E) (t : ℕ × E) =>
      match homeA[t.1]?, F.shown t.1 with
      | some s, some v => some (x.1 ++ [(s, mulE t.2 (F.mf.getD t.1 zeroE))], addE x.2 (mulE t.2 v))
      | _, _ => none) x = some y → ∀ t ∈ l, t.1 < homeA.size
  | [], _, _, _ => fun t ht => by cases ht
  | t :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    cases h1 : homeA[t.1]? with
    | none => rw [h1] at h; cases h
    | some s =>
      cases h2 : F.shown t.1 with
      | none => rw [h1, h2] at h; cases h
      | some v =>
        rw [h1, h2] at h
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact (Array.getElem?_eq_some_iff.1 h1).1
        · exact maskLoop_side F homeA l _ y h z hz

/-- **maskSide's yes gives the two side clauses.** -/
theorem maskSide_side {F : Fork} {homeA : Array Slot} {a : Aff} {y : MaskForm × E}
    (h : maskSide F homeA a = some y) : Side homeA a := by
  unfold maskSide at h
  split at h
  · cases h
  · rename_i he
    rw [← Array.foldlM_toList] at h
    refine ⟨by simpa using he, fun t ht => ?_⟩
    exact maskLoop_side F homeA _ _ y h t (Array.mem_toList_iff.2 ht)

/-- What is made member by member was made of every member. -/
theorem mapM_all {α β : Type} (f : α → Option β) : ∀ (os : List α) (fr : List β),
    os.mapM f = some fr → ∀ a ∈ os, ∃ R, f a = some R
  | [], _, _, a, ha => by cases ha
  | b :: os, fr, h, a, ha => by
    rw [List.mapM_cons] at h
    cases hb : f b with
    | none => simp [hb] at h
    | some Rb =>
      cases hos : os.mapM f with
      | none => simp [hb, hos] at h
      | some fr' =>
        rcases List.mem_cons.1 ha with rfl | ha'
        · exact ⟨Rb, hb⟩
        · exact mapM_all f os fr' hos a ha'

theorem aff_side {F : Fork} {homeA : Array Slot} {a : Aff} {R : GRow}
    (h : rowOfAff F homeA a = some R) : Side homeA a := by
  unfold rowOfAff at h
  obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 h
  exact maskSide_side hy

theorem plane_side {pa : GRow → Tensor → GRow} {F : Fork} {homeA : Array Slot} {t : Bool}
    {c : PlaneClaim} {R : GRow} (h : rowOfPlane pa F homeA t c = some R) : Side homeA c.lead := by
  unfold rowOfPlane at h
  obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 h
  exact maskSide_side hy

/-- **groupRows' yes gives the side clauses of all its forms, and three claims on the planes.** -/
theorem group_side {pa : GRow → Tensor → GRow} {F : Fork} {homeA : Array Slot}
    {objects : List Aff} {planes : List PlaneClaim} {rows : List GRow}
    (h : groupRows pa F homeA objects planes = some rows) :
    (∀ a ∈ objects, Side homeA a) ∧ (∀ c ∈ planes, Side homeA c.lead) ∧ planes.length = 3 := by
  unfold groupRows at h
  match planes, hg : objects.getLast?, h with
  | [leaves, value, counts], some bits, h =>
    simp only at h
    cases h0 : objects.dropLast.mapM (rowOfAff F homeA) with
    | none => simp [h0] at h
    | some front =>
      cases h1 : rowOfPlane pa F homeA true leaves with
      | none => simp [h0, h1] at h
      | some r1 =>
        cases h2 : rowOfAff F homeA bits with
        | none => simp [h0, h1, h2] at h
        | some r2 =>
          cases h3 : rowOfPlane pa F homeA false value with
          | none => simp [h0, h1, h2, h3] at h
          | some r3 =>
            cases h4 : rowOfPlane pa F homeA true counts with
            | none => simp [h0, h1, h2, h3, h4] at h
            | some r4 =>
              refine ⟨fun a ha => ?_, fun c hc => ?_, rfl⟩
              · have hne : objects ≠ [] := by
                  rintro rfl
                  cases hg
                have e := List.dropLast_append_getLast hne
                have el : objects.getLast hne = bits := by
                  rw [List.getLast?_eq_getLast hne] at hg
                  exact Option.some.inj hg
                rw [← e, el] at ha
                rcases List.mem_append.1 ha with h5 | h5
                · obtain ⟨R, hR⟩ := mapM_all _ _ _ h0 a h5
                  exact aff_side hR
                · obtain rfl := List.mem_singleton.1 h5
                  exact aff_side h2
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                rcases hc with rfl | rfl | rfl
                · exact plane_side h1
                · exact plane_side h3
                · exact plane_side h4

/-- **keyClaims' yes gives the side clauses of every part's form.** -/
theorem keys_side {S : Lkp.Public} {F : Fork} {homeA : Array Slot} {g : HeardG}
    {keys : List Lkp.Keys} (h : keyClaims S F homeA g = some keys) :
    ∀ x ∈ g.keys.zipIdx, Side homeA x.1.2 := by
  intro x hx
  unfold keyClaims at h
  obtain ⟨R, hR⟩ := mapM_all _ _ _ h x hx
  obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hR
  exact maskSide_side hy

end Johnson.RunOne.Law.TieSide

#print axioms Johnson.RunOne.Law.TieSide.maskLoop_side
#print axioms Johnson.RunOne.Law.TieSide.maskSide_side
#print axioms Johnson.RunOne.Law.TieSide.mapM_all
#print axioms Johnson.RunOne.Law.TieSide.aff_side
#print axioms Johnson.RunOne.Law.TieSide.plane_side
#print axioms Johnson.RunOne.Law.TieSide.group_side
#print axioms Johnson.RunOne.Law.TieSide.keys_side
