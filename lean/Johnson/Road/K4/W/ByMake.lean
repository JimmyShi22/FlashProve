-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/ByMake.lean: CONDITIONAL.

Not shown here. EACH OF THE THREE LAWS ON CLAIMS HAS A PREMISE THAT SAYS THAT A SLOT HOLDS THE WORTH
OF THE VERY FORM THAT IS TAKEN FROM IT: so each of them restates its premise, and the third does no
more besides than open its list. THE PREMISES ARE ASKED IN THE WORLD's OWN ENTRIES: whoever lays a
slot as a form's value on reads of its own owes that these reads are the world's entries. That a
world with such slots is the one that an honest run leaves is not shown. No example is known.
Nothing is said in the library's terms.

THREE GROUPS OF CLAIMS OF THE SUB-PROTOCOL K4 THAT ARE WORTH 0 WHERE EACH SLOT HOLDS THE VALUE OF
ITS OWN FORM: the two claims on the sides of the batched sumcheck's end, and the claims on the
values that the second token sumcheck shows (OnBytes/Desc/First/K4/Claims.lean). At a free reading
and a free world.

  mem_of_mapM    every member of a returned list comes from a member of the list that was mapped.
  sideA_zero, sideB_zero   the fields sideA, sideB of BackWorth (Johnson/Road/K4/WorthGroups.lean).
  terms_zero'    the field terms of FrontWorth.

No property is claimed.
-/
import Johnson.Road.K4.WorthGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Heard Own)
open OnBytes.Desc.First.K4 (termsForms)

variable {K : Type} [CommRing K] {ρ : Reading K} {W : World K}

/-- Every member of a returned list comes from a member of the list that was mapped. -/
theorem mem_of_mapM {α β : Type} {f : α → Option β} : ∀ {l : List α} {r : List β},
    l.mapM f = some r → ∀ b ∈ r, ∃ a ∈ l, f a = some b
  | [], r, h, b, hb => by
    rw [List.mapM_nil] at h
    obtain rfl := Option.some.inj h
    cases hb
  | a :: l, r, h, b, hb => by
    rw [List.mapM_cons] at h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., hx⟩
    · obtain ⟨a', ha', e⟩ := mem_of_mapM hxs b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', e⟩

/-- **The claim on the A side's end value**: the slot holds the worth of the form. -/
theorem sideA_zero {o : Own} (hA : W.slot o.K.sA0 = o.K.fin.Alin.value ρ W) :
    (Aff.slot o.K.sA0 - o.K.fin.Alin).value ρ W = 0 := by
  rw [Aff.value_sub, Aff.value_slot, hA, sub_self]

/-- **The claim on the B side's end value.** -/
theorem sideB_zero {o : Own} (hB : W.slot o.K.sB0 = o.K.fin.Blin.value ρ W) :
    (Aff.slot o.K.sB0 - o.K.fin.Blin).value ρ W = 0 := by
  rw [Aff.value_sub, Aff.value_slot, hB, sub_self]

/-- **The claims on the values that the second token sumcheck shows**: each slot holds the worth of
its form in the reads at the sumcheck's end point. tT: that sumcheck as it was heard. -/
theorem terms_zero' {v : Env} {H : Heard} {tT : Tsc} (hT : H.tT = some tT)
    (hR : ∀ i, i < v.y.NN * v.y.Lam → ∀ x, v.rowR "rt" i = some x →
      W.slot (tT.sEnd + i) = x.value ρ W)
    (hS : ∀ lm, lm < v.y.LamM → ∀ x, v.shA "sc" "rt" lm 0 = some x →
      W.slot (tT.sEnd + v.y.NN * v.y.Lam + lm) = x.value ρ W)
    (hE : ∀ k, k < v.y.LamM * v.y.h.NE → ∀ z,
      v.shA "sel" "rt" (k / v.y.h.NE) (k % v.y.h.NE) = some z →
      W.slot (tT.sEnd + v.y.NN * v.y.Lam + v.y.LamM + k) = z.value ρ W) :
    ∀ l, termsForms v H = some l → ∀ f ∈ l, f.value ρ W = 0 := by
  intro l h f hf
  unfold termsForms at h
  obtain ⟨tT', a0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : tT = tT' := Option.some.inj (hT.symm.trans a0)
  obtain ⟨a, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : a ++ b ++ c = l := Option.some.inj h
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨i, hi, e⟩ := mem_of_mapM a1 f hf
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp e
      rw [Aff.value_sub, Aff.value_slot, hR i (List.mem_range.mp hi) x hx, sub_self]
    · obtain ⟨i, hi, e⟩ := mem_of_mapM a2 f hf
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp e
      rw [Aff.value_sub, Aff.value_slot, hS i (List.mem_range.mp hi) x hx, sub_self]
  · obtain ⟨i, hi, e⟩ := mem_of_mapM a3 f hf
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp e
    rw [Aff.value_sub, Aff.value_slot, hE i (List.mem_range.mp hi) x hx, sub_self]

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.mem_of_mapM
#print axioms OnBytes.Road.K4.W.sideA_zero
#print axioms OnBytes.Road.K4.W.sideB_zero
#print axioms OnBytes.Road.K4.W.terms_zero'
