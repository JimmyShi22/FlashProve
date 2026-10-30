-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/WireOK.lean: lemmas on the parts of a wire record: `Enum.ofNum_ok`, `map_firstBlocks_unif`,
`WireE.one_ok`, `WireE.two_ok`.
-/
import Iop.WireOf
import Prob.Count
import Mathlib.Logic.Equiv.Fin.Basic

namespace Iop
open Prob

/-- The enumeration of a finite non-empty type by its number of elements is a bijection. -/
theorem Enum.ofNum_ok (β : Type) [Fintype β] [Nonempty β] (nb : β ≃ Fin (Fintype.card β)) :
    (Enum.ofNum β nb).OK := by
  have hc : 0 < Fintype.card β := Fintype.card_pos
  have hlt : ∀ r : Fin (Fintype.card β - 1 + 1), r.val < Fintype.card β := fun r => by
    have := r.isLt
    omega
  constructor
  · intro r r' h
    have h0 : nb.symm ⟨r.val % Fintype.card β, Nat.mod_lt _ hc⟩ =
        nb.symm ⟨r'.val % Fintype.card β, Nat.mod_lt _ hc⟩ := h
    have h2 : r.val % Fintype.card β = r'.val % Fintype.card β :=
      congrArg Fin.val (nb.symm.injective h0)
    rw [Nat.mod_eq_of_lt (hlt r), Nat.mod_eq_of_lt (hlt r')] at h2
    exact Fin.ext h2
  · intro b
    have hb := (nb b).isLt
    have hb' : (nb b).val < Fintype.card β - 1 + 1 := by omega
    refine ⟨⟨(nb b).val, hb'⟩, ?_⟩
    show nb.symm ⟨(nb b).val % Fintype.card β, Nat.mod_lt _ hc⟩ = b
    have he : (⟨(nb b).val % Fintype.card β, Nat.mod_lt _ hc⟩ : Fin (Fintype.card β)) = nb b :=
      Fin.ext (Nat.mod_eq_of_lt hb)
    rw [he, Equiv.symm_apply_apply]

/-- The first b of K uniform blocks of a non-empty type D are uniform, if b ≤ K. (The value dflt for
a missing block is never used.) -/
theorem map_firstBlocks_unif (D : Type) [Fintype D] [Nonempty D] (dflt : D) (b K : ℕ) (h : b ≤ K) :
    (unif (Fin K → D)).map
        (fun (u : Fin K → D) (i : Fin b) => if h' : i.val < K then u ⟨i.val, h'⟩ else dflt) =
      unif (Fin b → D) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← map_unif_equiv (Fin.appendEquiv b d : (Fin b → D) × (Fin d → D) ≃ (Fin (b + d) → D)),
    PMF.map_comp, ← map_fst_unif (C := Fin b → D) (D := Fin d → D)]
  congr 1
  funext p
  funext i
  have hi : i.val < b + d := lt_of_lt_of_le i.isLt (Nat.le_add_right b d)
  show (if h' : i.val < b + d then Fin.append p.1 p.2 ⟨i.val, h'⟩ else dflt) = p.1 i
  rw [dif_pos hi]
  exact Fin.append_left p.1 p.2 i

/-- One external string. -/
theorem WireE.one_ok (n : ℕ) (Sg : Type) (z : Sg) : (WireE.one n Sg z).OK where
  nodup := List.nodup_finRange n
  complete := List.mem_finRange
  build_rd := fun f p a h => by
    show (f p).getD z = a
    rw [h]
    rfl

/-- Two external strings. -/
theorem WireE.two_ok (n : ℕ) (Sg : Type) (z : Sg) : (WireE.two n Sg z).OK where
  nodup := by
    show ((List.finRange n).map Sum.inl ++
      (List.finRange n).map Sum.inr : List (Fin n ⊕ Fin n)).Nodup
    refine List.Nodup.append ((List.nodup_finRange n).map Sum.inl_injective)
      ((List.nodup_finRange n).map Sum.inr_injective) ?_
    intro p hl hr
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hr
    cases hb
  complete := fun p => by
    show p ∈ ((List.finRange n).map Sum.inl ++ (List.finRange n).map Sum.inr : List (Fin n ⊕ Fin n))
    cases p with
    | inl q => exact List.mem_append_left _ (List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩)
    | inr q => exact List.mem_append_right _ (List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩)
  build_rd := fun f p a h => by
    cases p with
    | inl q =>
        show (f (.inl q)).getD z = a
        rw [h]
        rfl
    | inr q =>
        show (f (.inr q)).getD z = a
        rw [h]
        rfl

end Iop
