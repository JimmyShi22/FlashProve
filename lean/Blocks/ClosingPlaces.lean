-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ClosingPlaces.lean: which entries of the pad vector are the pads of a closing.

The pad vector has n entries (Blocks/Allot.lean). A closing (Blocks/ClosingBlock.lean) with nR REL
and nO opened forms takes the 2 nR + nO entries from index b on (indices modulo n: `allot`,
Blocks/Allot.lean):
  `Closing.placesAt hn b`: the pads of ϑ0 and ϑ1 of REL number r at b + 2 r and b + 2 r + 1; the pad
  of the opened form number o at b + 2 nR + o;
  `aux_injective`, `opn_injective`, `opn_aux_disjoint`: every entry is used once, if b + (2 nR + nO)
  ≤ n;
  `range_placesAt_sub`: all these entries are in the region from b to b + (2 nR + nO).
-/
import Blocks.Allot
import Blocks.ClosingBlock

set_option autoImplicit false

namespace Blocks.Closing

variable {n : ℕ} (hn : 0 < n) (b : ℕ) (nR nO : ℕ)

/-- The pads of a closing: the pad vector's entries from index b on. -/
def placesAt : Places (Fin n) (Fin nR) nO where
  aux := fun k => allot hn (b + 2 * k.1.val + if k.2 then 1 else 0)
  opn := fun o => allot hn (b + 2 * nR + o.val)

variable {b nR nO}

theorem aux_injective (hfit : b + (2 * nR + nO) ≤ n) :
    Function.Injective (placesAt hn b nR nO).aux := by
  rintro ⟨r, β⟩ ⟨r', β'⟩ h
  have h1 := r.2
  have h2 := r'.2
  have h3 : b + 2 * r.val + (if β then 1 else 0) = b + 2 * r'.val + (if β' then 1 else 0) :=
    allot_inj hn (by split_ifs <;> omega) (by split_ifs <;> omega) h
  have h4 : r = r' := Fin.ext (by split_ifs at h3 <;> omega)
  subst h4
  cases β <;> cases β' <;> simp at h3 ⊢

theorem opn_injective (hfit : b + (2 * nR + nO) ≤ n) :
    Function.Injective (placesAt hn b nR nO).opn := by
  intro o o' h
  have h1 := o.2
  have h2 := o'.2
  have h3 : b + 2 * nR + o.val = b + 2 * nR + o'.val := allot_inj hn (by omega) (by omega) h
  exact Fin.ext (by omega)

theorem opn_aux_disjoint (hfit : b + (2 * nR + nO) ≤ n) :
    Disjoint (Set.range (placesAt hn b nR nO).opn) (Set.range (placesAt hn b nR nO).aux) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨o, rfl⟩ ⟨⟨r, β⟩, h⟩
  have h1 := o.2
  have h2 := r.2
  have h3 : b + 2 * r.val + (if β then 1 else 0) = b + 2 * nR + o.val :=
    allot_inj hn (by split_ifs <;> omega) (by omega) h
  split_ifs at h3 <;> omega

theorem range_placesAt_sub :
    Set.range (placesAt hn b nR nO).aux ∪ Set.range (placesAt hn b nR nO).opn ⊆
      region hn b (b + (2 * nR + nO)) := by
  rintro q (⟨⟨r, β⟩, rfl⟩ | ⟨o, rfl⟩)
  · have h2 := r.2
    exact mem_region hn (by omega) (by split_ifs <;> omega)
  · have h1 := o.2
    exact mem_region hn (by omega) (by omega)

end Blocks.Closing
