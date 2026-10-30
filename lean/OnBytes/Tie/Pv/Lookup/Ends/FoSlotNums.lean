-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoSlotNums.lean: the places of a lookup's mask entries lie below the
number of these entries.

FoLedger.ledger_lt (OnBytes/Tie/Pv/Lookup/Forest/FoLedger.lean) says so of a name (sumcheck, entry)
in the list of all names. Here it is said of the five functions by which the lookup's two
descriptions address the places (TwNums.Sizes.pTie, pKey, pTab, pEnd, pBit,
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean), for every S, with no hypothesis on S.

 - Has c e: the sumcheck c has the entry e: a coefficient inside the round's degree, the constant,
   or a shown value below the number shown. mem_of_has: then e is in entsOf c. has_clamp: a clamped
   entry is one.
 - place_lt: for i below the number of the sumchecks: the place of an entry that sumcheck number i
   has is below S.nMasks.
 - pTie_lt, pKey_lt, pTab_lt, pEnd_lt, pBit_lt: the five functions at an entry that the sumcheck
   has, at every step and level (a step or level that is not played goes to place 0).
 - pTieC_lt, pKeyC_lt, pTabC_lt, pEndC_lt, pBitC_lt: the clamped functions at every step, level and
   entry.

Limits: at an entry that the sumcheck has not, the five bare functions may run beyond S.nMasks;
nothing is said there. Numbers alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoWalk
import OnBytes.Tie.Pv.Lookup.Value.TwO65

set_option autoImplicit false

namespace Fo.Slots
open TwNums TwNums.Sizes FoLedger Cb.Fo.Walk

/-- The sumcheck c has the entry e. -/
def Has (c : Sc) : Ent → Prop
  | .coef j t => t < c.degs.getD j 0
  | .const => True
  | .shown a => a < c.shown

theorem mem_of_has {c : Sc} : ∀ {e : Ent}, Has c e → e ∈ entsOf c
  | .coef j t, h => by
    have h' : t < c.degs.getD j 0 := h
    have hj : j < c.degs.length := by
      by_contra hn
      rw [List.getD_eq_default _ _ (by omega)] at h'
      omega
    unfold entsOf
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2
      ⟨j, List.mem_range.2 hj, List.mem_map.2 ⟨t, List.mem_range.2 h', rfl⟩⟩))
  | .const, _ => by
    unfold entsOf
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
  | .shown a, h => by
    unfold entsOf
    exact List.mem_append_right _ (List.mem_map.2 ⟨a, List.mem_range.2 h, rfl⟩)

/-- A clamped entry is an entry of the sumcheck. -/
theorem has_clamp (c : Sc) : ∀ e : Ent, Has c (Ent.clamp c e)
  | .coef j t => by
    show Has c (if t < c.degs.getD j 0 then .coef j t else .const)
    by_cases h : t < c.degs.getD j 0
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      trivial
  | .const => trivial
  | .shown a => by
    show Has c (if c.shown = 0 then .const else .shown (min a (c.shown - 1)))
    by_cases h : c.shown = 0
    · rw [if_pos h]
      trivial
    · rw [if_neg h]
      show min a (c.shown - 1) < c.shown
      omega

variable (S : Sizes)

/-- The place of an entry that sumcheck number i has lies below the number of mask entries. -/
theorem place_lt {i : ℕ} (hi : i < S.scs.length) {e : Ent}
    (he : Has (S.scs.getD i ⟨[], false, 0⟩) e) : S.place i e < S.nMasks :=
  ledger_lt S (i, e) (List.mem_flatMap.2
    ⟨i, List.mem_range.2 hi, List.mem_map.2 ⟨e, mem_of_has he, rfl⟩⟩)

theorem pTie_lt (j : ℕ) {e : Ent} (he : Has (S.scTie j) e) : S.pTie j e < S.nMasks := by
  unfold Sizes.pTie
  split
  · rename_i hj
    refine place_lt S (by rw [scs_length]; unfold Sizes.iTie; omega) ?_
    rw [scs_tie S j hj]
    exact he
  · exact Cb.Tw.nMasks_pos S

theorem pKey_lt (l : ℕ) {e : Ent} (he : Has (S.scKey l) e) : S.pKey l e < S.nMasks := by
  unfold Sizes.pKey
  split
  · rename_i hl
    refine place_lt S (by rw [scs_length]; unfold Sizes.iKey; omega) ?_
    rw [scs_key S l hl]
    exact he
  · exact Cb.Tw.nMasks_pos S

theorem pTab_lt (l : ℕ) {e : Ent} (he : Has (S.scTab l) e) : S.pTab l e < S.nMasks := by
  unfold Sizes.pTab
  split
  · rename_i hl
    refine place_lt S (by rw [scs_length]; unfold Sizes.iTab; omega) ?_
    rw [scs_tab S l hl]
    exact he
  · exact Cb.Tw.nMasks_pos S

theorem pEnd_lt {e : Ent} (he : Has S.scEnd e) : S.pEnd e < S.nMasks := by
  unfold Sizes.pEnd
  refine place_lt S (by rw [scs_length]; unfold Sizes.iEnd; omega) ?_
  rw [scs_end S]
  exact he

theorem pBit_lt {e : Ent} (he : Has S.scBit e) : S.pBit e < S.nMasks := by
  unfold Sizes.pBit
  refine place_lt S (by rw [scs_length]; unfold Sizes.iBit; omega) ?_
  rw [scs_bit S]
  exact he

/-! ### the clamped places, at every step, level and entry -/

theorem pTieC_lt (j : ℕ) (e : Ent) : S.pTieC j e < S.nMasks := pTie_lt S j (has_clamp _ e)
theorem pKeyC_lt (l : ℕ) (e : Ent) : S.pKeyC l e < S.nMasks := pKey_lt S l (has_clamp _ e)
theorem pTabC_lt (l : ℕ) (e : Ent) : S.pTabC l e < S.nMasks := pTab_lt S l (has_clamp _ e)
theorem pEndC_lt (e : Ent) : S.pEndC e < S.nMasks := pEnd_lt S (has_clamp _ e)
theorem pBitC_lt (e : Ent) : S.pBitC e < S.nMasks := pBit_lt S (has_clamp _ e)

end Fo.Slots
