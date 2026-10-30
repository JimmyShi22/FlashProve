-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/GroupColSome.lean: a leaf's column of the right width is always cut.

The format cuts the words of an opened leaf of a group's tree into main symbols and mask symbols and
puts them on the group's rows (`groupCol` in Fmt/M2Types.lean). The cut refuses a list of words that
is too short or too long. This file proves that it refuses nothing else: a list with exactly
`widthOf` words (same file) is cut.

Main theorems.
 `takeParts_some`   the main symbols can be taken off a list that has their words and n more, and n
                    words are left.
 `takeE_exact`      n mask symbols can be taken off a list of 3 n words, and none is left.
 `cutParts_isSome`  both together.
 `groupCol_isSome`  the column of a group's tree.

Not claimed. Nothing on what the cut column holds.
-/
import Fmt.M3Dec

set_option autoImplicit false

namespace OnBytes.Slice

/-- The main symbols can be taken off a list of words that has their words and n more. Then n words
are left. A symbol over the larger field has three words, one over the base field has one. -/
theorem takeParts_some : ∀ (ds : List Bool) (w : List UInt64) (n : Nat),
    w.length = (ds.map fun e => if e then 3 else 1).sum + n →
    ∃ ms w', Fmt.M2.takeParts ds w = some (ms, w') ∧ w'.length = n
  | [], w, n, h => ⟨[], w, rfl, by simpa using h⟩
  | true :: ds, a :: b :: c :: w, n, h => by
    have hw : w.length = (ds.map fun e => if e then 3 else 1).sum + n := by
      simp only [List.length_cons, List.map_cons, List.sum_cons, if_true] at h
      omega
    obtain ⟨ms, w', e, hl⟩ := takeParts_some ds w n hw
    exact ⟨(a, b, c) :: ms, w', by rw [Fmt.M2.takeParts, e]; rfl, hl⟩
  | false :: ds, a :: w, n, h => by
    have hw : w.length = (ds.map fun e => if e then 3 else 1).sum + n := by
      simp only [List.length_cons, List.map_cons, List.sum_cons, Bool.false_eq_true, if_false] at h
      omega
    obtain ⟨ms, w', e, hl⟩ := takeParts_some ds w n hw
    exact ⟨Fmt.Fld.ofF a :: ms, w', by rw [Fmt.M2.takeParts, e]; rfl, hl⟩
  | true :: ds, [], n, h => by
    simp only [List.length_nil, List.map_cons, List.sum_cons, if_true] at h
    omega
  | true :: ds, [_], n, h => by
    simp only [List.length_cons, List.length_nil, List.map_cons, List.sum_cons, if_true] at h
    omega
  | true :: ds, [_, _], n, h => by
    simp only [List.length_cons, List.length_nil, List.map_cons, List.sum_cons, if_true] at h
    omega
  | false :: ds, [], n, h => by
    simp only [List.length_nil, List.map_cons, List.sum_cons, Bool.false_eq_true, if_false] at h
    omega

/-- n symbols over the larger field can be taken off a list of 3 n words, and no word is left. -/
theorem takeE_exact : ∀ (n : Nat) (w : List UInt64), w.length = 3 * n →
    ∃ zs, Fmt.M1.takeE n w = some (zs, [])
  | 0, w, h => by
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], by rw [hw]; rfl⟩
  | n + 1, a :: b :: c :: w, h => by
    have hw : w.length = 3 * n := by
      simp only [List.length_cons] at h
      omega
    obtain ⟨zs, e⟩ := takeE_exact n w hw
    exact ⟨(a, b, c) :: zs, by rw [Fmt.M1.takeE, e]; rfl⟩
  | n + 1, [], h => by
    simp only [List.length_nil] at h
    omega
  | n + 1, [_], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | n + 1, [_, _], h => by
    simp only [List.length_cons, List.length_nil] at h
    omega

/-- A list with the words of the main symbols and of nz mask symbols, and no more, is cut. -/
theorem cutParts_isSome (degs : List Bool) (nz : Nat) (w : List UInt64)
    (h : w.length = (degs.map fun e => if e then 3 else 1).sum + 3 * nz) :
    (Fmt.M2.cutParts degs nz w).isSome = true := by
  obtain ⟨ms, w', e1, hl⟩ := takeParts_some degs w (3 * nz) h
  obtain ⟨zs, e2⟩ := takeE_exact nz w' hl
  unfold Fmt.M2.cutParts
  rw [e1]
  show (match Fmt.M1.takeE nz w' with
    | some (zs, []) => some (ms, zs)
    | _ => none).isSome = true
  rw [e2]
  rfl

/-- A column of the right width is always cut. -/
theorem groupCol_isSome (ms : List Fmt.M2.Mem) (fresh : Nat) (w : List UInt64)
    (h : w.length = Fmt.M2.widthOf ms fresh) : (Fmt.M2.groupCol ms fresh w).isSome = true := by
  unfold Fmt.M2.groupCol
  rw [Option.isSome_map]
  exact cutParts_isSome _ _ w h

end OnBytes.Slice

#print axioms OnBytes.Slice.takeParts_some
#print axioms OnBytes.Slice.takeE_exact
#print axioms OnBytes.Slice.cutParts_isSome
#print axioms OnBytes.Slice.groupCol_isSome
