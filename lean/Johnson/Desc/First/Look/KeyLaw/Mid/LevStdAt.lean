-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevStdAt.lean: at the places LevPl.std every level of the table's
tree and of the parts' trees has its places where the fresh mask entries of the course over the
field stand.

The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean); that the program's run, read in the field, is this
course is not shown in this file.

Statements and proofs: four of the five fields of PlAt
(Johnson/Desc/First/Look/KeyLaw/Mid/LevSimD.lean), the one on the order of the rounds left out, at
the value LevPl.std (Cb/Pv/KeyLookup/LevStd.lean) of the places, with ms k := sl (D.ms k) and ix k
:= sl (D.ix k).

Main names:
  wvF_off, wcF_off: for every list fr of fresh entries: wvF sl k fr r t is sl of fr's entry number
    offW k (nmV k r t), and wcF sl k fr that of number offW k (nmC k). No premise.
  frAt_lo: entry i < 2 k + 3 of frAt D last k own idx is D.ms (own + i). frAt_c: at last = false the
    entries 2 k + 3 and 2 k + 4 are D.ms (own + 2 k + 3), D.ms (own + 2 k + 4); at last = true they
    are D.ix idx, D.ix (idx + 1).
  ownN_grp: ownN g l = Lev.grp g l.
  tab_at: the table's level l, at last = false, own := bT + ownN A.mu l, every idx.
  key_at: level l of part i's tree with l + 1 ≠ A.v i, at last = false, own := bK + partSum A.toPub
    i + ownN 0 l, every idx.
  key_last: the level l with l + 1 = A.v i, at last = true, the same own, idx := bI + 2 i.

Limits: the premises named. Nothing on the order of the rounds.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimD
import Johnson.Desc.First.Look.KeyLaw.Mid.LevStdSim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev

theorem getD_drop2 {α : Type} (l : List α) (i : ℕ) (d : α) :
    (l.drop 2).getD i d = l.getD (2 + i) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

section
variable {J : Type} (sl : Slot → J)

theorem wcF_off : ∀ (k : ℕ) (fr : List Slot),
    wcF sl k fr = sl (fr.getD (offW (E := GE) k (nmC GE k)) ⟨0, 0⟩)
  | 0, _ => rfl
  | k + 1, fr => by
    show wcF sl k (fr.drop 2) = sl (fr.getD (2 + offW (E := GE) k (nmC GE k)) ⟨0, 0⟩)
    rw [wcF_off k (fr.drop 2), getD_drop2]

theorem wvF_off (t : Fin 2) : ∀ (k : ℕ) (fr : List Slot) (r : ℕ),
    wvF sl k fr r t = sl (fr.getD (offW (E := GE) k (nmV GE k r t)) ⟨0, 0⟩)
  | 0, _, _ => rfl
  | _ + 1, _, 0 => rfl
  | k + 1, fr, r + 1 => by
    show wvF sl k (fr.drop 2) r t = sl (fr.getD (2 + offW (E := GE) k (nmV GE k r t)) ⟨0, 0⟩)
    rw [wvF_off t k (fr.drop 2) r, getD_drop2]

end

theorem slots_length (e : ℕ → Slot) (b n : ℕ) : (slots e b n).length = n := by
  unfold slots
  rw [List.length_map, List.length_range]

theorem frAt_lo (D : Dt) (last : Bool) (k own idx i : ℕ) (h : i < 2 * k + 3) (d : Slot) :
    (frAt D last k own idx).getD i d = D.ms (own + i) := by
  cases last
  · show (slots D.ms own (2 * k + 5)).getD i d = _
    exact slots_getD _ _ _ _ (by omega) d
  · show (slots D.ms own (2 * k + 5 - 2) ++ slots D.ix idx 2).getD i d = _
    rw [List.getD_append _ _ _ _ (by rw [slots_length]; omega)]
    exact slots_getD _ _ _ _ (by omega) d

theorem frAt_c_false (D : Dt) (k own idx i : ℕ) (h : i < 2) (d : Slot) :
    (frAt D false k own idx).getD (2 * k + 3 + i) d = D.ms (own + (2 * k + 3 + i)) :=
  slots_getD _ _ _ _ (by omega) d

theorem frAt_c_true (D : Dt) (k own idx i : ℕ) (h : i < 2) (d : Slot) :
    (frAt D true k own idx).getD (2 * k + 3 + i) d = D.ix (idx + i) := by
  show (slots D.ms own (2 * k + 5 - 2) ++ slots D.ix idx 2).getD (2 * k + 3 + i) d = _
  rw [List.getD_append_right _ _ _ _ (by rw [slots_length]; omega), slots_length]
  have e : 2 * k + 3 + i - (2 * k + 5 - 2) = i := by omega
  rw [e]
  exact slots_getD _ _ _ _ h d

theorem ownN_grp (g : ℕ) : ∀ l, ownN g l = grp g l
  | 0 => rfl
  | l + 1 => by
    rw [grp_succ, ← ownN_grp g l]
    rfl

section
variable (A : Dat GE) (sl : Slot → A.J) (D : Dt) (bK bI bT : ℕ)

/-- The table's level l. -/
theorem tab_at (l idx : ℕ) :
    (A.tabD (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT)).wv l =
        wvF sl (A.mu + l) (frAt D false (A.mu + l) (bT + ownN A.mu l) idx) ∧
      (A.tabD (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT)).wc l =
        wcF sl (A.mu + l) (frAt D false (A.mu + l) (bT + ownN A.mu l) idx) ∧
      (A.tabD (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT)).c l false =
        sl ((frAt D false (A.mu + l) (bT + ownN A.mu l) idx).getD (2 * (A.mu + l) + 3) ⟨0, 0⟩) ∧
      (A.tabD (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT)).c l true =
        sl ((frAt D false (A.mu + l) (bT + ownN A.mu l) idx).getD (2 * (A.mu + l) + 4) ⟨0, 0⟩) := by
  rw [ownN_grp]
  refine ⟨funext fun r => funext fun t => ?_, ?_, ?_, ?_⟩
  · rw [wvF_off, frAt_lo D false _ _ _ _ (offW_lt _ _)]
    rfl
  · rw [wcF_off, frAt_lo D false _ _ _ _ (offW_lt _ _)]
    rfl
  · rw [frAt_c_false D (A.mu + l) _ idx 0 (by omega)]
    rfl
  · rw [frAt_c_false D (A.mu + l) _ idx 1 (by omega)]
    show sl (D.ms (bT + grp A.mu l + (2 * (A.mu + l) + 3) + 1)) = _
    rw [Nat.add_assoc]

/-- A level of part i's tree that is not its last. -/
theorem key_at (i l idx : ℕ) (h : l + 1 ≠ A.v i) :
    (partD (A.part (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT) i)).wv l =
        wvF sl (0 + l) (frAt D false (0 + l) (bK + partSum A.toPub i + ownN 0 l) idx) ∧
      (partD (A.part (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT) i)).wc l =
        wcF sl (0 + l) (frAt D false (0 + l) (bK + partSum A.toPub i + ownN 0 l) idx) ∧
      (partD (A.part (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT) i)).c l
          false =
        sl ((frAt D false (0 + l) (bK + partSum A.toPub i + ownN 0 l) idx).getD
          (2 * (0 + l) + 3) ⟨0, 0⟩) ∧
      (partD (A.part (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT) i)).c l
          true =
        sl ((frAt D false (0 + l) (bK + partSum A.toPub i + ownN 0 l) idx).getD
          (2 * (0 + l) + 4) ⟨0, 0⟩) := by
  rw [ownN_grp]
  refine ⟨funext fun r => funext fun t => ?_, ?_, ?_, ?_⟩
  · rw [wvF_off, frAt_lo D false _ _ _ _ (offW_lt _ _)]
    rfl
  · rw [wcF_off, frAt_lo D false _ _ _ _ (offW_lt _ _)]
    rfl
  · rw [frAt_c_false D (0 + l) _ idx 0 (by omega)]
    show (if l + 1 = A.v i then _ else
      sl (D.ms (bK + partSum A.toPub i + grp 0 l + (2 * l + 3) + 0))) = _
    rw [if_neg h, Nat.zero_add]
    rfl
  · rw [frAt_c_false D (0 + l) _ idx 1 (by omega)]
    show (if l + 1 = A.v i then _ else
      sl (D.ms (bK + partSum A.toPub i + grp 0 l + (2 * l + 3) + 1))) = _
    rw [if_neg h, Nat.zero_add, Nat.add_assoc]

/-- The last level of part i's tree. -/
theorem key_last (i l : ℕ) (h : l + 1 = A.v i) :
    (partD (A.part (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT) i)).wv l =
        wvF sl (0 + l)
          (frAt D true (0 + l) (bK + partSum A.toPub i + ownN 0 l) (bI + 2 * i)) ∧
      (partD (A.part (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT) i)).wc l =
        wcF sl (0 + l)
          (frAt D true (0 + l) (bK + partSum A.toPub i + ownN 0 l) (bI + 2 * i)) ∧
      (partD (A.part (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT) i)).c l
          false =
        sl ((frAt D true (0 + l) (bK + partSum A.toPub i + ownN 0 l) (bI + 2 * i)).getD
          (2 * (0 + l) + 3) ⟨0, 0⟩) ∧
      (partD (A.part (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI bT) i)).c l
          true =
        sl ((frAt D true (0 + l) (bK + partSum A.toPub i + ownN 0 l) (bI + 2 * i)).getD
          (2 * (0 + l) + 4) ⟨0, 0⟩) := by
  rw [ownN_grp]
  refine ⟨funext fun r => funext fun t => ?_, ?_, ?_, ?_⟩
  · rw [wvF_off, frAt_lo D true _ _ _ _ (offW_lt _ _)]
    rfl
  · rw [wcF_off, frAt_lo D true _ _ _ _ (offW_lt _ _)]
    rfl
  · rw [frAt_c_true D (0 + l) _ _ 0 (by omega)]
    show (if l + 1 = A.v i then sl (D.ix (bI + 2 * i + 0)) else _) = _
    rw [if_pos h]
  · rw [frAt_c_true D (0 + l) _ _ 1 (by omega)]
    show (if l + 1 = A.v i then sl (D.ix (bI + 2 * i + 1)) else _) = _
    rw [if_pos h]

end
end Lk6.Mid

#print axioms Lk6.Mid.wvF_off
#print axioms Lk6.Mid.wcF_off
#print axioms Lk6.Mid.tab_at
#print axioms Lk6.Mid.key_at
#print axioms Lk6.Mid.key_last
