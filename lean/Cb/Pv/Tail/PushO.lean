-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/PushO.lean: a form on entries J, carried along a partial map of J into other entries.

`pushF` (Cb/Pv/Tail/DigBatch.lean) carries a form along a map. A block may name, beside entries that
stand among the committed ones, an entry that is always 0 and stands nowhere. Along a partial map
such an entry is dropped.

Main names:
  `pushO i f`: the form f along i : J → Option J'.
  `pushO_gap`, `pushO_holds`, `pushOL_holds`: its gap at m is the gap of f at the values that m
    gives through i, and 0 where i gives nothing.
  `pushO_co_zero`: it weighs an entry only if f weighs an entry that i takes there.



Terms: lean/GLOSSARY.md.
-/
import Cb.G6.Led

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open TWhole

variable {E J J' : Type} [Field E] [Fintype J] [DecidableEq J']

/-- The form f on the entries J, as a form on the entries J', along the partial map i. -/
def pushO (i : J → Option J') (f : Form E J) : Form E J' :=
  ⟨fun j' => ∑ j, if i j = some j' then f.co j else 0, f.tg⟩

/-- The values that m gives through i; 0 where i gives nothing. -/
def viaO (i : J → Option J') (m : J' → E) (j : J) : E := (i j).elim 0 m

theorem pushO_co_zero (i : J → Option J') (f : Form E J) (j' : J')
    (h : ∀ j, i j = some j' → f.co j = 0) : (pushO i f).co j' = 0 := by
  show ∑ j, (if i j = some j' then f.co j else 0) = 0
  exact Finset.sum_eq_zero fun j _ => by
    by_cases e : i j = some j'
    · rw [if_pos e, h j e]
    · rw [if_neg e]

variable [Fintype J']

theorem pushO_gap (i : J → Option J') (f : Form E J) (m : J' → E) :
    (pushO i f).gap m = f.gap (viaO i m) := by
  unfold pushO Form.gap
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold viaO
  cases h : i j with
  | none => simp
  | some j' => simp [ite_mul, Finset.sum_ite_eq]

theorem pushO_holds (i : J → Option J') (f : Form E J) (m : J' → E) :
    (pushO i f).Holds m ↔ f.Holds (viaO i m) := by
  unfold Form.Holds
  rw [pushO_gap]

theorem pushOL_holds (i : J → Option J') (L : Ledger E J) (m : J' → E) :
    Ledger.Holds (L.map (pushO i)) m ↔ Ledger.Holds L (viaO i m) := by
  unfold Ledger.Holds
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun f _ => pushO_holds i f m

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.pushO_co_zero
#print axioms Cb.Pv.Tail.pushOL_holds
