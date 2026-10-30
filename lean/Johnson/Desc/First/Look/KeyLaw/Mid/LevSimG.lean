-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevSimG.lean: at the standard places (`LevPl.std`, LevStd.lean)
the fields `keys` and `table` of `Sims` (Seams.lean) hold: the orders and the places of all levels
are the course's.

Main names:
  `ordDown_ofFn`, `ordFirst_ofFn` the course's two lists of an order are those of the reversal and
    of `ordOf first k`.
  `ownP_partSum` two counts of the mask entries that the parts below i take agree.
  `table_std`, `keys_std` the two fields.
Limits: D.S = A.toPub; 1 ≤ d; 1 ≤ m; 1 ≤ v i for i < m; for the keys the clause on the named
variables of the last key level (each below the least part's last level; none twice).

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimF
import Johnson.Desc.First.Look.KeyLaw.Mid.LevStdAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev

theorem list_ofFn (l : List ℕ) (k : ℕ) (hl : l.length = k) (f : Fin k → ℕ)
    (h : ∀ j : Fin k, f j = l.getD j.1 0) : l = List.ofFn f :=
  List.ext_getElem (by rw [hl, List.length_ofFn]) fun i h1 _ => by
    rw [List.getElem_ofFn, h, List.getD_eq_getElem _ _ h1]

theorem ordDown_ofFn (k : ℕ) :
    ordDown k = List.ofFn fun j : Fin k => ((Fin.revPerm j : Fin k) : ℕ) :=
  list_ofFn _ k (by unfold ordDown; rw [List.length_reverse, List.length_range]) _ (rev_val k)

theorem ordFirst_ofFn (first : List ℕ) (k : ℕ) (h : BeginOK first k) :
    ordFirst first k = List.ofFn fun j : Fin k => ((ordOf first k j : Fin k) : ℕ) :=
  list_ofFn (beginList first k) k
    ((beginList_perm first k h.1 h.2).length_eq.trans List.length_range) _ (ordOf_val h)

variable (A : Dat GE) (sl : Slot → A.J) (D : Dt)

theorem ownP_partSum (hv : ∀ i < A.m, 1 ≤ A.v i) : ∀ i ≤ A.m, ownP A i = partSum A.toPub i
  | 0, _ => rfl
  | i + 1, hi => by
    have h1 := hv i hi
    obtain ⟨n, hn⟩ : ∃ n, A.v i = n + 1 := ⟨A.v i - 1, by omega⟩
    have hg : grp 0 (A.v i) = ownN 0 n + (2 * (0 + n) + 5) := by
      rw [← ownN_grp, hn]
      rfl
    show ownP A i + (ownN 0 (A.v i - 1) + (2 * (0 + (A.v i - 1)) + 5 - 2)) = _
    rw [partSum_succ, ← ownP_partSum hv i (Nat.le_of_succ_le hi)]
    show _ = ownP A i + (grp 0 (A.v i) - 2)
    rw [hg, hn]
    have e1 : n + 1 - 1 = n := rfl
    rw [e1]
    omega

/-- **The table's tree at the standard places.** -/
theorem table_std (st : A.St) (own idx bK bI : ℕ) (hS : D.S = A.toPub) (hd : 1 ≤ A.d) :
    Goes (Sim A sl st own idx 4) (Sim A sl st own idx 5) (cTable D)
      (A.tableRun (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k)) bK bI
        (own + ownAt A.toPub 4))) (fmT A.mu (A.d - 1)) :=
  table_goes A sl _ D st own idx hS hd fun l _ =>
    ⟨(if_neg Bool.false_ne_true).trans (ordDown_ofFn (A.mu + l)),
      (tab_at A sl D bK bI (own + ownAt A.toPub 4) l (idx + idxAt A.toPub 4)).1,
      (tab_at A sl D bK bI (own + ownAt A.toPub 4) l (idx + idxAt A.toPub 4)).2.1,
      (tab_at A sl D bK bI (own + ownAt A.toPub 4) l (idx + idxAt A.toPub 4)).2.2.1,
      (tab_at A sl D bK bI (own + ownAt A.toPub 4) l (idx + idxAt A.toPub 4)).2.2.2⟩

/-- **The key trees at the standard places.** -/
theorem keys_std (st : A.St) (own idx bT : ℕ) (hS : D.S = A.toPub) (hm : 1 ≤ A.m)
    (hv : ∀ i < A.m, 1 ≤ A.v i)
    (hO : (∀ j ∈ A.order, j + 1 < A.least) ∧ A.order.Nodup) :
    Goes (Sim A sl st own idx 3) (Sim A sl st own idx 4) (cKeys D)
      (A.keysRun (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k))
        (own + ownAt A.toPub 3) (idx + idxAt A.toPub 3) bT))
      (A.keysFm (LevPl.std A (fun k => sl (D.ms k)) (fun k => sl (D.ix k))
        (own + ownAt A.toPub 3) (idx + idxAt A.toPub 3) bT)) := by
  refine keys_goes A sl _ D st own idx hS hm hv fun i hi l hl => ?_
  rw [ownP_partSum A hv i (Nat.le_of_lt hi)]
  by_cases h : l + 1 = A.v i
  · rw [decide_eq_true h]
    have hk := key_last A sl D (own + ownAt A.toPub 3) (idx + idxAt A.toPub 3) bT i l h
    have hb : BeginOK A.order (0 + l) := by
      have h0 := A.toPub.beginOK hO i hi
      have e : A.v i - 1 = l := by omega
      rw [show A.toPub.v i - 1 = l from e] at h0
      exact h0
    refine ⟨?_, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩
    rw [if_pos rfl, hS]
    refine (ordFirst_ofFn A.order (0 + l) hb).trans ?_
    show _ = List.ofFn fun j => ((ordKey A.order (A.v i - 1 + 1) l j : Fin (0 + l)) : ℕ)
    rw [ordKey_last A.order (by omega : l + 1 = A.v i - 1 + 1)]
  · rw [decide_eq_false h]
    have hk := key_at A sl D (own + ownAt A.toPub 3) (idx + idxAt A.toPub 3) bT i l
      (idx + idxAt A.toPub 3 + 2 * i) h
    refine ⟨?_, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩
    rw [if_neg Bool.false_ne_true]
    refine (ordDown_ofFn (0 + l)).trans ?_
    show _ = List.ofFn fun j => ((ordKey A.order (A.v i - 1 + 1) l j : Fin (0 + l)) : ℕ)
    rw [ordKey_other A.order (by omega : l + 1 ≠ A.v i - 1 + 1)]

end Lk6.Mid

#print axioms Lk6.Mid.table_std
#print axioms Lk6.Mid.keys_std
