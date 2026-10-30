-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/WfRoom.lean: the two ledgers have room for every lookup of a key's chain, one after the
other: the arithmetic.

A key's chain runs its lookups in a row. Each takes `ownTotal` entries of the first ledger and
`treesKey` entries of the second (`Caller.Laws.verify_val`, OnBytes/G4/AnyRun.lean). The port sizes
the two ledgers by `Wf.ownMasks` and `Wf.indexMasks` (OnBytes/Iop/Wf.lean), which are sums over the
lookups. Here: if the first ledger has at least `Wf.ownMasks x m` entries left and the second at
least `Wf.indexMasks x m`, then before lookup number i, after the lookups before it have taken
theirs, there is room for lookup number i.

Main names:
  `ownTotal_eq`: a lookup's entries of the first ledger are `Lkp.allMasks` less `Lkp.keyMasks`.
  `ownMasks_eq`, `indexMasks_eq`: the port's two sums are the sums of `ownTotal` and of `treesKey`.
  `takenOwn`, `takenKey`: what the first i lookups take of each ledger; `takenOwn_succ`,
  `takenKey_succ`: one lookup more.
  `room_at`: the room before lookup number i, in numbers a and b of entries left at the start.
  `left_succ`: taking lookup i's entries from what is left before it gives what is left before
  lookup i + 1.
  `lookupOf_getD`: lookup number i as a member of `Wf.lookupsOf`.
Under: every lookup passes the program's test of form (`Lkp.Public.ok`).
Limits: numbers alone. Nothing is said of a ledger: that it is open, what its entries are, or that
  the number of entries that it has left is a or b. `Wf.indexMaskEntries`, which also counts what
  the batching of pending rows takes, is not treated.


-/
import OnBytes.G4.WfCall
import OnBytes.G4.ReadyLaws

set_option autoImplicit false

namespace OnBytes.G4

open OnBytes.Params

/-- A lookup's entries of the first ledger: all its mask entries less those of the second. -/
theorem ownTotal_eq (S : Lkp.Public) (hok : S.ok = true) :
    ownTotal S = Lkp.allMasks S - Lkp.keyMasks S := by
  obtain ⟨h1, h2⟩ := masks_split S hok
  omega

/-- The port's size of the block's own mask rows is the sum of the lookups' `ownTotal`. -/
theorem ownMasks_eq (x : WfPublic) (m : Wf.Matrix)
    (hok : ∀ S ∈ Wf.lookupsOf x m, S.ok = true) :
    Wf.ownMasks x m = ((Wf.lookupsOf x m).map ownTotal).sum := by
  unfold Wf.ownMasks
  rw [sumT_eq]
  exact congrArg List.sum (List.map_congr_left fun S hS => (ownTotal_eq S (hok S hS)).symm)

/-- The port's count of the lookups' entries of the index-mask message is the sum of the lookups'
`treesKey`. -/
theorem indexMasks_eq (x : WfPublic) (m : Wf.Matrix)
    (hok : ∀ S ∈ Wf.lookupsOf x m, S.ok = true) :
    Wf.indexMasks x m = ((Wf.lookupsOf x m).map fun S => treesKey S.parts).sum := by
  unfold Wf.indexMasks
  rw [sumT_eq]
  exact congrArg List.sum (List.map_congr_left fun S hS => (masks_split S (hok S hS)).1.symm)

/-- The first i members of a list of numbers and member number i sum to at most the whole. -/
theorem take_sum_add_le : ∀ (l : List Nat) (i : Nat) (h : i < l.length),
    (l.take i).sum + l[i] ≤ l.sum
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: l, 0, _ => by simp
  | a :: l, i + 1, h => by
    have ih := take_sum_add_le l i (Nat.lt_of_succ_lt_succ h)
    simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
    omega

/-- One member more. -/
theorem take_succ_sum : ∀ (l : List Nat) (i : Nat) (h : i < l.length),
    (l.take (i + 1)).sum = (l.take i).sum + l[i]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: l, 0, _ => by simp
  | a :: l, i + 1, h => by
    have ih := take_succ_sum l i (Nat.lt_of_succ_lt_succ h)
    simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
    omega

/-- What the first i lookups take of the first ledger. -/
def takenOwn (x : WfPublic) (m : Wf.Matrix) (i : Nat) : Nat :=
  (((Wf.lookupsOf x m).map ownTotal).take i).sum

/-- What the first i lookups take of the second ledger. -/
def takenKey (x : WfPublic) (m : Wf.Matrix) (i : Nat) : Nat :=
  (((Wf.lookupsOf x m).map fun S => treesKey S.parts).take i).sum

/-- Lookup number i, as the run names it, is member number i of the port's list. -/
theorem lookupOf_getD (x : WfPublic) (m : Wf.Matrix) (i : Nat) (hi : i < x.lookups.length) :
    Wf.lookupOf x.messageId m (x.lookups.getD i default) =
      (Wf.lookupsOf x m)[i]'(by rw [Wf.lookupsOf, List.length_map]; exact hi) := by
  unfold Wf.lookupsOf
  rw [List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem takenOwn_zero (x : WfPublic) (m : Wf.Matrix) : takenOwn x m 0 = 0 := rfl

theorem takenKey_zero (x : WfPublic) (m : Wf.Matrix) : takenKey x m 0 = 0 := rfl

/-- One lookup more, in the first ledger. -/
theorem takenOwn_succ (x : WfPublic) (m : Wf.Matrix) (i : Nat) (hi : i < x.lookups.length) :
    takenOwn x m (i + 1) =
      takenOwn x m i + ownTotal (Wf.lookupOf x.messageId m (x.lookups.getD i default)) := by
  have hl : i < ((Wf.lookupsOf x m).map ownTotal).length := by
    rw [List.length_map, Wf.lookupsOf, List.length_map]
    exact hi
  unfold takenOwn
  rw [take_succ_sum _ i hl, List.getElem_map, lookupOf_getD x m i hi]

/-- One lookup more, in the second ledger. -/
theorem takenKey_succ (x : WfPublic) (m : Wf.Matrix) (i : Nat) (hi : i < x.lookups.length) :
    takenKey x m (i + 1) =
      takenKey x m i +
        treesKey (Wf.lookupOf x.messageId m (x.lookups.getD i default)).parts := by
  have hl : i < ((Wf.lookupsOf x m).map fun S => treesKey S.parts).length := by
    rw [List.length_map, Wf.lookupsOf, List.length_map]
    exact hi
  unfold takenKey
  rw [take_succ_sum _ i hl, List.getElem_map, lookupOf_getD x m i hi]

/-- The room before lookup number i. a and b: the entries that the two ledgers have left before the
first lookup. -/
theorem room_at (x : WfPublic) (m : Wf.Matrix) (hok : ∀ S ∈ Wf.lookupsOf x m, S.ok = true)
    (a b : Nat) (ha : Wf.ownMasks x m ≤ a) (hb : Wf.indexMasks x m ≤ b) (i : Nat)
    (hi : i < x.lookups.length) :
    ownTotal (Wf.lookupOf x.messageId m (x.lookups.getD i default)) ≤ a - takenOwn x m i ∧
      treesKey (Wf.lookupOf x.messageId m (x.lookups.getD i default)).parts ≤
        b - takenKey x m i := by
  have hl1 : i < ((Wf.lookupsOf x m).map ownTotal).length := by
    rw [List.length_map, Wf.lookupsOf, List.length_map]
    exact hi
  have hl2 : i < ((Wf.lookupsOf x m).map fun S => treesKey S.parts).length := by
    rw [List.length_map, Wf.lookupsOf, List.length_map]
    exact hi
  have h1 := take_sum_add_le _ i hl1
  have h2 := take_sum_add_le _ i hl2
  rw [List.getElem_map, ← lookupOf_getD x m i hi, ← ownMasks_eq x m hok] at h1
  rw [List.getElem_map, ← lookupOf_getD x m i hi, ← indexMasks_eq x m hok] at h2
  unfold takenOwn takenKey
  constructor <;> omega

/-- Taking lookup i's entries from what is left before it gives what is left before the next. -/
theorem left_succ (x : WfPublic) (m : Wf.Matrix) (a b i : Nat) (hi : i < x.lookups.length) :
    a - takenOwn x m i - ownTotal (Wf.lookupOf x.messageId m (x.lookups.getD i default)) =
        a - takenOwn x m (i + 1) ∧
      b - takenKey x m i -
          treesKey (Wf.lookupOf x.messageId m (x.lookups.getD i default)).parts =
        b - takenKey x m (i + 1) := by
  rw [takenOwn_succ x m i hi, takenKey_succ x m i hi]
  constructor <;> omega

end OnBytes.G4

#print axioms OnBytes.G4.room_at
#print axioms OnBytes.G4.left_succ
