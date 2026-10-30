-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/Closed.lean: two closed facts on `lookUpd`
(Honest/K3/Shape/Ops.lean): the count of slots goes on by the face's number of slots; three claims
more are owed, none marked as added. On the code alone: no ledger, no hearing. Theorems; two small
definitions.

Terms. Honest/K3/GLOSSARY.md: see there ledger, slot, face and shape (of the ledger). The steps and
`runOps` are those of Ops.lean.

What is shown.
  `runOps_next`: the count behind a list of steps: the count in front and the steps' lengths.
  `lookOps_len`: at a face that passes its own test the steps' lengths sum to `Face.slots`.
  `lookUpd_next`: f.ok = true → (lookUpd f L).next = L.next + f.slots.
  `lookUpd_owed`: (lookUpd f L).owed = L.owed ++ [false, false, false].
  `lookUpd_frame`: the number of slots and the two sizes stay.
Definitions: `Op.len`, `Op.quiet`. The other theorems are helpers on lengths (`len_…`) and on steps
that owe nothing (`quiet_…`).

Hypotheses that remain.
  `h`: (in `lookOps_len`, `lookUpd_next`) the face passes its own test; it gives that a level's
    order has as many entries as the level has variables. The others have none.

Users. Honest/K3/Shape/Window.lean imports this file.

Limits. Nothing on the marks: that `lookUpd` marks all of the lookup's slots but the leaves' own is
seen at three faces (Honest/K3/Shape/Guards.lean [not in this library], by evaluation), not proved.
Shown in part: `hearV_full` (Honest/K3/Parts/Packs.lean): of ledgers: behind a hearing that returns,
from a ledger whose arrays have their size, every slot of the lookup's window but the leaves' own is
filled. What stays open: of the code `lookUpd` itself it is seen at the three faces alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Ops
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanesReturn
import Johnson.Desc.ProofFile.Honest.K3.Parts.NamesMarks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (zeroE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.First.Shape (LedSh)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (ownSlots)
open VerifiableInference.Desc.K3 (noVar leafVars bitsCall)
open ProofFile.Honest.K3.Law (own_leafVars own_bits)
open ProofFile.Honest.K3.Parts (own_levelVars)

local notation "KFace" => VerifiableInference.Desc.K3.Face

/-- How many slots a step takes. -/
def Op.len : Op → Nat
  | .sum o e => o + e
  | .left o => o
  | .owe => 0

/-- The step adds no owed claim. -/
def Op.quiet : Op → Bool
  | .owe => false
  | _ => true

/-! ## 1 The count of slots -/

theorem on_next (o : Op) (L : LedSh) : (o.on L).next = L.next + o.len := by
  cases o with
  | sum o e =>
    show L.next + o + e = L.next + (o + e)
    omega
  | left o => rfl
  | owe => rfl

theorem runOps_next : ∀ (l : List Op) (L : LedSh),
    (runOps l L).next = L.next + (l.map Op.len).sum
  | [], _ => rfl
  | o :: l, L => by
    show (runOps l (o.on L)).next = _
    rw [runOps_next l, on_next, List.map_cons, List.sum_cons]
    omega

theorem len_same {α : Type} (b : Op) : ∀ l : List α,
    ((l.flatMap fun _ => [b]).map Op.len).sum = l.length * b.len
  | [] => by simp
  | _ :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, len_same b l, List.length_cons]
    simp [Nat.succ_mul]
    omega

theorem len_tie (w : Nat) : ((tieOps w).map Op.len).sum = 7 + 6 * (w - 2) := by
  unfold tieOps
  rw [List.map_append, List.sum_append, len_same, List.length_range]
  show (4 + 3 + 0) + (w - 2) * (4 + 2) = _
  omega

theorem len_parts : ∀ n : Nat, ((partsOps n).map Op.len).sum = 5 * n
  | 0 => rfl
  | n + 1 => by
    unfold partsOps
    rw [List.map_append, List.sum_append, len_parts n]
    show (3 + 2 + 0) + 5 * n = _
    omega

theorem len_level (order : List Nat) : (levelOp order).len = 2 * order.length + 5 := by
  show ownSlots (⟨0, VerifiableInference.Desc.First.ProdV.levelVars 0 #[] order,
    some VerifiableInference.Desc.First.ProdV.levelEnds⟩ : MaskedSum.Call).all + 2 = _
  rw [own_levelVars]

theorem len_levels (m0 : Nat) (orders : Nat → List Nat) : ∀ l : List Nat,
    (∀ i ∈ l, (orders (m0 + i)).length = m0 + i) →
    ((levelOps m0 orders l).map Op.len).sum = (l.map fun i => 2 * (m0 + i) + 5).sum
  | [], _ => rfl
  | i :: l, h => by
    show (levelOp (orders (m0 + i))).len + ((levelOps m0 orders l).map Op.len).sum = _
    rw [len_level, h i (List.mem_cons_self ..),
      len_levels m0 orders l fun j hj => h j (List.mem_cons_of_mem _ hj), List.map_cons,
      List.sum_cons]

theorem len_keys (f : KFace) : ∀ xs : List (Nat × Nat),
    (∀ x ∈ xs, ∀ i ∈ List.range x.1, (f.orders x.2 (0 + i)).length = 0 + i) →
    ((keysOps f xs).map Op.len).sum =
      (xs.map fun x => ((List.range x.1).map fun k => 2 * k + 5).sum).sum
  | [], _ => rfl
  | x :: xs, h => by
    unfold keysOps
    rw [List.map_append, List.sum_append, len_levels 0 _ _ (h x (List.mem_cons_self ..)),
      len_keys f xs fun y hy => h y (List.mem_cons_of_mem _ hy), List.map_cons, List.sum_cons]
    simp

/-- A face that passes its own test: a key level's order has as many entries as the level has
variables. -/
theorem orders_len {f : KFace} (h : f.ok = true) :
    ∀ x ∈ f.parts.zipIdx, ∀ i ∈ List.range x.1, (f.orders x.2 (0 + i)).length = 0 + i := by
  unfold VerifiableInference.Desc.K3.Face.ok at h
  simp only [Bool.and_eq_true] at h
  intro x hx i hi
  have h9 := List.all_eq_true.1 h.2 x hx
  unfold VerifiableInference.Desc.First.Prod.runOk at h9
  rw [Bool.and_eq_true] at h9
  have h10 := List.all_eq_true.1 h9.2 i hi
  unfold VerifiableInference.Desc.First.Prod.orderOk at h10
  simp only [Bool.and_eq_true, beq_iff_eq] at h10
  exact h10.1.1

theorem map_zipIdx_fst (g : Nat → Nat) : ∀ (l : List Nat) (n : Nat),
    ((l.zipIdx n).map fun x => g x.1) = l.map g
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, map_zipIdx_fst g l]

theorem sum_zipIdx (l : List Nat) (g : Nat → Nat) :
    (l.zipIdx.map fun x => g x.1).sum = (l.map g).sum := by
  rw [map_zipIdx_fst]

/-- **At a face that passes its own test the steps' lengths sum to the face's number of slots.** -/
theorem lookOps_len {f : KFace} (h : f.ok = true) : ((lookOps f).map Op.len).sum = f.slots := by
  unfold lookOps VerifiableInference.Desc.K3.Face.slots
  simp only [List.map_append, List.sum_append]
  rw [len_tie, len_parts, len_keys f _ (orders_len h),
    sum_zipIdx f.parts (fun v => ((List.range v).map fun k => 2 * k + 5).sum),
    len_levels f.mu orderDefault _ (fun i _ => by simp [orderDefault])]
  show 0 + 0 + (0 + 0 + (0 + 0 + (_ + (_ + (_ + (_ + ((ownSlots (leafVars f #[]) + 0) +
    ((ownSlots (bitsCall (List.replicate (f.mu + f.d) zeroE)).all + 1) + 0)))))))) = _
  rw [own_leafVars, own_bits, List.length_replicate]
  omega

/-- **The count of slots goes on by the face's number of slots.** Conditional on the face's own
test. -/
theorem lookUpd_next {f : KFace} (h : f.ok = true) (L : LedSh) :
    (lookUpd f L).next = L.next + f.slots := by
  unfold lookUpd
  rw [runOps_next, lookOps_len h]

/-! ## 2 The owed claims; what stays -/

theorem on_owed_quiet (o : Op) (h : o.quiet = true) (L : LedSh) : (o.on L).owed = L.owed := by
  cases o with
  | sum o e => rfl
  | left o => rfl
  | owe => exact nomatch h

theorem runOps_owed_quiet : ∀ (l : List Op) (L : LedSh), l.all Op.quiet = true →
    (runOps l L).owed = L.owed
  | [], _, _ => rfl
  | o :: l, L, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    show (runOps l (o.on L)).owed = _
    rw [runOps_owed_quiet l _ h.2, on_owed_quiet o h.1]

theorem quiet_levels (m0 : Nat) (orders : Nat → List Nat) (l : List Nat) :
    (levelOps m0 orders l).all Op.quiet = true := by
  unfold levelOps
  rw [List.all_map]
  exact List.all_eq_true.2 fun _ _ => rfl

theorem quiet_tie (w : Nat) : (tieOps w).all Op.quiet = true := by
  unfold tieOps
  rw [List.all_append, List.all_flatMap]
  exact Bool.and_eq_true_iff.2 ⟨rfl, List.all_eq_true.2 fun _ _ => rfl⟩

theorem quiet_parts : ∀ n : Nat, (partsOps n).all Op.quiet = true
  | 0 => rfl
  | n + 1 => by
    unfold partsOps
    rw [List.all_append, quiet_parts n]
    rfl

theorem quiet_keys (f : KFace) : ∀ xs : List (Nat × Nat), (keysOps f xs).all Op.quiet = true
  | [] => rfl
  | x :: xs => by
    unfold keysOps
    rw [List.all_append, quiet_levels, quiet_keys f xs]
    rfl

/-- **Three claims more are owed, none marked as added.** No hypothesis. -/
theorem lookUpd_owed (f : KFace) (L : LedSh) :
    (lookUpd f L).owed = L.owed ++ [false, false, false] := by
  unfold lookUpd lookOps
  rw [runOps_append, runOps_append, runOps_append, runOps_owed_quiet]
  · show ((L.owed ++ [false]) ++ [false]) ++ [false] = _
    simp
  · simp only [List.all_append, quiet_tie, quiet_parts, quiet_keys, quiet_levels, Bool.true_and]
    rfl

theorem on_frame (o : Op) (L : LedSh) :
    (o.on L).ns = L.ns ∧ (o.on L).shown = L.shown ∧ (o.on L).factors = L.factors := by
  cases o <;> exact ⟨rfl, rfl, rfl⟩

theorem runOps_frame : ∀ (l : List Op) (L : LedSh),
    (runOps l L).ns = L.ns ∧ (runOps l L).shown = L.shown ∧ (runOps l L).factors = L.factors
  | [], _ => ⟨rfl, rfl, rfl⟩
  | o :: l, L => by
    obtain ⟨a, b, c⟩ := runOps_frame l (o.on L)
    obtain ⟨a', b', c'⟩ := on_frame o L
    exact ⟨a.trans a', b.trans b', c.trans c'⟩

/-- The number of slots and the two sizes stay. No hypothesis. -/
theorem lookUpd_frame (f : KFace) (L : LedSh) :
    (lookUpd f L).ns = L.ns ∧ (lookUpd f L).shown = L.shown ∧
      (lookUpd f L).factors = L.factors := runOps_frame _ L

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.on_next
#print axioms ProofFile.Honest.K3.Shape.runOps_next
#print axioms ProofFile.Honest.K3.Shape.len_same
#print axioms ProofFile.Honest.K3.Shape.len_tie
#print axioms ProofFile.Honest.K3.Shape.len_parts
#print axioms ProofFile.Honest.K3.Shape.len_level
#print axioms ProofFile.Honest.K3.Shape.len_levels
#print axioms ProofFile.Honest.K3.Shape.len_keys
#print axioms ProofFile.Honest.K3.Shape.orders_len
#print axioms ProofFile.Honest.K3.Shape.map_zipIdx_fst
#print axioms ProofFile.Honest.K3.Shape.sum_zipIdx
#print axioms ProofFile.Honest.K3.Shape.lookOps_len
#print axioms ProofFile.Honest.K3.Shape.lookUpd_next
#print axioms ProofFile.Honest.K3.Shape.on_owed_quiet
#print axioms ProofFile.Honest.K3.Shape.runOps_owed_quiet
#print axioms ProofFile.Honest.K3.Shape.quiet_levels
#print axioms ProofFile.Honest.K3.Shape.quiet_tie
#print axioms ProofFile.Honest.K3.Shape.quiet_parts
#print axioms ProofFile.Honest.K3.Shape.quiet_keys
#print axioms ProofFile.Honest.K3.Shape.lookUpd_owed
#print axioms ProofFile.Honest.K3.Shape.on_frame
#print axioms ProofFile.Honest.K3.Shape.runOps_frame
#print axioms ProofFile.Honest.K3.Shape.lookUpd_frame
