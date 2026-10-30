-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/InsideOfShapes.lean: WHERE A MEMBER's MESSAGE HAS A WEIGHT, THE ENTRY THAT BELONGS TO THE INDEX LIES
INSIDE THAT MESSAGE's OWN TABLE: AT A GROUP THAT HOLDS A WRITTEN LIST's MEMBERS. Theorems.

Why. `TiedOwes` (TiedLaidIn.lean beside this file: what is left of K10's clause «tied», by name) has three fields on
indices: inMain, inKept, inMask. They were shown of nothing. This file pays them at `groupLayK` | `namesOf`.

What is said, under T.layout g = some L; `ShapesAre T G lo kb no`; at a member a of the written list:
  `inMain_of_shapes`: L.k = s.h + s.g: where a's message has a weight at the index (b's number + 2 ^ (s.h + s.g) * x),
    x below the stage's main code's message length: `mainBack` of the index is below 2 ^ (the message's main bits).
  `inKept_of_shapes`: hinj: a slot that bears a's number: its index at the place x is below the same bound.
  `inMask_of_shapes`: L.h = s.h: the like of inMain for the mask table.
How. `unshift` a (k - a) (n + 2 ^ k * x) = n % 2 ^ a + 2 ^ a * x for n < 2 ^ k and a ≤ k; that is below 2 ^ a * (x + 1); the
code's message length is at most 2 to its ceilLog2. THE WEIGHT IS USED ONLY FOR «the member has a block» (so a ≤ k; and,
for the mask, that the member has mask rows at all).

Limits. `ShapesAre` and hinj are shown of no verifier's state here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.BlockOfShapes
import Johnson.Desc.K1.Law.Port4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G
open Cb
open OnBytes.LayLaw (layout_blocksOk)
open VerifiableInference.Desc.First.Close

/-- An index (row r, place x) of a table with 2 ^ a rows and at most 2 ^ c places. -/
theorem idx_inside {a c r x l : ℕ} (hr : r < 2 ^ a) (hx : x < l) (hl : l ≤ 2 ^ c) :
    r + 2 ^ a * x < 2 ^ (a + c) := by
  calc r + 2 ^ a * x < 2 ^ a + 2 ^ a * x := by omega
    _ = 2 ^ a * (x + 1) := by ring
    _ ≤ 2 ^ a * 2 ^ c := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (a + c) := (pow_add 2 _ _).symm

/-- The index without the block's number, at (row n, place x) of the group's table. -/
theorem unshift_at {a k n x : ℕ} (ha : a ≤ k) (hn : n < 2 ^ k) :
    unshift a (k - a) (n + 2 ^ k * x) = n % 2 ^ a + 2 ^ a * x := by
  unfold unshift
  have e1 : a + (k - a) = k := by omega
  have e2 : 2 ^ k = 2 ^ a * 2 ^ (k - a) := by rw [← pow_add, e1]
  rw [e1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hn, Nat.zero_add]
  congr 1
  rw [e2, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- A message with a weight on the main table has a block there. -/
theorem main_block_of_weight {T : Statement} {L : GroupLayout} {o J : ℕ}
    (h : mainWeight (K := GE) T L o J ≠ 0) :
    ∃ i first, L.find o = some i ∧ L.mainFirst.getD i none = some first := by
  unfold mainWeight at h
  cases hf : L.find o with
  | none => simp [hf] at h
  | some i =>
    cases hm : L.mainFirst.getD i none with
    | none => simp [hf, hm] at h
    | some first => exact ⟨i, first, rfl, hm⟩

/-- The like on the mask table. -/
theorem mask_block_of_weight {T : Statement} {L : GroupLayout} {o J : ℕ}
    (h : maskWeight (K := GE) T L o J ≠ 0) :
    ∃ i first, L.find o = some i ∧ L.maskFirst.getD i none = some first := by
  unfold maskWeight at h
  cases hf : L.find o with
  | none => simp [hf] at h
  | some i =>
    cases hm : L.maskFirst.getD i none with
    | none => simp [hf, hm] at h
    | some first => exact ⟨i, first, rfl, hm⟩

variable {cs : Codes} {lo : List (OracleShape × ℕ)} {s : Sg} {e : ℕ} {kb : Fin lo.length → Bool}
  {hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C}
  {hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z}
  {no : Fin lo.length → ℕ} {T : Statement} {G : Group} {g : ℕ} {L : GroupLayout}

include hM in
/-- **ON THE MAIN TABLE.** -/
theorem inMain_of_shapes (hL : T.layout g = some L) (H : ShapesAre T G lo kb no)
    (hk : L.k = s.h + s.g) (a : {i // memMain lo i}) (b : Fin (s.h + s.g) → Bool)
    (x : Fin s.C.l)
    (hw : mainWeight (K := GE) T L (no a.1) (Sz.rowNo b + 2 ^ (s.h + s.g) * x.val) ≠ 0) :
    mainBack T L (no a.1) (Sz.rowNo b + 2 ^ (s.h + s.g) * x.val) <
      2 ^ (K1.Msg.of cs (lo.get a.1).1).bits .main := by
  have hm : a.1 ∈ membersOf lo := mem_members.2 a.2
  obtain ⟨i, first, hf, hfi⟩ := main_block_of_weight hw
  have hb := (layout_blocksOk T g L hL).1 _ _ _ hf hfi
  have hl : s.C.l = (pMain cs (lo.get a.1).1).ell := by rw [← hM a.1 a.2 a.2]; rfl
  have hrb : T.rowBits (no a.1) .main = k1 (lo.get a.1).1 := (has_of_shape (H.shape _ hm) .main).2
  unfold mainBack
  rw [K1.bits_main cs _ (Nat.pos_of_ne_zero a.2), hk, unshift_at (hk ▸ hb.le) (rowNo_lt b), hrb]
  exact idx_inside (Nat.mod_lt _ (Nat.two_pow_pos _)) (hl ▸ x.isLt) (le_two_pow_ceilLog2 _)

/-- **IN A KEPT SLOT.** -/
theorem inKept_of_shapes
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (a : {i // memMain lo i}) (q : (groupLayK cs lo s e kb hM hZ).Kp) (x : Fin s.C.l)
    (hq : (namesOf cs lo s e kb hM hZ no).orc q = no a.1) :
    (namesOf cs lo s e kb hM hZ no).idx q x < 2 ^ (K1.Msg.of cs (lo.get a.1).1).bits .main := by
  have ea : q.1.1.1 = a.1 := hinj _ (mem_members.2 q.1.1.2) _ (mem_members.2 a.2) hq
  have hl : s.C.l = (pMain cs (lo.get q.1.1.1).1).ell := by
    rw [← hM q.1.1.1 q.1.1.2 q.1.1.2]; rfl
  rw [← ea, K1.bits_main cs _ (Nat.pos_of_ne_zero q.1.1.2)]
  show q.2.val + x.val * 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows < _
  rw [Nat.mul_comm]
  exact idx_inside (lt_of_lt_of_le q.2.2 (le_two_pow_ceilLog2 _)) (hl ▸ x.isLt)
    (le_two_pow_ceilLog2 _)

include hZ in
/-- **ON THE MASK TABLE.** -/
theorem inMask_of_shapes (hG : T.groups[g]? = some G) (hL : T.layout g = some L)
    (hOk : GroupOk T G) (H : ShapesAre T G lo kb no) (hh : L.h = s.h)
    (a : {i // memMain lo i}) (b : Fin s.h → Bool) (y : Fin s.Z.l)
    (hw : maskWeight (K := GE) T L (no a.1) (Sz.rowNo b + 2 ^ s.h * y.val) ≠ 0) :
    maskBack T L (no a.1) (Sz.rowNo b + 2 ^ s.h * y.val) <
      2 ^ (K1.Msg.of cs (lo.get a.1).1).bits .mask := by
  have hm : a.1 ∈ membersOf lo := mem_members.2 a.2
  obtain ⟨i, first, hf, hfi⟩ := mask_block_of_weight hw
  obtain ⟨hhas, hb⟩ := (layFacts hG hL hOk).mask_block _ i first hf hfi
  have hz : 0 < (lo.get a.1).1.maskRows := by
    rw [(has_of_shape (H.shape _ hm) .mask).1] at hhas
    exact of_decide_eq_true hhas
  have hl : s.Z.l = (pMask cs (lo.get a.1).1).ell := by
    rw [← hZ a.1 a.2 (Nat.pos_iff_ne_zero.1 hz)]; rfl
  have hrb : T.rowBits (no a.1) .mask = k2 (lo.get a.1).1 := (has_of_shape (H.shape _ hm) .mask).2
  unfold maskBack
  rw [K1.bits_mask cs _ hz, hh, unshift_at (hh ▸ hb.le) (rowNo_lt b), hrb]
  exact idx_inside (Nat.mod_lt _ (Nat.two_pow_pos _)) (hl ▸ y.isLt) (le_two_pow_ceilLog2 _)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.idx_inside
#print axioms VerifiableInference.Desc.LinkJoin.unshift_at
#print axioms VerifiableInference.Desc.LinkJoin.main_block_of_weight
#print axioms VerifiableInference.Desc.LinkJoin.mask_block_of_weight
#print axioms VerifiableInference.Desc.LinkJoin.inMain_of_shapes
#print axioms VerifiableInference.Desc.LinkJoin.inKept_of_shapes
#print axioms VerifiableInference.Desc.LinkJoin.inMask_of_shapes
