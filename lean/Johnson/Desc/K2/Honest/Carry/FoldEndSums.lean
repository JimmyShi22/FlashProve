-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Carry/FoldEndSums.lean: the kind "the code switch" (K2): WHAT A FOLD LEAVES
(`foldEndAt`, Johnson/Desc/K2/Honest/FoldEnd.lean), FIELD BY FIELD, MESSAGES AND TAILS, AS SUMS OVER
THE ROWS OF THE GROUP's TWO TABLES AND OF THE FRESH MASK, EACH ROW UNDER ITS WEIGHT AT THE FOLD's
POINT. Five definitions, six lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness,
soundness or hiding.

  `tabMain`, `tabMainTl`, `tabMask`, `tabMaskTl`, `tailIn`  DEFINITIONS: the functions that stand
      inside `foldEndAt` without a name: row ρ of the group's main table and of its mask table, as
      message and as tail; a main row's tail laid into the extension field
  **`foldEndAt_main_sum`**, `foldEndAt_mainTail_sum`  the folded main row: over the 2^k rows
  `foldEndAt_mask0_sum`, `foldEndAt_maskTail0_sum`  the fold of the group's mask rows: over 2^h
  `foldEndAt_mask1_sum`, `foldEndAt_maskTail1_sum`  the fold of the fresh mask's rows
How. `foldV` (Cb/Ld/LdRel.lean) is a sum over the cube by its text; `sum_range_cube`, `eqW_rowNo`
(OnBytes/Slice/SimBasic.lean) turn it into a sum over numbers.
Limits. Below the two codes' sizes; the main row at h ≤ k. The field `kept` is not spoken of. The
rows M, the fresh mask and the point γ are letters: nothing says whose they are.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K2.Honest.Carry.OfRows
import OnBytes.Slice.SimBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE codeOf eqW)
open Johnson.Prover.Send (Rows)

/-- Row ρ of the group's main table: its message. 0 at a row that nobody has sent. -/
def tabMain (L : GroupLayout) (ms : List GroupMember) (M : Nat → Rows) (ρ j : Nat) : GE :=
  match tableRow L.mainFirst (fun w => (shapeOf ms w).mainRows) ρ with
  | some (w, b) => (M w).main ((shapeOf ms w).mainDeg == 3) b j
  | none => zeroG

/-- A main row's tail, in the extension field. -/
def tailIn (R : Rows) (overE : Bool) (b q : Nat) : GE :=
  if overE then R.mainTlE b q else OnBytes.Slice.toE (OnBytes.Slice.ofF (R.mainTlF b q), 0, 0)

/-- Row ρ of the group's main table: its tail. -/
def tabMainTl (L : GroupLayout) (ms : List GroupMember) (M : Nat → Rows) (ρ q : Nat) : GE :=
  match tableRow L.mainFirst (fun w => (shapeOf ms w).mainRows) ρ with
  | some (w, b) => tailIn (M w) ((shapeOf ms w).mainDeg == 3) b q
  | none => zeroG

/-- Row ρ of the group's mask table: its message. -/
def tabMask (L : GroupLayout) (ms : List GroupMember) (M : Nat → Rows) (ρ j : Nat) : GE :=
  match tableRow L.maskFirst (fun w => (shapeOf ms w).maskRows) ρ with
  | some (w, b) => (M w).mask b j
  | none => zeroG

/-- Row ρ of the group's mask table: its tail. -/
def tabMaskTl (L : GroupLayout) (ms : List GroupMember) (M : Nat → Rows) (ρ q : Nat) : GE :=
  match tableRow L.maskFirst (fun w => (shapeOf ms w).maskRows) ρ with
  | some (w, b) => (M w).maskTl b q
  | none => zeroG

variable (L : GroupLayout) (codes : Codes) (code maskCode : Nat) (ms : List GroupMember)
  (M : Nat → Rows) (fresh : Rows) (γ : List GE)

/-- The folded main row's message. -/
theorem foldEndAt_main_sum (hh : L.h ≤ L.k) (j : Nat)
    (hj : j < (codeOf (codes.base.getD code default)).l) :
    (foldEndAt L codes code maskCode ms M fresh γ).main j =
      ∑ b ∈ Finset.range (2 ^ L.k), eqW L.k (fun i => γ.getD i zeroG) b * tabMain L ms M b j := by
  have hk : L.h + (L.k - L.h) = L.k := by omega
  have key : (foldEndAt L codes code maskCode ms M fresh γ).main j =
      ∑ b ∈ Finset.range (2 ^ (L.h + (L.k - L.h))),
        eqW (L.h + (L.k - L.h)) (fun i => γ.getD i zeroG) b * tabMain L ms M b j := by
    rw [OnBytes.Slice.sum_range_cube]
    unfold foldEndAt
    dsimp only
    split
    · exact Finset.sum_congr rfl fun β _ => by rw [OnBytes.Slice.eqW_rowNo]; rfl
    · rename_i h
      exact absurd hj h
  rw [hk] at key
  exact key

/-- The folded main row's tail. -/
theorem foldEndAt_mainTail_sum (hh : L.h ≤ L.k) (q : Nat)
    (hq : q < (codeOf (codes.base.getD code default)).r) :
    (foldEndAt L codes code maskCode ms M fresh γ).mainTail q =
      ∑ b ∈ Finset.range (2 ^ L.k),
        eqW L.k (fun i => γ.getD i zeroG) b * tabMainTl L ms M b q := by
  have hk : L.h + (L.k - L.h) = L.k := by omega
  have key : (foldEndAt L codes code maskCode ms M fresh γ).mainTail q =
      ∑ b ∈ Finset.range (2 ^ (L.h + (L.k - L.h))),
        eqW (L.h + (L.k - L.h)) (fun i => γ.getD i zeroG) b * tabMainTl L ms M b q := by
    rw [OnBytes.Slice.sum_range_cube]
    unfold foldEndAt
    dsimp only
    split
    · exact Finset.sum_congr rfl fun β _ => by rw [OnBytes.Slice.eqW_rowNo]; rfl
    · rename_i h
      exact absurd hq h
  rw [hk] at key
  exact key

/-- The fold of the group's mask rows: its message. -/
theorem foldEndAt_mask0_sum (j : Nat) (hj : j < (codeOf (codes.mask.getD maskCode default)).l) :
    (foldEndAt L codes code maskCode ms M fresh γ).mask 0 j =
      ∑ b ∈ Finset.range (2 ^ L.h), eqW L.h (fun i => γ.getD i zeroG) b * tabMask L ms M b j := by
  rw [OnBytes.Slice.sum_range_cube]
  unfold foldEndAt
  dsimp only
  split
  · exact Finset.sum_congr rfl fun β _ => by rw [OnBytes.Slice.eqW_rowNo]; rfl
  · rename_i h
    exact absurd hj h

/-- The fold of the group's mask rows: its tail. -/
theorem foldEndAt_maskTail0_sum (q : Nat)
    (hq : q < (codeOf (codes.mask.getD maskCode default)).r) :
    (foldEndAt L codes code maskCode ms M fresh γ).maskTail 0 q =
      ∑ b ∈ Finset.range (2 ^ L.h),
        eqW L.h (fun i => γ.getD i zeroG) b * tabMaskTl L ms M b q := by
  rw [OnBytes.Slice.sum_range_cube]
  unfold foldEndAt
  dsimp only
  split
  · exact Finset.sum_congr rfl fun β _ => by rw [OnBytes.Slice.eqW_rowNo]; rfl
  · rename_i h
    exact absurd hq h

/-- The fold of the fresh mask's rows: its message. -/
theorem foldEndAt_mask1_sum (j : Nat) (hj : j < (codeOf (codes.mask.getD maskCode default)).l) :
    (foldEndAt L codes code maskCode ms M fresh γ).mask 1 j =
      ∑ b ∈ Finset.range (2 ^ L.h), eqW L.h (fun i => γ.getD i zeroG) b * fresh.mask b j := by
  rw [OnBytes.Slice.sum_range_cube]
  unfold foldEndAt
  dsimp only
  split
  · exact Finset.sum_congr rfl fun β _ => by rw [OnBytes.Slice.eqW_rowNo]; rfl
  · rename_i h
    exact absurd hj h

/-- The fold of the fresh mask's rows: its tail. -/
theorem foldEndAt_maskTail1_sum (q : Nat)
    (hq : q < (codeOf (codes.mask.getD maskCode default)).r) :
    (foldEndAt L codes code maskCode ms M fresh γ).maskTail 1 q =
      ∑ b ∈ Finset.range (2 ^ L.h), eqW L.h (fun i => γ.getD i zeroG) b * fresh.maskTl b q := by
  rw [OnBytes.Slice.sum_range_cube]
  unfold foldEndAt
  dsimp only
  split
  · exact Finset.sum_congr rfl fun β _ => by rw [OnBytes.Slice.eqW_rowNo]; rfl
  · rename_i h
    exact absurd hq h

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.tabMain
#print axioms VerifiableInference.Desc.K2.Honest.tailIn
#print axioms VerifiableInference.Desc.K2.Honest.tabMainTl
#print axioms VerifiableInference.Desc.K2.Honest.tabMask
#print axioms VerifiableInference.Desc.K2.Honest.tabMaskTl
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_main_sum
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_mainTail_sum
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_mask0_sum
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_maskTail0_sum
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_mask1_sum
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt_maskTail1_sum
