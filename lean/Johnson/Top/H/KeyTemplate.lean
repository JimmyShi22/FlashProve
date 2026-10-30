-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/KeyTemplate.lean: the rows of keys of `keysGl` beyond the last row or pair of rows,
and the letters of 24 forests.

Definitions, statements and proofs. The library's keys of weights-formedness (`keysGl`) stand in
two forests of 2^22 rows of keys: one key map
for all 3,076,096 rows of the index matrix, one for all 1,527,800 pairs of rows
(Cm/WfGlKeys.lean). A row of keys beyond the last row or pair has the offset 0 and no coefficient.
Here each forest is cut in blocks of rows, and the first twelve blocks are kept: 12 blocks of 2^18
rows of the first (3,145,728 rows), 12 blocks of 2^17 rows of the second (1,572,864). What is left
out is idle.
Main names:
  `ofPairs_idle1`, `ofPairs_idle2`, `idle2_of_eq`: of the plan with keys of two kinds
    (`Plan.ofPairs`, Blocks/RngPlan.lean): beyond the last row, or the last pair of rows, the offset
    is 0 and there is no coefficient.
  `keysGl_off`, `keysGl_coeff`, `planGl_eq`, `idle0`, `idle1`: the same of `keysGl`: from row
    3,076,096 on at the first table, from pair 1,527,800 on at the second.


  `lkI`, `ptI`, `rvK`, `dK`: of which forest a part is, which block of it, its row variables, the
    variables of its table: forest f < 12 is block f of the first forest, forest 12 + j is block j
    of the second.





  `row_ge`: the row of keys of a key of block j is at least the block's first row.




Limits: THE ORDER OF THE ROWS OF KEYS IS THE LIBRARY'S, NOT THE PROGRAMS'. In the programs a part is
what the public runs of rows of the key file say. An evaluation of the public record of the example
at full size shows: at the first lookup the last part has the same number of live places as block 11
here, at other places (two halves of 2^17 places, each with its 96,256 live places first, against
one run of 192,512 here); at the second lookup the padding stands at the same places; the rows
themselves were not compared at either. So the blocks here are not the parts of the programs'
lookups. Johnson/Pack/KeyRuns.lean has the lemma by which keys in another
order describe the same set.

Nothing on knowledge soundness.

-/
import Cb.GlVal.GlThird
import Cb.Obj.LdObjectConfMore
import Cb.Gl.GlSenders
import Cb.Gl.GlField
import Alg.Mle
import Mathlib.Tactic.Ring
import Cm.TargetPLangs
import Cm.WfGlKeys
import Cm.TargetPLangsProofs
import Cm.IndexRefProofs
import Cb.Gen.WfKeys
import Cb.Gen.LkpAlg
import Cb.Ld.LdLkpMultProofs
import Cb.Obj.LdObjectConfProofs
import Cm.WfGlCount
import Cb.Ld.LdBldPlan
import Cb.Ld.LdBldFoldProofs
import Cb.GlVal.GlJohn
import Cb.Ld.LdBldCode
import Cb.Gen.JohnsonList
import Cb.Ld.LdBldCodeProofs
import Cb.Ld.LdGroupStd
import Cb.Ld.LdKappaTowN
import Cb.Ref.GlRefNum
import Cb.Ld.LdKappaWorkRef
import Cb.Ld.LdKappaList
import Cb.Gl.GlObjMix
import Cb.Ld.LdBldMsgProofs
import Cb.Ld.LdBatShapeProofs
import Cb.Ref.GlRefCodeSplit
import Cb.Gl.GlFinalEvProofs
import Cb.Obj.LdObjectCtb
import Cb.Gen.JohnsonListProofs
import Cb.Ld.LdBldSwOrd
import Cb.Ld.LdBldSwOrdProofs
import Cb.Ld.LdBldCodeGrpProofs
import Cb.Ref.GlRefNumMca
import Cb.Ld.LdLinkClose
import Cb.Ld.LdBldObjProofs
import Cb.Gl.GlFinalPpP
import Cb.Ld.LdBldWfTwo
import Mathlib.Algebra.BigOperators.Fin
import Cb.Ld.LdBldSwBridge
import Cb.Ld.LdBldWfTwoProofs
import Cb.Ld.LdBldWfProofs
import Cb.Ld.LdWfFull
import Cb.Ld.LdBldWfWith
import Cb.Ld.LdBldSwShape
import Cb.Ld.LdKappaW
import Cb.Gl.GlLdJAt
import Johnson.Pack.KeyHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Pack
open Inst.Model Inst.Model.All Iop Prob Hiop Cb Cb.Gl.Ref Cb.Gl.Bld Cb.Lkp Cm Cm.WfGl
open Blocks Blocks.Rng
open Inst.Model.Layout (kRef hRef m2 units)

/-! ### Idle rows of keys -/

section Plan
variable {F : Type} [Field F] (h k D B lp m₂ : ℕ) (y0 y1 : ℕ → ℕ)

/-- A call of the first kind: beyond the last row the offset is 0 and there is no coefficient. -/
theorem ofPairs_idle1 (f i : ℕ) (hf : f < nCalls D k h) (hi : ¬ f * 2 ^ (D - k) + i < h) :
    (Plan.ofPairs F h k D B lp m₂ y0 y1).off f i = 0 ∧
      ∀ y, (Plan.ofPairs F h k D B lp m₂ y0 y1).Γ f i y = 0 := by
  refine ⟨?_, fun y => ?_⟩
  · show (if f < nCalls D k h then (if f * 2 ^ (D - k) + i < h then (128 : F) else 0) else _) = 0
    rw [if_pos hf, if_neg hi]
  · show (if f < nCalls D k h then (if f * 2 ^ (D - k) + i < h then _ else (0 : F)) else _) = 0
    rw [if_pos hf, if_neg hi]

/-- A call of the second kind: beyond the last pair of rows the same. -/
theorem ofPairs_idle2 (f i : ℕ) (hf : ¬ f < nCalls D k h)
    (hi : ¬ (f - nCalls D k h) * 2 ^ (D - k) + i < m₂) :
    (Plan.ofPairs F h k D B lp m₂ y0 y1).off f i = 0 ∧
      ∀ y, (Plan.ofPairs F h k D B lp m₂ y0 y1).Γ f i y = 0 := by
  refine ⟨?_, fun y => ?_⟩
  · show (if f < nCalls D k h then _
      else (if (f - nCalls D k h) * 2 ^ (D - k) + i < m₂ then (4096 : F) else 0)) = 0
    rw [if_neg hf, if_neg hi]
  · show (if f < nCalls D k h then _
      else (if (f - nCalls D k h) * 2 ^ (D - k) + i < m₂ then _ else (0 : F))) = 0
    rw [if_neg hf, if_neg hi]

/-- The same, for the first call of the second kind, beyond the last pair. -/
theorem ofPairs_idle2' (f i : ℕ) (hn : nCalls D k h = f) (hi : m₂ ≤ i) :
    (Plan.ofPairs F h k D B lp m₂ y0 y1).off f i = 0 ∧
      ∀ y, (Plan.ofPairs F h k D B lp m₂ y0 y1).Γ f i y = 0 :=
  ofPairs_idle2 h k D B lp m₂ y0 y1 f i (by rw [hn]; exact Nat.lt_irrefl f)
    (by rw [hn, Nat.sub_self, Nat.zero_mul, Nat.zero_add]; exact Nat.not_lt.2 hi)

/-- The same of any plan that is equal to such a plan. -/
theorem idle2_of_eq (P : Plan F) (hP : P = Plan.ofPairs F h k D B lp m₂ y0 y1) (f i : ℕ)
    (hn : nCalls D k h = f) (hi : m₂ ≤ i) : P.off f i = 0 ∧ ∀ y, P.Γ f i y = 0 := by
  subst hP
  exact ofPairs_idle2' h k D B lp m₂ y0 y1 f i hn hi

end Plan

theorem nCalls_ref : nCalls 40 kRef hRef = 1 := nCallsGl_h

/-- Beyond the last row of the index matrix. -/
theorem idle0 (u : ℕ) (h : hRef ≤ u) : keysGl.off 0 u = 0 ∧ ∀ y, keysGl.coeff 0 u y = 0 :=
  ofPairs_idle1 (F := Gl.F) hRef kRef 40 40 5 (m2 kRef (units ppref)) (Layout.Bridge.y0 ppref kRef)
    (Layout.Bridge.y1 ppref kRef) 0 u (by rw [nCalls_ref]; exact Nat.one_pos)
    (by rw [Nat.zero_mul, Nat.zero_add]; exact Nat.not_lt.2 h)

/-- The plan, with the number of pairs of rows as a numeral. -/
theorem planGl_eq : planGl = Plan.ofPairs Gl.F hRef kRef 40 40 5 1527800
    (Layout.Bridge.y0 ppref kRef) (Layout.Bridge.y1 ppref kRef) := by
  unfold planGl
  rw [Layout.Sanity.plan_numbers.1]

/-- The keys' offsets and coefficients are the plan's. (Stated of the functions: applied at the
second table, a check by evaluation would unfold the count of the pairs of rows.) -/
theorem keysGl_off : keysGl.off = planGl.off := rfl
theorem keysGl_coeff : keysGl.coeff = planGl.Γ := rfl

/-- Beyond the last pair of rows. -/
theorem idle1 (u : ℕ) (h : 1527800 ≤ u) : keysGl.off 1 u = 0 ∧ ∀ y, keysGl.coeff 1 u y = 0 := by
  rw [keysGl_off, keysGl_coeff]
  exact idle2_of_eq hRef kRef 40 40 5 1527800 (Layout.Bridge.y0 ppref kRef)
    (Layout.Bridge.y1 ppref kRef) planGl planGl_eq 1 u nCalls_ref h

/-! ### The value -/

section Val
variable (s : Scales)

/-- Of which of the library's two forests a part is; which block of it; its row variables; the
variables of its table. -/
def lkI (f : ℕ) : ℕ := if f < 12 then 0 else 1
def ptI (f : ℕ) : ℕ := if f < 12 then f else f - 12
def rvK (f : ℕ) : ℕ := if f < 12 then 18 else 17
def dK (f : ℕ) : ℕ := if f < 12 then 8 else 13

/-- The row of keys of a key of block j is at least the block's first row. -/
theorem row_ge (k r j b : ℕ) : j * 2 ^ r ≤ (j * 2 ^ (r + k) + b) / 2 ^ k := by
  have hp : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
  rw [pow_add, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hp]
  exact Nat.le_add_left _ _

end Val

end Johnson.Pack

#print axioms Johnson.Pack.idle0
#print axioms Johnson.Pack.idle1
