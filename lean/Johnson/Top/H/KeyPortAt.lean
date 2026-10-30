-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/KeyPortAt.lean: what is asked of the two lookups of a key file, in the programs' own
order of places, and the offset and the coefficients of `keysGl` at a row and at a pair of rows.


Definitions, statements and proofs. Johnson/Top/H/KeyTemplate.lean has 24 forests in the library's
order of rows, which is not the programs'.
The two lookups are variables.


Main names:
  `ofPairs_live1`, `live2_of_eq`, `live0`, `live1`: the offset and the coefficients of `keysGl`
    (Cm/WfGlKeys.lean) at a row of the index matrix (128; 1 at that row) and at a pair of rows
    (4096; 1 and 256 at the two rows of the pair).
  `lkP`: the lookup of a forest: forest f < 12 is part f of the
    first lookup, forest 12 + j part j of the second.
  `pairY`, `RangesOK l₀ l₁`: what is asked of the two lookups: twelve parts each, of 2^18 and of
    2^17 places; the offsets 128 and 4096; the weights 1, 256 of the second; keys of padding in the
    tables; the verifier's own tests `Wf.runsOk` on every part and `Wf.coversAllRows` on the first
    lookup; the first lookup's runs inside the matrix; and (P1), (P2): the covered places of the
    second lookup read exactly the pairs of rows of the library's layout.






Limits: `RangesOK` is a hypothesis, and no lookups are given here. All its clauses but (P1) and (P2)
are tests on a few numbers and on the lists of runs. (P1) and (P2) tie the programs' runs to the
pairs of rows of the library's layout (Inst/Model/LayoutBridge.lean); they are shown of no record in
this file. Johnson/Top/H/KeyRangesThm.lean shows all clauses, with these two, of the two lookups at
full size as they are written out in Johnson/Top/H/KeyRangesFull.lean. A row number of the programs'
matrix is taken as the same row number of the library's index matrix; that the two hold the same
entries at the same rows is not said.

Nothing on multiplicities, on padding that a lookup does not count, or on knowledge soundness.
-/
import Johnson.Top.H.KeyTemplate
import Johnson.Pack.KeyPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Pack
open Inst.Model Inst.Model.All Iop Prob Hiop Cb Cb.Gl.Ref Cb.Gl.Bld Cb.Lkp Cm Cm.WfGl
open Blocks Blocks.Rng OnBytes.Slice
open Inst.Model.Layout (kRef hRef m2 units)
open OnBytes.Params (WfRun WfPart WfLookup)

/-! ### Live rows of keys -/

section Plan
variable {F : Type} [Field F] (h k D B lp m₂ : ℕ) (y0 y1 : ℕ → ℕ)

/-- A call of the first kind, at a row of the matrix. -/
theorem ofPairs_live1 (f i : ℕ) (hf : f < nCalls D k h) (hi : f * 2 ^ (D - k) + i < h) :
    (Plan.ofPairs F h k D B lp m₂ y0 y1).off f i = 128 ∧
      ∀ y, (Plan.ofPairs F h k D B lp m₂ y0 y1).Γ f i y =
        if y = f * 2 ^ (D - k) + i then 1 else 0 := by
  refine ⟨?_, fun y => ?_⟩
  · show (if f < nCalls D k h then (if f * 2 ^ (D - k) + i < h then (128 : F) else 0) else _) = _
    rw [if_pos hf, if_pos hi]
  · show (if f < nCalls D k h then (if f * 2 ^ (D - k) + i < h then
      (if y = f * 2 ^ (D - k) + i then (1 : F) else 0) else 0) else _) = _
    rw [if_pos hf, if_pos hi]

/-- The first call of the second kind, at a pair of rows; of any plan that is equal to such a
plan. -/
theorem live2_of_eq (P : Plan F) (hP : P = Plan.ofPairs F h k D B lp m₂ y0 y1) (f i : ℕ)
    (hn : nCalls D k h = f) (hi : i < m₂) :
    P.off f i = 4096 ∧
      ∀ y, P.Γ f i y = (if y = y0 i then 1 else 0) + (if y = y1 i then 256 else 0) := by
  subst hP
  have hf : ¬ f < nCalls D k h := by rw [hn]; exact Nat.lt_irrefl f
  have e : (f - nCalls D k h) * 2 ^ (D - k) + i = i := by
    rw [hn, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
  refine ⟨?_, fun y => ?_⟩
  · show (if f < nCalls D k h then _
      else (if (f - nCalls D k h) * 2 ^ (D - k) + i < m₂ then (4096 : F) else 0)) = _
    rw [if_neg hf, e, if_pos hi]
  · show (if f < nCalls D k h then _
      else (if (f - nCalls D k h) * 2 ^ (D - k) + i < m₂ then
        (if y = y0 ((f - nCalls D k h) * 2 ^ (D - k) + i) then (1 : F) else 0) +
          (if y = y1 ((f - nCalls D k h) * 2 ^ (D - k) + i) then 256 else 0)
        else 0)) = _
    rw [if_neg hf, e, if_pos hi]

end Plan

/-- At a row of the index matrix. -/
theorem live0 (v : ℕ) (h : v < hRef) :
    keysGl.off 0 v = 128 ∧ ∀ y, keysGl.coeff 0 v y = if y = v then 1 else 0 := by
  have g := ofPairs_live1 (F := Gl.F) hRef kRef 40 40 5 (m2 kRef (units ppref))
    (Layout.Bridge.y0 ppref kRef) (Layout.Bridge.y1 ppref kRef) 0 v
    (by rw [nCalls_ref]; exact Nat.one_pos) (by rw [Nat.zero_mul, Nat.zero_add]; exact h)
  rw [Nat.zero_mul, Nat.zero_add] at g
  exact g

/-- At a pair of rows. -/
theorem live1 (v : ℕ) (h : v < 1527800) :
    keysGl.off 1 v = 4096 ∧ ∀ y, keysGl.coeff 1 v y =
      (if y = Layout.Bridge.y0 ppref kRef v then 1 else 0) +
        (if y = Layout.Bridge.y1 ppref kRef v then 256 else 0) := by
  rw [keysGl_off, keysGl_coeff]
  exact live2_of_eq hRef kRef 40 40 5 1527800 (Layout.Bridge.y0 ppref kRef)
    (Layout.Bridge.y1 ppref kRef) planGl planGl_eq 1 v nCalls_ref h

theorem toF_lit (n : ℕ) (a : UInt64) (h : a.toNat = n) : toF a = ((n : ℕ) : GF) := by
  unfold toF
  rw [h]

/-! ### The value -/

section Val
variable (s : Scales) (l₀ l₁ : WfLookup)

/-- The lookup of a forest. -/
def lkP (f : ℕ) : WfLookup := if f < 12 then l₀ else l₁

/-- The rows of the matrix that a pair of the library's layout reads. -/
def pairY (v q : ℕ) : ℕ :=
  if q = 0 then Layout.Bridge.y0 ppref kRef v else Layout.Bridge.y1 ppref kRef v

/-- What is asked of the two lookups. All clauses but the last two are tests on a few numbers and on
the lists of runs. -/
structure RangesOK : Prop where
  n₀ : l₀.parts.length = 12
  n₁ : l₁.parts.length = 12
  lp₀ : ∀ j < 12, (partAt l₀ j).logPlaces = 18
  lp₁ : ∀ j < 12, (partAt l₁ j).logPlaces = 17
  off₀ : l₀.offset.toNat = 128
  off₁ : l₁.offset.toNat = 4096
  w₁ : l₁.digitWeight = [1, 256]
  pad₀ : l₀.paddingKey.toNat < 2 ^ 8
  pad₁ : l₁.paddingKey.toNat < 2 ^ 13
  runs₀ : ∀ p ∈ l₀.parts, OnBytes.Wf.runsOk p.logPlaces 0 p.runs = true
  runs₁ : ∀ p ∈ l₁.parts, OnBytes.Wf.runsOk p.logPlaces 0 p.runs = true
  fit₀ : ∀ p ∈ l₀.parts, ∀ r ∈ p.runs, r.firstRow + r.places ≤ hRef
  cov₀ : OnBytes.Wf.coversAllRows ⟨18, hRef⟩ l₀ = true
  /-- every covered place of the second lookup reads a pair of rows of the library's layout -/
  P1 : ∀ p ∈ l₁.parts, ∀ ρ ∈ p.runs, ∀ u, hasPl ρ u →
    ∃ v < 1527800, ∀ q < l₁.digitWeight.length, pairY v q = rowOf ρ u q
  /-- every pair of rows of the library's layout is read at a covered place of the second lookup -/
  P2 : ∀ v < 1527800, ∃ p ∈ l₁.parts, ∃ ρ ∈ p.runs, ∃ u, hasPl ρ u ∧
    ∀ q < l₁.digitWeight.length, pairY v q = rowOf ρ u q

variable {l₀ l₁}

end Val

end Johnson.Pack

#print axioms Johnson.Pack.live0
#print axioms Johnson.Pack.live1
