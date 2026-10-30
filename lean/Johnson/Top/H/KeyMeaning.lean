-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/KeyMeaning.lean: every entry of the committed matrix is a signed byte and every
two-byte weight is in range if and only if the matrix holds an index.

Definitions, statements and proofs. Two readings of "the matrix is in range" stand in this library.
Johnson/Flat/LedgerClaim.lean has `Flat.InRange M`: M holds a well-formed matrix of digits; what a
proof means is proved at it. Johnson/Top/H/KeyAny.lean has `PartsIn`: the keys of all parts of the
key file's two lookups, made from the public runs of rows, lie in their tables; the laws of the key
file's record are proved at it. That at the two lookups at full size the two are the same statement
is not shown here.
Main names:
  `units_fit`, `pairY_lt`, `sum_pick`: the units fit into the matrix; both rows of a pair are rows
    of the matrix; a sum that picks one row.



  `cubeOf M`, `cubeOf_bits`, `extE`, `extE_in`: a matrix of 3,076,096 rows and 2^18 columns on the
    cube of the column variables (column number c at the vertex `Alg.bits kRef c`: the top bit
    first), and as a function on all pairs of numbers.


  `wfw_cut`, `wfPairs_iff_inRange`: every entry is a signed byte and every two-byte weight is in
    range (`WFPairs`, Blocks/RngPlan.lean) if and only if the matrix holds an index (by
    `wfPairs_iff`, Inst/Model/LayoutBridge.lean, at the extension field).


  `inRange_zero`, `not_inRange_200`: two controls: the matrix 0 holds an index; a matrix with a cell
    200 holds none. So neither side is always true or always false.






Limits: both sides speak of one matrix M. That row y
and column c of M are row y and column c of the matrix that the programs commit to is a matter of
the reading of a stored table, and is not said here.
`cubeOf` labels the cube with the top bit first, as `KeysD.T`
does.


Nothing on multiplicities or on knowledge soundness.
-/
import Johnson.Top.H.KeyAny
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Pack
open Inst.Model Inst.Model.All Cb Cb.Lkp Cm Cm.WfGl OnBytes.Slice Blocks Blocks.Rng
open Inst.Model.Layout (kRef hRef m2 units)

/-- The units fit into the matrix. -/
theorem units_fit : Layout.off kRef (units ppref) (units ppref).length ≤ hRef := by
  rw [Layout.Sanity.units_total.1, Layout.Sanity.units_total.2]; decide

/-- Both rows of a pair are rows of the matrix. -/
theorem pairY_lt (q : ℕ) (hq : q < 1527800) : pairY q 0 < hRef ∧ pairY q 1 < hRef :=
  Layout.Bridge.pair_lt ppref kRef hRef units_fit q
    (by rw [Layout.Sanity.plan_numbers.1]; exact hq)

theorem sum_pick {h : ℕ} (v : ℕ) (hv : v < h) (a : GE) (g : Fin h → GE) :
    ∑ r : Fin h, (if r.val = v then a else 0) * g r = a * g ⟨v, hv⟩ := by
  rw [Fintype.sum_eq_single ⟨v, hv⟩]
  · rw [if_pos rfl]
  · intro r hr
    rw [if_neg fun e => hr (Fin.ext e), zero_mul]

/-! ### From the cube to the matrix of rows and columns -/

section Mat
variable (M : Fin hRef → Fin (2 ^ kRef) → GE)

/-- The matrix on the cube of the column variables: column number c stands at the vertex
`Alg.bits kRef c` (the top bit first). -/
def cubeOf : Fin hRef × (Fin kRef → Bool) → GE := fun rc => M rc.1 ⟨Alg.num rc.2, Alg.num_lt rc.2⟩

theorem cubeOf_bits (y : Fin hRef) (c : ℕ) (hc : c < 2 ^ kRef) :
    cubeOf M (y, Alg.bits kRef c) = M y ⟨c, hc⟩ := by
  unfold cubeOf
  congr 1
  exact Fin.ext (Alg.num_bits hc)

/-- The matrix as a function on all pairs of numbers: 0 outside the shape. -/
def extE : ℕ → ℕ → GE := fun y c =>
  if h : y < hRef ∧ c < 2 ^ kRef then M ⟨y, h.1⟩ ⟨c, h.2⟩ else 0

theorem extE_in (y c : ℕ) (hy : y < hRef) (hc : c < 2 ^ kRef) : extE M y c = M ⟨y, hy⟩ ⟨c, hc⟩ :=
  dif_pos ⟨hy, hc⟩

theorem p_big : 2 ^ 17 < Gl.p := by decide +kernel

/-- An integer matrix cut to the shape and extended by 0 is well formed if the matrix is. -/
theorem wfw_cut (W : Mat) (h : Layout.WFW ppref kRef W hRef) :
    Layout.WFW ppref kRef (Cm.ext (Cm.cut W)) hRef := by
  have e : ∀ y, y < hRef → ∀ c, c < 2 ^ kRef → Cm.ext (Cm.cut W) y c = W y c := by
    intro y hy c hc
    unfold Cm.ext Cm.cut
    rw [dif_pos ⟨hy, hc⟩]
  obtain ⟨hb, hp⟩ := (Layout.Bridge.wfw_iff_pairs W).1 h
  refine (Layout.Bridge.wfw_iff_pairs _).2 ⟨fun y hy c hc => ?_, fun q hq c hc => ?_⟩
  · rw [e y hy c hc]
    exact hb y hy c hc
  · obtain ⟨l0, l1⟩ := Layout.Bridge.pair_lt ppref kRef hRef units_fit q hq
    rw [e _ l0 c hc, e _ l1 c hc]
    exact hp q hq c hc

/-- The matrix is well formed in the sense of Blocks/RngPlan.lean if and only if it holds an
index. -/
theorem wfPairs_iff_inRange :
    WFPairs hRef kRef 1527800 (Layout.Bridge.y0 ppref kRef) (Layout.Bridge.y1 ppref kRef)
        (extE M) ↔ VerifiableInference.OnPublicFiles.Flat.InRange M := by
  have g := Layout.Bridge.wfPairs_iff (P := ppref) (k := kRef) (h := hRef) Gl.p p_big units_fit
    (extE M)
  rw [Layout.Sanity.plan_numbers.1] at g
  rw [g]
  constructor
  · rintro ⟨W, hW, ha⟩
    refine ⟨⟨Cm.cut W, wfw_cut W hW⟩, fun y c => ?_, fun y c hn => ?_⟩
    · have := ha y.val y.isLt c.val c.isLt
      rw [extE_in M _ _ y.isLt c.isLt] at this
      show M y c = ((Cm.ext (Cm.cut W) y.val c.val : ℤ) : GE)
      unfold Cm.ext Cm.cut
      rw [dif_pos ⟨y.isLt, c.isLt⟩]
      exact this
    · show Cm.ext (Cm.cut W) y c = 0
      unfold Cm.ext
      rw [dif_neg hn]
  · rintro ⟨i, hs, _⟩
    refine ⟨i.mat, i.wf, fun y hy c hc => ?_⟩
    rw [extE_in M y c hy hc]
    exact hs ⟨y, hy⟩ ⟨c, hc⟩

end Mat

/-! ### Two controls: neither side is always true or always false -/

/-- The matrix 0 holds an index. -/
theorem inRange_zero :
    VerifiableInference.OnPublicFiles.Flat.InRange
      (fun (_ : Fin hRef) (_ : Fin (2 ^ kRef)) => (0 : GE)) := by
  refine (wfPairs_iff_inRange _).1 ?_
  have e : ∀ y c, extE (fun _ _ => (0 : GE)) y c = 0 := by
    intro y c
    unfold extE
    split <;> rfl
  refine ⟨fun y _ c _ => ?_, fun q _ c _ => ?_⟩
  · rw [e]
    exact ⟨0, by norm_num, by norm_num, by simp⟩
  · rw [e, e]
    exact ⟨0, 0, ⟨by norm_num, by norm_num, by simp⟩, ⟨by norm_num, by norm_num, by simp⟩,
      by norm_num, by norm_num⟩

/-- A matrix with a cell 200 holds none. -/
theorem not_inRange_200 (M : Fin hRef → Fin (2 ^ kRef) → GE) (y : Fin hRef) (c : Fin (2 ^ kRef))
    (h : M y c = 200) : ¬ VerifiableInference.OnPublicFiles.Flat.InRange M := by
  rintro ⟨i, hs, _⟩
  have hw := i.wf.1 y.val y.isLt c.val c.isLt
  have e : ((i.mat y.val c.val : ℤ) : GE) = ((200 : ℤ) : GE) := by
    rw [← hs y c, h]
    norm_num
  have h1 : (Gl.p : ℤ) ∣ 200 - i.mat y.val c.val := ((CharP.intCast_eq_intCast GE Gl.p).1 e).dvd
  have hp : (1000 : ℤ) < (Gl.p : ℤ) := by
    have e' : Gl.p = 18446744069414584321 := Code.pGold_eq
    rw [e']
    norm_num
  have h2 : |200 - i.mat y.val c.val| < (Gl.p : ℤ) := by
    refine lt_trans ?_ hp
    rw [abs_lt]
    constructor <;> omega
  have h3 := Int.eq_zero_of_abs_lt_dvd h1 h2
  omega

/-! ### The record's laws where "holds an index" is read off the matrix of rows and columns -/

end Johnson.Pack

#print axioms Johnson.Pack.inRange_zero
#print axioms Johnson.Pack.not_inRange_200
