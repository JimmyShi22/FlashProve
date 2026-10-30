-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyHeldMeans.lean: at the full size: «THE KEY FILE's LOOKUPS ENFORCE InRange»: where an F-valued table says a matrix M over the extension field, our tables' sentence `InRange` (Johnson/Desc/Key/KeyWords.lean) at the two written lookups gives `Flat.InRange M`: M holds an index.
THE ROAD IS THE LIBRARY's OWN AND IS CALLED: `rangesOK_full` (Johnson/Top/H/KeyRangesThm.lean: the first lookup's runs reach every row; every pair of rows of the library's layout is read at a covered place of the second: by the kernel) · `covers_rows` (Johnson/Pack/KeyPort.lean) · `wfPairs_iff_inRange` (Johnson/Top/H/KeyMeaning.lean) · `inTab_byte_iff` | `inTab_pair_iff` (Blocks/RngPlan.lean) · `readE_add` | `readE_mul` | `readE_ofF` (OnBytes/Slice/ProgField.lean). WHAT IS ADDED: the program's key `keyAt` read in the field.
Main names.
  `rdF w`: a word, read in the extension field · `key0_read` | `key1_read`: a key of a lookup with the weights [1] | [1, 256], read.
  `bytes_of_range` | `pairs_of_range`: every entry is a signed byte; every two-byte weight is in range.
  `inRange_of_ranges`: THE THEOREM: `same` gives equal readings · mat says M · both sentences ⟹ `Flat.InRange M`.
OBJECT: `InRange` of our tables at `lk0Full` | `lk1Full`; `Flat.InRange` · USER: KeyHeldAtName.lean · LETTERS: same · mat · M.
Limits. THAT mat SAYS M IS A PREMISE. The two lookups are the written values; that they are the plan's in scope is not said here. It is said by three theorems together: in scope, where the description's tests on the plan say yes (planOk), the ranges of the description's source are the written key's (`LPFD.one_full`, KeyPublicAtSeat.lean, from `Johnson.RunOne.Law.KeyInScope.five_in_scope`, Johnson/RunOne/Law/KeyInScope.lean), and the written key's lookups are these two (`LPFD.looks_full`, KeyHeldAtName.lean). The reference numbers alone. Nothing on a protocol. Nothing on soundness.

-/
import Johnson.Desc.Key.KeyWords
import Johnson.Top.H.KeyMeaning
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFD
open OnBytes OnBytes.Slice
open OnBytes.Params (WfRun WfPart WfLookup)
open VerifiableInference.Desc.Key (keyAt InRange)
open Johnson.Pack (lk0Full lk1Full rangesOK_full covers_rows hasPl rowOf pairY cast_toF extE extE_in wfPairs_iff_inRange p_big pairY_lt)
open Blocks.Rng (WFPairs IsByte IsPair InTab inTab_byte_iff inTab_pair_iff)
open Inst.Model.Layout (kRef hRef)

/-- A word, read in the extension field. -/
noncomputable def rdF (w : OnBytes.F) : GE := readE (OnBytes.ofF w)

theorem rdF_nat (w : OnBytes.F) : rdF w = ((w.toNat : ℕ) : GE) := by
  unfold rdF
  rw [readE_ofF, cast_toF]

theorem rdF_of (v : ℕ) (h : v < 2 ^ 64) : rdF v.toUInt64 = (v : GE) := by
  rw [rdF_nat]
  have e : v.toUInt64.toNat = v := by
    show (UInt64.ofNat v).toNat = v
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]
  rw [e]

/-- A key of a lookup with one digit of weight 1, read. -/
theorem key0_read (l : WfLookup) (hw : l.digitWeight = [1]) (ho : l.offset.toNat = 128) (mat : ℕ → ℕ → OnBytes.F) (r : WfRun) (t c : ℕ) :
    readE (keyAt l mat r t c) = 128 + rdF (mat (r.firstRow + t) c) := by
  unfold keyAt
  rw [hw]
  show readE (addE (OnBytes.ofF l.offset) (mulE (OnBytes.ofF 1) (OnBytes.ofF (mat (r.firstRow + t + 0 * r.stride) c)))) = _
  rw [readE_add, readE_mul, Nat.zero_mul, Nat.add_zero]
  show rdF l.offset + rdF 1 * rdF (mat (r.firstRow + t) c) = _
  rw [rdF_nat l.offset, ho, rdF_nat 1]
  have h1 : (1 : OnBytes.F).toNat = 1 := rfl
  rw [h1]
  norm_num

/-- A key of a lookup with two digits of the weights 1 and 256, read. -/
theorem key1_read (l : WfLookup) (hw : l.digitWeight = [1, 256]) (ho : l.offset.toNat = 4096) (mat : ℕ → ℕ → OnBytes.F) (r : WfRun) (t c : ℕ) :
    readE (keyAt l mat r t c) = 4096 + rdF (mat (r.firstRow + t) c) + 256 * rdF (mat (r.firstRow + t + r.stride) c) := by
  unfold keyAt
  rw [hw]
  show readE (addE (addE (OnBytes.ofF l.offset) (mulE (OnBytes.ofF 1) (OnBytes.ofF (mat (r.firstRow + t + 0 * r.stride) c))))
    (mulE (OnBytes.ofF 256) (OnBytes.ofF (mat (r.firstRow + t + 1 * r.stride) c)))) = _
  rw [readE_add, readE_add, readE_mul, readE_mul, Nat.zero_mul, Nat.add_zero, Nat.one_mul]
  show rdF l.offset + rdF 1 * rdF (mat (r.firstRow + t) c) + rdF 256 * rdF (mat (r.firstRow + t + r.stride) c) = _
  rw [rdF_nat l.offset, ho, rdF_nat 1, rdF_nat 256]
  have h1 : (1 : OnBytes.F).toNat = 1 := rfl
  have h2 : (256 : OnBytes.F).toNat = 256 := rfl
  rw [h1, h2]
  norm_num

section
variable (same : OnBytes.E → OnBytes.E → Prop) (hsame : ∀ a b, same a b → readE a = readE b) (m : OnBytes.Wf.Matrix) (hk : m.kCol = kRef)
  (mat : ℕ → ℕ → OnBytes.F)
include hsame hk

/-- **Every entry is a signed byte.** -/
theorem bytes_of_range (h0 : InRange same m lk0Full mat) : ∀ y, y < hRef → ∀ c, c < 2 ^ kRef → IsByte (rdF (mat y c)) := by
  intro y hy c hc
  obtain ⟨hw, hcov⟩ := covers_rows ⟨18, hRef⟩ lk0Full rangesOK_full.cov₀
  obtain ⟨p, hp, r, hr, h1, h2⟩ := hcov y hy
  obtain ⟨v, hv, hs⟩ := h0 p hp r hr (y - r.firstRow) (by omega) c (by rw [hk]; exact hc)
  have e := hsame _ _ hs
  rw [key0_read lk0Full hw rangesOK_full.off₀, show r.firstRow + (y - r.firstRow) = y by omega] at e
  have hd : lk0Full.d = 8 := by decide +kernel
  rw [hd] at hv
  refine (inTab_byte_iff _).1 ⟨v, hv, ?_⟩
  rw [e]
  exact rdF_of v (by omega)

/-- **Every two-byte weight is in range.** -/
theorem pairs_of_range (h0 : InRange same m lk0Full mat) (h1 : InRange same m lk1Full mat) :
    ∀ q, q < 1527800 → ∀ c, c < 2 ^ kRef →
      IsPair (rdF (mat (Inst.Model.Layout.Bridge.y0 Inst.Model.ppref kRef q) c)) (rdF (mat (Inst.Model.Layout.Bridge.y1 Inst.Model.ppref kRef q) c)) := by
  intro q hq c hc
  obtain ⟨p, hp, r, hr, u, ⟨hu1, hu2⟩, hrow⟩ := rangesOK_full.P2 q hq
  have hw := rangesOK_full.w₁
  have r0 : Inst.Model.Layout.Bridge.y0 Inst.Model.ppref kRef q = r.firstRow + (u - r.firstPlace) := by
    have := hrow 0 (by rw [hw]; decide)
    simpa [pairY, rowOf] using this
  have r1 : Inst.Model.Layout.Bridge.y1 Inst.Model.ppref kRef q = r.firstRow + (u - r.firstPlace) + r.stride := by
    have := hrow 1 (by rw [hw]; decide)
    simpa [pairY, rowOf] using this
  obtain ⟨v, hv, hs⟩ := h1 p hp r hr (u - r.firstPlace) (by omega) c (by rw [hk]; exact hc)
  have e := hsame _ _ hs
  rw [key1_read lk1Full hw rangesOK_full.off₁, ← r1, ← r0] at e
  have hd : lk1Full.d = 13 := by decide +kernel
  rw [hd] at hv
  obtain ⟨l0, l1⟩ := pairY_lt q hq
  have b0 := bytes_of_range same hsame m hk mat h0 _ (by simpa [pairY] using l0) c hc
  have b1 := bytes_of_range same hsame m hk mat h0 _ (by simpa [pairY] using l1) c hc
  refine (inTab_pair_iff Cb.Gl.p p_big b0 b1).1 ⟨v, hv, ?_⟩
  rw [e]
  exact rdF_of v (by omega)

/-- **«THE KEY FILE's LOOKUPS ENFORCE InRange».** -/
theorem inRange_of_ranges (M : Fin hRef → Fin (2 ^ kRef) → GE) (hM : ∀ y c, M y c = rdF (mat y.val c.val))
    (h0 : InRange same m lk0Full mat) (h1 : InRange same m lk1Full mat) : VerifiableInference.OnPublicFiles.Flat.InRange M := by
  refine (wfPairs_iff_inRange M).1 ⟨fun y hy c hc => ?_, fun q hq c hc => ?_⟩
  · rw [extE_in M y c hy hc, hM]
    exact bytes_of_range same hsame m hk mat h0 y hy c hc
  · obtain ⟨l0, l1⟩ := pairY_lt q hq
    have l0' : Inst.Model.Layout.Bridge.y0 Inst.Model.ppref kRef q < hRef := by simpa [pairY] using l0
    have l1' : Inst.Model.Layout.Bridge.y1 Inst.Model.ppref kRef q < hRef := by simpa [pairY] using l1
    rw [extE_in M _ c l0' hc, extE_in M _ c l1' hc, hM, hM]
    exact pairs_of_range same hsame m hk mat h0 h1 q hq c hc

end

end LPFD

#print axioms LPFD.key0_read
#print axioms LPFD.key1_read
#print axioms LPFD.bytes_of_range
#print axioms LPFD.pairs_of_range
#print axioms LPFD.inRange_of_ranges
