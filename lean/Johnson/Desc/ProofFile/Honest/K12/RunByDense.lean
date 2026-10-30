-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByDense.lean: proof of `Spec.dense_reads` (RunBySpec.lean).
`denseAt row s` (Run.lean) expands a claim's row of coefficients into two arrays of words. If
h ≤ k and the main code's message length is a power of two, the arrays decode to the row's
coefficients (`vecG`) and have the sizes of the stage's two tables, 2 ^ k * C.l and 2 ^ h * Z.l.

  `denseBy_reads`   the proof of `Spec.dense_reads`
  `main_longer`   shows that the hypothesis on l is needed for the first size

By what. `Form.writeOut_val` (OnBytes/Iop/DotLaws.lean) gives the first branch of `denseAt`; the
second branch and the mask table are `Array.ofFn`, read entry by entry.

Limits.
- Not shown for h above k.
- The equation is about what the words decode to, at the indices of the stage's two tables. It does
  not say that the words are below the prime: on the main table they are what `Form.writeOut` or
  `Form.entry` returns, on the mask table they are the row's own.
- Nothing on the row's target, which `denseAt` passes on as its three words. Nothing on the forms
  that a row keeps beside its vector (`kept`): neither `denseAt` nor `vecG` reads them.
- Nothing follows on what a verifier decides.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunByTab
import OnBytes.Iop.DotLaws
import OnBytes.Slice.ProgCodes
import OnBytes.Slice.SimLink
import OnBytes.Slice.Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Form GroupRow ceilLog2 zeroE)
open OnBytes.Slice (GE toE vec vecIn vecG formAt readE readV rdE Sz rowNo_lt readV_eq_vec vec_ofFn
  ceilLog2_two_pow le_two_pow_ceilLog2)
open Fmt.M1 (Stage)
open VerifiableInference.Desc.K12 (dense)
open H2K.Pub (sgOf)

/-! ## 1 Numbers -/

/-- If l is a power of two, the 2 ^ (k + ceilLog2 l) entries written are the table's 2 ^ k * l. -/
theorem pow_vars (k l : ℕ) (hp : pow2B l = true) : 2 ^ (k + ceilLog2 l) = 2 ^ k * l := by
  obtain ⟨m, rfl⟩ : ∃ m, l = 2 ^ m := ⟨Fmt.M1.lg l, eq_of_beq hp⟩
  rw [ceilLog2_two_pow, pow_add]

/-- If l is not a power of two, more entries are written than the table has. -/
theorem main_longer (k l : ℕ) (hp : pow2B l = false) : 2 ^ k * l < 2 ^ (k + ceilLog2 l) := by
  have h1 : l ≤ 2 ^ ceilLog2 l := le_two_pow_ceilLog2 l
  have h2 : l ≠ 2 ^ ceilLog2 l := by
    intro h
    have h3 : pow2B l = true := by
      rw [h]
      unfold pow2B Fmt.M1.lg
      rw [Nat.log2_two_pow]
      exact beq_self_eq_true _
    rw [hp] at h3
    cases h3
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_of_le_of_ne h1 h2) (Nat.two_pow_pos k)

/-! ## 2 The vector on the main table -/

/-- `dense f n` decodes, entry by entry, to the form f, if every tensor of f has n variables. -/
theorem vec_dense (f : Form) (n i : ℕ) (hv : ∀ v ∈ f.tensors, v.vars = n) (hi : i < 2 ^ n) :
    vec (dense f n) i = formAt f i := by
  show vec ((f.writeOut n).map OnBytes.E.triple) i = _
  rw [← readV_eq_vec]
  exact (Form.writeOut_val rdE f n hv i hi).2

theorem all_vars (f : Form) (n : ℕ) (h : f.tensors.all (fun v => v.vars == n) = true) :
    ∀ v ∈ f.tensors, v.vars = n :=
  fun v hv => eq_of_beq (List.all_eq_true.1 h v hv)

theorem main_reads (f : Form) (n i : ℕ) (hi : i < 2 ^ n) :
    vec (if f.tensors.all (fun v => v.vars == n) then dense f n
      else Array.ofFn (n := 2 ^ n) fun i => (f.entry i.val).triple) i = formAt f i := by
  by_cases h : f.tensors.all (fun v => v.vars == n) = true
  · rw [if_pos h]
    exact vec_dense f n i (all_vars f n h) hi
  · rw [if_neg h, vec_ofFn, dif_pos hi]
    rfl

theorem main_size (f : Form) (n : ℕ) :
    (if f.tensors.all (fun v => v.vars == n) then dense f n
      else Array.ofFn (n := 2 ^ n) fun i => (f.entry i.val).triple).size = 2 ^ n := by
  by_cases h : f.tensors.all (fun v => v.vars == n) = true
  · rw [if_pos h]
    show ((f.writeOut n).map OnBytes.E.triple).size = _
    rw [Array.size_map]
    exact (Form.writeOut_val rdE f n (all_vars f n h) 0 (Nat.two_pow_pos n)).1
  · rw [if_neg h, Array.size_ofFn]

/-! ## 3 The vector on the mask table -/

/-- An array cut, or filled up with 0, to m entries decodes to the array's elements below m. -/
theorem mask_reads (d : Array OnBytes.E) (m i : ℕ) (hi : i < m) :
    vec (Array.ofFn (n := m) fun i => (d.getD i.val zeroE).triple) i = readV d i := by
  rw [vec_ofFn, dif_pos hi]
  rfl

/-! ## 4 The statement -/

theorem denseAt_c (row : GroupRow) (s : Stage) : (denseAt row s).c =
    if row.c.tensors.all (fun v => v.vars == s.k + ceilLog2 s.C.l)
      then dense row.c (s.k + ceilLog2 s.C.l)
      else Array.ofFn (n := 2 ^ (s.k + ceilLog2 s.C.l)) fun i => (row.c.entry i.val).triple := rfl

theorem denseAt_d (row : GroupRow) (s : Stage) : (denseAt row s).d =
    Array.ofFn (n := 2 ^ s.h * s.Z.l) fun i => (row.d.getD i.val zeroE).triple := rfl

theorem denseBy_reads : Spec.dense_reads := by
  intro row s hk hp
  have hn : 2 ^ (s.k + ceilLog2 s.C.l) = 2 ^ s.k * s.C.l := pow_vars s.k s.C.l hp
  have hg : (sgOf s).h + (sgOf s).g = s.k := sg_k hk
  refine ⟨funext fun j => ?_, ?_, ?_⟩
  · rcases j with ⟨b, c⟩ | ⟨b, c⟩
    · have hc : c.val < s.C.l := c.isLt
      show vec (denseAt row s).c (Sz.rowNo b + 2 ^ ((sgOf s).h + (sgOf s).g) * c.val) =
        formAt row.c (Sz.rowNo b + 2 ^ ((sgOf s).h + (sgOf s).g) * c.val)
      rw [denseAt_c]
      refine main_reads row.c _ _ ?_
      rw [hn, ← hg]
      exact tab_idx_lt _ _ _ _ (rowNo_lt b) hc
    · have hc : c.val < s.Z.l := c.isLt
      show vec (denseAt row s).d (Sz.rowNo b + 2 ^ s.h * c.val) =
        readV row.d (Sz.rowNo b + 2 ^ s.h * c.val)
      rw [denseAt_d]
      exact mask_reads row.d _ _ (tab_idx_lt _ _ _ _ (rowNo_lt b) hc)
  · rw [denseAt_c, main_size, hn]
  · rw [denseAt_d, Array.size_ofFn]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.pow_vars
#print axioms ProofFile.Honest.K12.Light.main_longer
#print axioms ProofFile.Honest.K12.Light.vec_dense
#print axioms ProofFile.Honest.K12.Light.all_vars
#print axioms ProofFile.Honest.K12.Light.main_reads
#print axioms ProofFile.Honest.K12.Light.main_size
#print axioms ProofFile.Honest.K12.Light.mask_reads
#print axioms ProofFile.Honest.K12.Light.denseAt_c
#print axioms ProofFile.Honest.K12.Light.denseAt_d
#print axioms ProofFile.Honest.K12.Light.denseBy_reads
