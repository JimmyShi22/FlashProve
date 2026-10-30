-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsSmp.lean: the sample of the code switch, in the library and in the format.

OnBytes/Slice/CsData.lean sets up the library's code switch at the sizes of two neighbouring stages
of the written proximity test. Its sample map is the sample row with a pad of one entry, under the
names of a new message's coordinates. This file shows two things of that map.

Main definition: `tabAt`, a row on the new tables, read at an index of either table.
Main theorems.
 `vecIn_eq`     the coefficients of a row on a group, through `tabAt`
 `smp_mat`      the library's sample at an entry is the format's sample row at that entry's index
 `csSample_ok`  a vector other than 0 has the answer 0 at no more seeds than the sample's count
                `err`: what the library's statement on the code switch asks of the sample

Not claimed. Nothing on the size of the count `err`. Nothing is said of hiding.
-/
import OnBytes.Slice.CsData
import OnBytes.Slice.SimSample

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

variable {s s' : Sg}

/-- A row on the new tables, read at an index of the main table (left) or of the mask table. -/
def tabAt (G : Fmt.M1.GRow) : ℕ ⊕ ℕ → GE := Sum.elim (vec G.c) (vec G.d)

/-- The coefficients of a row on a group are the row's entries at the indices of the tables. -/
theorem vecIn_eq (s' : Sg) (G : Fmt.M1.GRow) (j : s'.cIn.J) :
    vecIn s' G j = tabAt G (outAt s' j) := by
  rcases j with x | x <;> rfl

/-! ## Sizes -/

/-- The new main table has 2^Am entries. -/
private theorem two_pow_Am (hf : CsFit s s') : 2 ^ s'.st.Am = 2 ^ (s'.h + s'.g) * s'.C.l := by
  show 2 ^ (s'.h + s'.g + Fmt.M1.lg s'.C.l) = _
  rw [pow_add, ← hf.powC]

/-- The new mask table has 2^Az entries. -/
private theorem two_pow_Az (hf : CsFit s s') : 2 ^ s'.st.Az = 2 ^ s'.h * s'.Z.l := by
  show 2 ^ (s'.h + Fmt.M1.lg s'.Z.l) = _
  rw [pow_add, ← hf.powZ]

/-- An index of the main table is below half the cube. -/
private theorem main_lt (hf : CsFit s s') (x : (Fin (s'.h + s'.g) → Bool) × Fin s'.C.l) :
    idxOf x < 2 ^ max s'.st.Am s'.st.Az := by
  have h1 := idxOf_lt x
  rw [← two_pow_Am hf] at h1
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

/-- An index of the mask table is below half the cube. -/
private theorem mask_lt (hf : CsFit s s') (x : (Fin s'.h → Bool) × Fin s'.Z.l) :
    idxOf x < 2 ^ max s'.st.Am s'.st.Az := by
  have h1 := idxOf_lt x
  rw [← two_pow_Az hf] at h1
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

/-- The vertex of an entry of the mask table. -/
private theorem cubeAt_inr (x : (Fin s'.h → Bool) × Fin s'.Z.l) :
    cubeAt s' (.inr x) = 2 ^ max s'.st.Am s'.st.Az + idxOf x := rfl

/-- Every vertex lies on the cube of the sample's point. -/
private theorem cubeAt_lt (hf : CsFit s s') (j : s'.cIn.J) : cubeAt s' j < 2 ^ s'.st.na := by
  show _ < 2 ^ (max s'.st.Am s'.st.Az + 1)
  rw [pow_succ]
  rcases j with x | x
  · have := main_lt hf x
    show idxOf x < _
    omega
  · have := mask_lt hf x
    rw [cubeAt_inr]
    omega

/-- Different entries have different vertices. -/
private theorem cubeAt_inj (hf : CsFit s s') : Function.Injective (cubeAt s') := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (idxOf_inj h)
  · have := main_lt hf x
    rw [cubeAt_inr] at h
    have h' : idxOf x = 2 ^ max s'.st.Am s'.st.Az + idxOf y := h
    omega
  · have := main_lt hf y
    rw [cubeAt_inr] at h
    have h' : 2 ^ max s'.st.Am s'.st.Az + idxOf x = idxOf y := h
    omega
  · rw [cubeAt_inr, cubeAt_inr] at h
    exact congrArg Sum.inr (idxOf_inj (Nat.add_left_cancel h))

/-! ## The two theorems on the sample -/

/-- The library's sample at an entry is the format's sample row there. -/
theorem smp_mat (hf : CsFit s s') (z : List Fmt.M1.E) (beta alpha : Fmt.M1.E)
    (hz : z.length = s'.st.na) (β : GEˣ) (hβ : β.val = toE beta) (n : CsK s ⊕ CsFree hf) :
    (csSample hf).mat (ptL _ z, β) () n
      = tabAt (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az z beta alpha) (outAt s' (csPlace hf n)) := by
  have hna : s'.st.na = max s'.st.Am s'.st.Az + 1 := rfl
  have hzA : s'.st.Am ≤ z.length := by
    have := le_max_left s'.st.Am s'.st.Az
    omega
  have hzZ : s'.st.Az ≤ z.length := by
    have := le_max_right s'.st.Am s'.st.Az
    omega
  show (padRow s'.st.na fun j : {j : s'.cIn.J // j ≠ csPad hf} => cubeAt s' j.1).mat
    (fun t => lst z t.val, β) () (splitAt (csPad hf) (csPlace hf n)) = _
  generalize csPlace hf n = j
  by_cases h : j = csPad hf
  · rw [h, splitAt_self]
    show _ = vec (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az z beta alpha).d
      (idxOf (cell _ _ (2 ^ s'.h * s'.Z.l - 1) _))
    rw [idxOf_cell, ← two_pow_Az hf]
    exact (sampleRow_d_pad _ _ z beta alpha β _ hzZ hβ.symm).symm
  · rw [splitAt_ne h]
    rcases j with x | x
    · have hlt : idxOf x < 2 ^ s'.st.Am := by
        rw [two_pow_Am hf]
        exact idxOf_lt x
      exact (sampleRow_c_entry s'.st.Am s'.st.Az z beta alpha β
        (fun j : {j : s'.cIn.J // j ≠ csPad hf} => cubeAt s' j.1) ⟨.inl x, h⟩ hzA hlt).symm
    · have hne : idxOf x ≠ 2 ^ s'.h * s'.Z.l - 1 := fun e =>
        h (congrArg Sum.inr (idxOf_inj (e.trans (idxOf_cell _ _ _ _).symm)))
      have hi : idxOf x + 1 < 2 ^ s'.st.Az := by
        have := idxOf_lt x
        rw [two_pow_Az hf]
        omega
      exact (sampleRow_d_entry s'.st.Am s'.st.Az z beta alpha β
        (fun j : {j : s'.cIn.J // j ≠ csPad hf} => cubeAt s' j.1) ⟨.inr x, h⟩ (idxOf x) hzZ hi
        rfl).symm

/-- The sample of the code switch tells vectors apart: a vector other than 0 has the answer 0 at no
more seeds than the sample's own count `err` allows. -/
theorem csSample_ok (hf : CsFit s s') : (csSw hf).Zo.OK :=
  @ok_reix _ _ _ _ _ _ _ _ (ok_pad_one s'.st.na (fun j : {j : s'.cIn.J // j ≠ csPad hf} =>
    cubeAt s' j.1) (fun j => cubeAt_lt hf j.1)
    fun _ _ h => Subtype.ext (cubeAt_inj hf h))

end OnBytes.Slice

#print axioms OnBytes.Slice.vecIn_eq
#print axioms OnBytes.Slice.smp_mat
#print axioms OnBytes.Slice.csSample_ok
