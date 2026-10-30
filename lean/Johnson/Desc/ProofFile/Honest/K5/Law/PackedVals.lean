-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/PackedVals.lean: WHAT THE VALUES OF THE ARRAYS "M mu" ARE, IN
THE EXTENSION FIELD: the value that `cellsVals` (Johnson/Desc/ProofFile/Honest/K1/FirstData.lean)
has for element (i', c) of an array is the packing at the radix 2 ^ 20 (`Alg.pack`, Alg/Range.lean)
of the images of the reader's cells of column c. CONDITIONAL: the array's name is read as a number;
that number names a matrix of the segment; the column lies inside its shape. Lemmas, at all sizes
and all readers. Nothing is said of what the cells are.

What it is for. The frame fills a first sending's main rows with `cellsVals`' values; the verifier's
side reads a cell as "the small integer column whose packing the symbols are". Whoever sets the two
side by side needs the frame's value in the form of a packing over the extension field.

Main names:
  `pack3_map`: a ring map goes through `pack3` (Johnson/HonestTrace/Packed.lean). No premise.
  `toE_base`, `val_eOfF`, `asE_inl`: an element of the base field, read into the extension field by
    the programs' element (`eOfF`, then `Reading.gl.val`) or by the frame's reading of an entry
    (`asE`), is its image under `algebraMap`. No premise.
  `labelNo_arrayLabel`: the frame's reader of names (`labelNo`, FirstData.lean) reads "M mu" as mu,
    at every mu below 26.
  `cellsVals_pack`: **the value as a packing.**
  `cellsVals_size`: the size that `cellsVals` says of an array: the matrix's packed shape.
    Conditional: the name; the matrix; it has an array of its own segment.

How. `pack3_eq_pack` (Packed.lean): `pack3` is `Alg.pack` at 2 ^ 20; `toE_ofF`, `toF_ofF`
(OnBytes/Slice/Field.lean); `E.triple_ofTriple` (OnBytes/Base.lean). Kin: `pack3_cast`
(Packed.lean): the like of `pack3_map` for the integers' cast.

Limits. hn, that `labelNo` reads the name as the number, is a premise of `cellsVals_pack` and
`cellsVals_size`, which stand at all sizes; `labelNo_arrayLabel` pays it at the names "M mu" with mu
below 26 alone: a law at all mu is not shown. `labelNo_arrayLabel` RESTS ON ONE CLOSED FACT THAT
LEAN's KERNEL DECIDED BY EVALUATION, behind `Johnson.Unfolds.slice_toNat?_eq`
(Johnson/Unfolds/SliceFoldl.lean), whose own limits bind here: its laws unfold definitions of Lean's
library by name, which another toolchain may spell otherwise. It has been checked by Lean's own
kernel alone. A matrix that an earlier segment has committed to has no array of the later segment: l
is the owner's number. Beyond the packed rows the left side is 0 (`pack3_out`, Packed.lean), and so
the right. The readers are letters.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.FirstData
import Johnson.Unfolds.SliceFoldl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.HonestTrace (Sz Seg MatName pack3 packedCells pack3_eq_pack arrayLabel)
open ProofFile.Honest.K1 (labelNo cellsVals)

/-- **A ring map goes through the packing of three rows.** -/
theorem pack3_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (col : ℕ → A)
    (i : ℕ) : f (pack3 m col i) = pack3 m (fun r => f (col r)) i := by
  have h2 : f 2 = 2 := by rw [← one_add_one_eq_two, map_add, map_one, one_add_one_eq_two]
  unfold pack3
  split_ifs <;> simp [h2]

/-- The triple (x, 0, 0) of words is read as the image of x. -/
theorem toE_base (x : Cb.Gl.F) :
    OnBytes.Slice.toE (OnBytes.Slice.ofF x, 0, 0) = algebraMap Cb.Gl.F Cb.Gl.E x := by
  have h := OnBytes.Slice.toE_ofF (OnBytes.Slice.ofF x)
  rw [OnBytes.Slice.toF_ofF] at h
  exact h

/-- An element of the base field as the programs' element, read back: its image. -/
theorem val_eOfF (x : Cb.Gl.F) :
    OnBytes.Model.Reading.gl.val (eOfF x) = algebraMap Cb.Gl.F Cb.Gl.E x := by
  show OnBytes.Slice.toE (OnBytes.E.ofTriple (OnBytes.Slice.ofF x, 0, 0)).triple = _
  rw [OnBytes.E.triple_ofTriple]
  exact toE_base x

/-- An entry over the base field, as the frame reads it into the extension field: its image. -/
theorem asE_inl (x : Cb.Gl.F) : asE (some (.inl x)) = algebraMap Cb.Gl.F Cb.Gl.E x :=
  toE_base x

/-- **The frame's reader of an array's name reads "M mu" as mu**, at every mu below 26. By one
closed fact, decided by evaluation in Lean's kernel behind the library's rewriting of `toNat?`. -/
theorem labelNo_arrayLabel {mu : ℕ} (h : mu < 26) : labelNo (arrayLabel mu) = some mu := by
  have H : ((List.range 26).all fun k => labelNo (arrayLabel k) == some k) = true := by
    simp only [labelNo, Johnson.Unfolds.slice_toNat?_eq]
    decide +kernel
  exact eq_of_beq (List.all_eq_true.1 H mu (List.mem_range.2 h))

/-- **THE VALUE OF AN ARRAY "M mu" IS A PACKING OF THE READER's CELLS.** Conditional: hn: the name
is read as mu; hM: mu names the matrix μ of the segment σ with the number l; hc: the column lies
inside the matrix's shape. -/
theorem cellsVals_pack (S : Sz) (R : Readers) (hd : List Fmt.Drawn) {l mu : ℕ} {name : String}
    (hn : labelNo name = some mu) {σ : Seg} {μ : MatName} (hM : S.matAt l mu = some (σ, μ))
    {c : ℕ} (hc : c < (S.shape σ μ).2) (i' : ℕ) :
    asE (some ((cellsVals S).val R hd l name i' c)) =
      Alg.pack (2 ^ 20) (fun r : Fin (S.shape σ μ).1 =>
        algebraMap Cb.Gl.F Cb.Gl.E (R.cells.cell l μ.label r.val c)) i' := by
  have e : (cellsVals S).val R hd l name i' c =
      .inl (pack3 (S.shape σ μ).1 (fun r => R.cells.cell l μ.label r c) i') := by
    simp only [cellsVals, hn, packedCells, hM, if_pos hc]
  rw [e, asE_inl, pack3_map, pack3_eq_pack]

/-- **The size that the values say of an array**: the matrix's packed shape. Conditional: hn; hM;
ho: the matrix has an array of its own segment. -/
theorem cellsVals_size (S : Sz) {l mu : ℕ} {name : String} (hn : labelNo name = some mu)
    {σ : Seg} {μ : MatName} (hM : S.matAt l mu = some (σ, μ))
    (ho : (S.arrayNo σ μ).isSome = true) :
    (cellsVals S).size l name = some (S.packedShape l mu) := by
  simp only [cellsVals, hn, hM, Option.bind_some, ho, if_true]

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.pack3_map
#print axioms ProofFile.Honest.K5.toE_base
#print axioms ProofFile.Honest.K5.val_eOfF
#print axioms ProofFile.Honest.K5.asE_inl
#print axioms ProofFile.Honest.K5.labelNo_arrayLabel
#print axioms ProofFile.Honest.K5.cellsVals_pack
#print axioms ProofFile.Honest.K5.cellsVals_size
