-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Packed.lean

The arrays of moment 0: the byte format's packing of a segment's matrices of cells into arrays over
F, and the layout's numbering of these arrays. At any sizes and any number of groups.

By docs/format/11-1-machinery.md a segment commits to each matrix number mu of its list that no
earlier segment has committed to, as the array M mu, whose entry in row i and column c holds the
rows of cells 3 i, 3 i + 1 and 3 i + 2 of column c, as cell(3 i) + 2^20 cell(3 i + 1) + 2^40 cell(3
i + 2), read in F. This file writes that array as a function of the sizes ("Sz",
Johnson/HonestTrace/Places.lean) and of the cells. It has no coin and no challenge in it.

Main definitions and theorems:
* "pack3": three rows of cells in one element, over any commutative ring. "pack3_eq_pack": it is the
  library's "Alg.pack" at the radix 2^20.
* "packedOf S T l mu i c": the array's entry, from a trace T of integers by numbers. "packedCells S
  cell l mu i c": the same from cells in F read by a segment's number and a matrix's label.
  "packedOf_eq_cells": the two agree if "cell" returns the images of T's integers.
* "Sz.matAt", "Sz.shapeNo", "Sz.packedShape": from numbers to names, the rows of cells and columns,
  the packed rows (m + 2) / 3 and columns. "matAt_eq_some_iff".
* "packedOf_out", "packedOf_zero": the entry is 0 outside the packed shape, and where its cells are
  0.
* "cellBack", "cellBack_packedOf": if all cells of a matrix inside its shape are below 2^19 in
  absolute value, they are read back from the packed array.
* "Sz.arrayNo", "Sz.ofArrayNo", "Sz.nArr", "arrayLabel": the number of a matrix's array among the
  arrays of moment 0 of its segment, the way back, how many there are, and the array's name.
  "arrayNo_isSome_iff", "arrayNo_lt", "arrayNo_inj", "arrayNo_onto", "ofArrayNo_arrayNo".
* "ref_arrays", "small_arrays": at the numbers of the two example sets the packed rows and columns,
  in that numbering, of four segments (the feed-forward segments of groups 0 and 1, attention of
  group 0, the head) are the numerals typed here, which a program outside Lean counted off the two
  layout files.

Limits. The rule of the packing and the rule of the numbering were typed by a reading of the
format's page. Rows and columns are those of "Sz.shape", with the limits of
Johnson/HonestTrace/Places.lean. In a layout file the links count from 1, and the numbers of arrays
begin again at each moment: "Sz.arrayNo" is the fourth word of a block's line whose second word is
1. Where in an oracle message's table an array's entry lies (the blocks of the item layout) is not a
matter of this file, nor are the arrays U3, ZZ and BZ, mask rows or padding of messages. For a
borrowed matrix "packedOf" packs what T has under the reader's numbers; that this is the owner's
array is a property of T (for the laying of Johnson/HonestTrace/Places.lean: "lay_owner"). The
strings that "packedCells" asks for spell a part by the matrix's name and the part's number ("af0"),
where the format's pages name whole matrices alone: they are the names of the entries in the Lean
verifier's plans ("TMat.name"), which is shown for public files in the goals' scope in
Johnson/Goal/HonestTrace/FullInScope.lean ("planName_ff_in_scope", "planName_att_in_scope",
"planName_head_in_scope"), not here. The bound 2^19 is, but for the value -2^19, what the digits
allow; the library's theorem that a symbol has one reading ("symbol_has_one_reading",
OnBytes/Model/FormFLaws.lean) asks cells strictly between -2^18 and 2^18. The numbers of
"ref_arrays" and "small_arrays" were counted off the two layout files by a program outside Lean; no
theorem of this file reads a file. xbI and xbO have one shape, so the numerals show that one array
of the stream stands before qa in group 0 and none from group 1 on, not which: that it is xbI rests
on the format's table of moments (docs/format/11-2-feed-forward-segment.md) alone. "Segment" here is
what the files on the lookups call a sub-proof.

Not claimed: that a prover's arrays are these; that a verifier accepts anything; anything on the
values of the cells.

-/
import Alg.Range
import Cb.Gl.GlField
import Johnson.HonestTrace.PlacesBack

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

/-! ## From numbers to names -/

namespace Sz
variable (S : Sz)

/-- The name with the number mu in the list of a segment's sort; "none" from the list's length on.
By comparison of numbers: the way back of "MatName.no?". -/
def nameNo : Seg → ℕ → Option MatName
  | .ff _, mu =>
    if mu < S.NAf then some (.af mu)
    else if mu < S.NAf + S.NAd then some (.ad (mu - S.NAf))
    else if mu = S.NAf + S.NAd then some .ar
    else if mu = S.NAf + S.NAd + 1 then some .b
    else if mu = S.NAf + S.NAd + 2 then some .qa
    else if mu = S.NAf + S.NAd + 3 then some .xbO
    else if mu = S.NAf + S.NAd + 4 then some .xbI
    else none
  | .att _, mu =>
    if mu < S.NAs then some (.as mu)
    else if mu = S.NAs then some .ah
    else if mu = S.NAs + 1 then some .ao
    else if mu = S.NAs + 2 then some .bA
    else if mu = S.NAs + 3 then some .qa
    else none
  | .head, mu =>
    if mu < S.NHf then some (.hf mu)
    else if mu = S.NHf then some .hd
    else if mu = S.NHf + 1 then some .hr
    else if mu = S.NHf + 2 then some .bH
    else if mu = S.NHf + 3 then some .xbL
    else none

/-- The segment with the number l (from 0) and the matrix with the number mu in its list; "none" if
the proof has no such segment or its list no such number. -/
def matAt (l mu : ℕ) : Option (Seg × MatName) :=
  (Seg.ofNo S.nGr l).bind fun σ => (S.nameNo σ mu).map fun μ => (σ, μ)

/-- Rows of cells and columns of matrix number mu of segment number l; (0, 0) if there is none. -/
def shapeNo (l mu : ℕ) : ℕ × ℕ :=
  match S.matAt l mu with
  | some (σ, μ) => S.shape σ μ
  | none => (0, 0)

/-- Rows and columns of the packed array of that matrix: three rows of cells in one row. -/
def packedShape (l mu : ℕ) : ℕ × ℕ := (Alg.symRows (S.shapeNo l mu).1, (S.shapeNo l mu).2)

end Sz

/-- The name that "nameNo" returns at mu has the number mu. -/
theorem no?_of_nameNo (S : Sz) {σ : Seg} {mu : ℕ} {μ : MatName} (h : S.nameNo σ mu = some μ) :
    MatName.no? S.NAf S.NAd S.NAs S.NHf σ μ = some mu := by
  cases σ <;> simp only [Sz.nameNo] at h <;> split_ifs at h <;>
    (obtain rfl := Option.some.inj h
     simp only [MatName.no?]
     first
       | (rw [if_pos (by omega)] <;> (congr 1; omega))
       | (congr 1; omega))

/-- A number in the list of a segment's sort is below the list's length. -/
theorem no?_lt (S : Sz) {σ : Seg} {μ : MatName} {mu : ℕ}
    (h : MatName.no? S.NAf S.NAd S.NAs S.NHf σ μ = some mu) : mu < S.len σ := by
  cases σ <;> cases μ <;> simp [MatName.no?, Sz.len] at h ⊢ <;> omega

/-- Below the list's length "nameNo" returns a name. -/
theorem nameNo_isSome (S : Sz) {σ : Seg} {mu : ℕ} (h : mu < S.len σ) :
    ∃ μ, S.nameNo σ mu = some μ := by
  cases σ <;> simp only [Sz.nameNo, Sz.len] at h ⊢ <;> split_ifs <;>
    first | exact ⟨_, rfl⟩ | omega

/-- "nameNo" returns μ at mu exactly if μ has the number mu. -/
theorem nameNo_eq_some_iff (S : Sz) (σ : Seg) (mu : ℕ) (μ : MatName) :
    S.nameNo σ mu = some μ ↔ MatName.no? S.NAf S.NAd S.NAs S.NHf σ μ = some mu := by
  constructor
  · exact no?_of_nameNo S
  · intro h
    obtain ⟨ν, hν⟩ := nameNo_isSome S (no?_lt S h)
    rw [hν, MatName.no?_inj (no?_of_nameNo S hν) h]

/-- "matAt" returns (σ, μ) at (l, mu) exactly if σ is a segment of the proof with the number l and μ
has the number mu in its list. -/
theorem matAt_eq_some_iff (S : Sz) (l mu : ℕ) (σ : Seg) (μ : MatName) :
    S.matAt l mu = some (σ, μ) ↔ σ.Below S.nGr ∧ σ.no S.nGr = l ∧ S.mu σ μ = some mu := by
  unfold Sz.matAt Sz.mu
  constructor
  · intro h
    obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨μ', h3, h4⟩ := Option.map_eq_some_iff.1 h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
    obtain ⟨b1, b2⟩ := Seg.of_ofNo h1
    exact ⟨b1, b2, by rw [if_pos b1]; exact (nameNo_eq_some_iff S _ _ _).1 h3⟩
  · rintro ⟨b1, rfl, h3⟩
    rw [if_pos b1] at h3
    rw [Seg.ofNo_no b1]
    show (S.nameNo σ mu).map (fun μ => (σ, μ)) = _
    rw [(nameNo_eq_some_iff S _ _ _).2 h3]
    rfl

/-! ## The packing -/

/-- **Three rows of cells in one element.** Of a column with m rows of cells: cell(3 i) + 2^20
cell(3 i + 1) + 2^40 cell(3 i + 2), where a row from m on counts as 0
(docs/format/11-1-machinery.md, "The array of a matrix"). -/
def pack3 {A : Type} [CommRing A] (m : ℕ) (col : ℕ → A) (i : ℕ) : A :=
  (if 3 * i < m then col (3 * i) else 0) + 2 ^ 20 * (if 3 * i + 1 < m then col (3 * i + 1) else 0) +
    2 ^ 40 * (if 3 * i + 2 < m then col (3 * i + 2) else 0)

/-- **The array of a matrix**: entry (i, c) of the packed array of matrix number mu of segment
number l (from 0), from a trace T by numbers (segment, matrix, row of cells, column). The sum is
formed over the integers and then read in F, so a negative cell enters as a negative integer. The
rows of cells and the columns are S's; the entry is 0 from S's columns on. -/
def packedOf (S : Sz) (T : ℕ → ℕ → ℕ → ℕ → ℤ) (l mu i c : ℕ) : Cb.Gl.F :=
  if c < (S.shapeNo l mu).2 then ((pack3 (S.shapeNo l mu).1 (fun r => T l mu r c) i : ℤ) : Cb.Gl.F)
  else 0

/-- The same from cells in F that are read by the segment's number and a string for the matrix: the
string asked for is "MatName.label" of the matrix with the number mu ("af0", "af1", .., "ar", ..). 0
where "matAt" is "none". -/
def packedCells (S : Sz) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (l mu i c : ℕ) : Cb.Gl.F :=
  match S.matAt l mu with
  | some (σ, μ) =>
    if c < (S.shape σ μ).2 then pack3 (S.shape σ μ).1 (fun r => cell l μ.label r c) i else 0
  | none => 0

/-- "pack3" is the library's packing "Alg.pack" (Alg/Range.lean) at the radix 2^20. -/
theorem pack3_eq_pack {A : Type} [CommRing A] (m : ℕ) (col : ℕ → A) (i : ℕ) :
    pack3 m col i = Alg.pack (2 ^ 20) (fun r : Fin m => col r.val) i := by
  unfold pack3 Alg.pack Alg.lane
  push_cast
  simp only [Nat.add_zero, dite_eq_ite]
  ring

/-- From (m + 2) / 3 packed rows on "pack3" is 0. -/
theorem pack3_out {A : Type} [CommRing A] {m i : ℕ} (col : ℕ → A) (h : Alg.symRows m ≤ i) :
    pack3 m col i = 0 := by
  unfold Alg.symRows at h
  unfold pack3
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

/-- Packing integers and reading the sum in a ring is packing the integers' images. -/
theorem pack3_cast {A : Type} [CommRing A] (m : ℕ) (col : ℕ → ℤ) (i : ℕ) :
    ((pack3 m col i : ℤ) : A) = pack3 m (fun r => (col r : A)) i := by
  unfold pack3
  split_ifs <;> push_cast <;> ring

/-- Outside the packed shape, (m + 2) / 3 rows and S's columns, the array's entry is 0. -/
theorem packedOf_out (S : Sz) (T : ℕ → ℕ → ℕ → ℕ → ℤ) (l mu i c : ℕ)
    (h : ¬ (i < (S.packedShape l mu).1 ∧ c < (S.packedShape l mu).2)) :
    packedOf S T l mu i c = 0 := by
  unfold packedOf
  by_cases hc : c < (S.shapeNo l mu).2
  · rw [if_pos hc, pack3_out _ (Nat.le_of_not_lt fun hi => h ⟨hi, hc⟩)]
    rfl
  · exact if_neg hc

/-- An entry of the array is 0 if the cells of its up to three rows of cells inside the matrix are
0. -/
theorem packedOf_zero (S : Sz) (T : ℕ → ℕ → ℕ → ℕ → ℤ) (l mu i c : ℕ)
    (h : ∀ r, r / 3 = i → r < (S.shapeNo l mu).1 → T l mu r c = 0) :
    packedOf S T l mu i c = 0 := by
  have z : pack3 (S.shapeNo l mu).1 (fun r => T l mu r c) i = 0 := by
    unfold pack3
    rw [ite_eq_right_iff.2 (h (3 * i) (by omega)), ite_eq_right_iff.2 (h (3 * i + 1) (by omega)),
      ite_eq_right_iff.2 (h (3 * i + 2) (by omega))]
    rfl
  unfold packedOf
  rw [z]
  simp

/-- If the reader "cell" returns, at every segment of the proof and every matrix of its list, under
the segment's number and the matrix's label, the image in F of T's integer: "packedOf" at T is
"packedCells" at "cell". -/
theorem packedOf_eq_cells (S : Sz) (T : ℕ → ℕ → ℕ → ℕ → ℤ)
    (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (h : ∀ σ μ mu, σ.Below S.nGr → S.mu σ μ = some mu → ∀ r c,
      cell (σ.no S.nGr) μ.label r c = ((T (σ.no S.nGr) mu r c : ℤ) : Cb.Gl.F)) (l mu i c : ℕ) :
    packedOf S T l mu i c = packedCells S cell l mu i c := by
  unfold packedOf packedCells Sz.shapeNo
  cases hm : S.matAt l mu with
  | none => rfl
  | some q =>
    obtain ⟨σ, μ⟩ := q
    obtain ⟨b1, rfl, h3⟩ := (matAt_eq_some_iff S l mu σ μ).1 hm
    show (if c < (S.shape σ μ).2 then _ else _) = if c < (S.shape σ μ).2 then _ else _
    rw [pack3_cast]
    simp only [h σ μ mu b1 h3]

/-! ## Unpacking -/

/-- The balanced digit of an integer at the radix 2^20: in -2^19 .. 2^19 - 1. -/
def lowDigit (z : ℤ) : ℤ := (z + 2 ^ 19) % 2 ^ 20 - 2 ^ 19

/-- What is left of an integer above its balanced digit. -/
def restDigit (z : ℤ) : ℤ := (z - lowDigit z) / 2 ^ 20

/-- Digit number j of an integer. -/
def digitAt : ℕ → ℤ → ℤ
  | 0, z => lowDigit z
  | j + 1, z => digitAt j (restDigit z)

/-- **The cell at row r and column c, read back from a packed array P**: balanced digit number r mod
3, at the radix 2^20, of the least residue in absolute value of P's entry in row r / 3. -/
def cellBack (P : ℕ → ℕ → Cb.Gl.F) (r c : ℕ) : ℤ := digitAt (r % 3) (P (r / 3) c).valMinAbs

/-- Three integers below 2^19 in absolute value are the first three balanced digits of a + 2^20 b +
2^40 c. -/
theorem digits3 {a b c : ℤ} (ha : |a| < 2 ^ 19) (hb : |b| < 2 ^ 19) (hc : |c| < 2 ^ 19) :
    digitAt 0 (a + 2 ^ 20 * b + 2 ^ 40 * c) = a ∧ digitAt 1 (a + 2 ^ 20 * b + 2 ^ 40 * c) = b ∧
      digitAt 2 (a + 2 ^ 20 * b + 2 ^ 40 * c) = c := by
  rw [abs_lt] at ha hb hc
  norm_num at ha hb hc
  have low : ∀ x y : ℤ, -524288 < x → x < 524288 → lowDigit (x + 1048576 * y) = x := by
    intro x y h1 h2
    unfold lowDigit
    norm_num
    omega
  have rest : ∀ x y : ℤ, -524288 < x → x < 524288 → restDigit (x + 1048576 * y) = y := by
    intro x y h1 h2
    unfold restDigit
    rw [low x y h1 h2]
    norm_num
  have e : a + 2 ^ 20 * b + 2 ^ 40 * c = a + 1048576 * (b + 1048576 * c) := by ring
  rw [e]
  refine ⟨low _ _ ha.1 ha.2, ?_, ?_⟩
  · show lowDigit (restDigit _) = b
    rw [rest _ _ ha.1 ha.2]
    exact low _ _ hb.1 hb.2
  · show lowDigit (restDigit (restDigit _)) = c
    rw [rest _ _ ha.1 ha.2, rest _ _ hb.1 hb.2]
    have h0 := low c 0 hc.1 hc.2
    rw [mul_zero, add_zero] at h0
    exact h0

/-- An integer below 2^60 in absolute value is the least residue in absolute value of its image in
F. -/
theorem valMinAbs_cast {z : ℤ} (h : |z| < 2 ^ 60) : ((z : ℤ) : Cb.Gl.F).valMinAbs = z := by
  haveI : NeZero Code.pGold := ⟨by norm_num [Code.pGold]⟩
  rw [abs_lt] at h
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩
  · have : ((Code.pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [Code.pGold]
    rw [this]
    norm_num at h
    omega
  · have : ((Code.pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [Code.pGold]
    rw [this]
    norm_num at h
    omega

/-- **Unpacking.** If all cells of matrix number mu of segment number l inside S's shape are below
2^19 in absolute value, "cellBack" reads each of them back from the packed array. -/
theorem cellBack_packedOf (S : Sz) (T : ℕ → ℕ → ℕ → ℕ → ℤ) (l mu : ℕ)
    (hT : ∀ r c, r < (S.shapeNo l mu).1 → c < (S.shapeNo l mu).2 → |T l mu r c| < 2 ^ 19)
    (r c : ℕ) (hr : r < (S.shapeNo l mu).1) (hc : c < (S.shapeNo l mu).2) :
    cellBack (packedOf S T l mu) r c = T l mu r c := by
  have lane : ∀ j, |if 3 * (r / 3) + j < (S.shapeNo l mu).1 then T l mu (3 * (r / 3) + j) c else 0|
      < 2 ^ 19 := by
    intro j
    split_ifs with h
    · exact hT _ _ h hc
    · norm_num
  have l0 := lane 0
  have l1 := lane 1
  have l2 := lane 2
  rw [Nat.add_zero] at l0
  obtain ⟨d0, d1, d2⟩ := digits3 l0 l1 l2
  have hz : |pack3 (S.shapeNo l mu).1 (fun r => T l mu r c) (r / 3)| < 2 ^ 60 := by
    unfold pack3
    rw [abs_lt] at l0 l1 l2 ⊢
    norm_num at l0 l1 l2 ⊢
    constructor <;> omega
  unfold cellBack packedOf
  rw [if_pos hc, valMinAbs_cast hz]
  have h3 : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  unfold pack3
  rcases h3 with h | h | h
  · rw [h, d0, if_pos (by omega), show 3 * (r / 3) = r by omega]
  · rw [h, d1, if_pos (by omega), show 3 * (r / 3) + 1 = r by omega]
  · rw [h, d2, if_pos (by omega), show 3 * (r / 3) + 2 = r by omega]

/-! ## The layout's numbering of the arrays of moment 0 -/

namespace Sz
variable (S : Sz)

/-- **The number of a matrix's array among the arrays of moment 0 of its segment**, from 0: first
the matrices that no other segment reads, in the list's order, then those that another segment
reads, in the list's order (docs/format/11-1-machinery.md, the table of arrays). In a feed-forward
segment: af, ad, ar, b, in group 0 then xbI, then qa, xbO. In attention and in the head it is the
number in the list. "none" for a borrowed matrix, for whatever is not in the list, and at a group
from nGr on. -/
def arrayNo (σ : Seg) (μ : MatName) : Option ℕ :=
  if (S.mu σ μ).isSome then
    match σ, μ with
    | .ff g, .xbI => if g = 0 then some (S.NAf + S.NAd + 2) else none
    | .ff g, .qa => some (S.NAf + S.NAd + (if g = 0 then 3 else 2))
    | .ff g, .xbO => some (S.NAf + S.NAd + (if g = 0 then 4 else 3))
    | .att _, .qa => none
    | .head, .xbL => none
    | _, _ => S.mu σ μ
  else none

/-- How many arrays of matrices a segment has at moment 0. -/
def nArr : Seg → ℕ
  | .ff g => S.NAf + S.NAd + (if g = 0 then 5 else 4)
  | .att _ => S.NAs + 3
  | .head => S.NHf + 3

/-- The way back: the matrix whose array has the number a among the arrays of moment 0; "none" from
"nArr" on and outside the proof. -/
def ofArrayNo (σ : Seg) (a : ℕ) : Option MatName :=
  if σ.Below S.nGr then
    match σ with
    | .ff g =>
      if a < S.NAf + S.NAd + 2 then S.nameNo σ a
      else if g = 0 then
        if a = S.NAf + S.NAd + 2 then some .xbI
        else if a = S.NAf + S.NAd + 3 then some .qa
        else if a = S.NAf + S.NAd + 4 then some .xbO
        else none
      else if a = S.NAf + S.NAd + 2 then some .qa
      else if a = S.NAf + S.NAd + 3 then some .xbO
      else none
    | .att _ => if a < S.NAs + 3 then S.nameNo σ a else none
    | .head => if a < S.NHf + 3 then S.nameNo σ a else none
  else none

end Sz

/-- The name of the array of matrix number mu in the item layout: the letter M followed by mu in
decimal digits. mu is the number in the segment's list, not "Sz.arrayNo": in group 0 the two part
(xbI has the array number NAf + NAd + 2 and the name M followed by NAf + NAd + 4). -/
def arrayLabel (mu : ℕ) : String := "M" ++ toString mu

/-- A matrix has an array of its segment exactly if it is in the segment's list and is its own
owner. -/
theorem arrayNo_isSome_iff (S : Sz) (σ : Seg) (μ : MatName) :
    (S.arrayNo σ μ).isSome = true ↔ (S.mu σ μ).isSome = true ∧ S.owner σ μ = (σ, μ) := by
  unfold Sz.arrayNo
  by_cases hm : (S.mu σ μ).isSome = true
  · rw [if_pos hm]
    cases σ <;> cases μ <;> simp [hm, Sz.owner]
  · rw [if_neg hm]
    simp [hm]

/-- An array's number is below "nArr". -/
theorem arrayNo_lt (S : Sz) {σ : Seg} {μ : MatName} {a : ℕ} (h : S.arrayNo σ μ = some a) :
    a < S.nArr σ := by
  unfold Sz.arrayNo at h
  by_cases hm : (S.mu σ μ).isSome = true
  · have hσ := below_of_mu hm
    rw [if_pos hm] at h
    unfold Sz.mu at h
    cases σ <;> cases μ <;> simp only [if_pos hσ, MatName.no?, Sz.nArr] at h ⊢ <;>
      (try split_ifs at h ⊢) <;>
      first | contradiction | (have := Option.some.inj h; omega)
  · rw [if_neg hm] at h
    contradiction

/-- "ofArrayNo" undoes "arrayNo". -/
theorem ofArrayNo_arrayNo (S : Sz) {σ : Seg} {μ : MatName} {a : ℕ} (h : S.arrayNo σ μ = some a) :
    S.ofArrayNo σ a = some μ := by
  unfold Sz.arrayNo at h
  by_cases hm : (S.mu σ μ).isSome = true
  · have hσ := below_of_mu hm
    rw [if_pos hm] at h
    unfold Sz.mu at h
    cases σ <;> cases μ <;> simp only [if_pos hσ, MatName.no?] at h <;>
      (try split_ifs at h) <;>
      first
        | contradiction
        | (obtain rfl := Option.some.inj h
           simp only [Sz.ofArrayNo, if_pos hσ, Sz.nameNo]
           split_ifs <;> first | rfl | omega | (congr 2; omega))
  · rw [if_neg hm] at h
    contradiction

/-- In one segment two matrices whose arrays have one number are one matrix. -/
theorem arrayNo_inj (S : Sz) {σ : Seg} {μ ν : MatName} {a : ℕ} (hμ : S.arrayNo σ μ = some a)
    (hν : S.arrayNo σ ν = some a) : μ = ν :=
  Option.some.inj ((ofArrayNo_arrayNo S hμ).symm.trans (ofArrayNo_arrayNo S hν))

/-- In a segment of the proof every number below "nArr" is the number of a matrix's array. -/
theorem arrayNo_onto (S : Sz) {σ : Seg} (hσ : σ.Below S.nGr) {a : ℕ} (h : a < S.nArr σ) :
    ∃ μ, S.arrayNo σ μ = some a := by
  cases σ with
  | ff g =>
    have hg : g < S.nGr := hσ
    have h' : a < S.NAf + S.NAd + (if g = 0 then 5 else 4) := h
    by_cases h1 : a < S.NAf
    · exact ⟨.af a, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h1]⟩
    by_cases h2 : a < S.NAf + S.NAd
    · exact ⟨.ad (a - S.NAf), by
        have h3 : a - S.NAf < S.NAd := by omega
        simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3]
        omega⟩
    by_cases h0 : g = 0
    · rw [if_pos h0] at h'
      obtain h3 | h3 | h3 | h3 | h3 : a = S.NAf + S.NAd ∨ a = S.NAf + S.NAd + 1 ∨
          a = S.NAf + S.NAd + 2 ∨ a = S.NAf + S.NAd + 3 ∨ a = S.NAf + S.NAd + 4 := by omega
      · exact ⟨.ar, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3]⟩
      · exact ⟨.b, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3]⟩
      · exact ⟨.xbI, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, h3, h0]; omega⟩
      · exact ⟨.qa, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, h3, h0]; omega⟩
      · exact ⟨.xbO, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, h3, h0]; omega⟩
    · rw [if_neg h0] at h'
      obtain h3 | h3 | h3 | h3 : a = S.NAf + S.NAd ∨ a = S.NAf + S.NAd + 1 ∨
          a = S.NAf + S.NAd + 2 ∨ a = S.NAf + S.NAd + 3 := by omega
      · exact ⟨.ar, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3]⟩
      · exact ⟨.b, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3]⟩
      · exact ⟨.qa, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3, h0]⟩
      · exact ⟨.xbO, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3, h0]⟩
  | att g =>
    have hg : g < S.nGr := hσ
    have h' : a < S.NAs + 3 := h
    by_cases h1 : a < S.NAs
    · exact ⟨.as a, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h1]⟩
    obtain h3 | h3 | h3 : a = S.NAs ∨ a = S.NAs + 1 ∨ a = S.NAs + 2 := by omega
    · exact ⟨.ah, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3]⟩
    · exact ⟨.ao, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3]⟩
    · exact ⟨.bA, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, hg, h3]⟩
  | head =>
    have h' : a < S.NHf + 3 := h
    by_cases h1 : a < S.NHf
    · exact ⟨.hf a, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, h1]⟩
    obtain h3 | h3 | h3 : a = S.NHf ∨ a = S.NHf + 1 ∨ a = S.NHf + 2 := by omega
    · exact ⟨.hd, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, h3]⟩
    · exact ⟨.hr, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, h3]⟩
    · exact ⟨.bH, by simp [Sz.arrayNo, Sz.mu, Seg.Below, MatName.no?, h3]⟩

/-! ## The two example sets -/

/-- Rows and columns of the packed arrays of moment 0 of a segment, in the order of "arrayNo". -/
def arraysOf (S : Sz) (σ : Seg) : List (ℕ × ℕ) :=
  (List.range (S.nArr σ)).map fun a =>
    match S.ofArrayNo σ a with
    | some μ => (Alg.symRows (S.shape σ μ).1, (S.shape σ μ).2)
    | none => (0, 0)

/-- At the full-size example's numbers the packed arrays of moment 0 of the feed-forward segments of
groups 0 and 1, of the attention segment of group 0 and of the head have these rows and columns. The
numbers were counted off examples/full-size/config/layout.txt by a program outside Lean (the lines
whose second word is 1; links 1, 3, 2 and 25), and typed here by hand. -/
theorem ref_arrays :
    arraysOf Sz.ref (.ff 0) = [(21846, 5990), (21846, 5990), (21846, 5990), (10923, 3200),
        (2731, 324), (21846, 256), (21846, 400), (21846, 1536), (21846, 400)] ∧
      arraysOf Sz.ref (.ff 1) = [(21846, 5990), (21846, 5990), (21846, 5990), (10923, 3200),
        (2731, 324), (21846, 256), (21846, 1536), (21846, 400)] ∧
      arraysOf Sz.ref (.att 0) = [(21846, 7200), (2731, 360), (21846, 640), (5462, 512)] ∧
      arraysOf Sz.ref .head = [(21846, 4816), (21846, 4816), (21846, 4816), (21846, 4816),
        (5462, 640), (2731, 15), (10923, 384)] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The same at the small example's numbers, against examples/accepted-proof/config/layout.txt
(links 1, 3, 2 and 5). -/
theorem small_arrays :
    arraysOf Sz.small (.ff 0) = [(2731, 247), (2731, 247), (2731, 247), (1366, 160), (1366, 14),
        (2731, 2048), (2731, 20), (2731, 96), (2731, 20)] ∧
      arraysOf Sz.small (.ff 1) = [(2731, 247), (2731, 247), (2731, 247), (1366, 160), (1366, 14),
        (2731, 2048), (2731, 96), (2731, 20)] ∧
      arraysOf Sz.small (.att 0) = [(683, 120), (1366, 4), (2731, 32), (2731, 1024)] ∧
      arraysOf Sz.small .head = [(5462, 20), (1366, 16), (1366, 2), (2731, 1536)] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.packedOf
#print axioms OnBytes.HonestTrace.packedCells
#print axioms OnBytes.HonestTrace.Sz.arrayNo
#print axioms OnBytes.HonestTrace.no?_of_nameNo
#print axioms OnBytes.HonestTrace.no?_lt
#print axioms OnBytes.HonestTrace.nameNo_isSome
#print axioms OnBytes.HonestTrace.nameNo_eq_some_iff
#print axioms OnBytes.HonestTrace.matAt_eq_some_iff
#print axioms OnBytes.HonestTrace.pack3_eq_pack
#print axioms OnBytes.HonestTrace.pack3_out
#print axioms OnBytes.HonestTrace.pack3_cast
#print axioms OnBytes.HonestTrace.packedOf_out
#print axioms OnBytes.HonestTrace.packedOf_zero
#print axioms OnBytes.HonestTrace.packedOf_eq_cells
#print axioms OnBytes.HonestTrace.digits3
#print axioms OnBytes.HonestTrace.valMinAbs_cast
#print axioms OnBytes.HonestTrace.cellBack_packedOf
#print axioms OnBytes.HonestTrace.arrayNo_isSome_iff
#print axioms OnBytes.HonestTrace.arrayNo_lt
#print axioms OnBytes.HonestTrace.ofArrayNo_arrayNo
#print axioms OnBytes.HonestTrace.arrayNo_inj
#print axioms OnBytes.HonestTrace.arrayNo_onto
#print axioms OnBytes.HonestTrace.ref_arrays
#print axioms OnBytes.HonestTrace.small_arrays
