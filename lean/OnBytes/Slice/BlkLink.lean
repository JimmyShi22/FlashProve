-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLink.lean: the rows of the program's link, in the field.

The program's verifier of a link (OnBytes/Iop/Link.lean) forms linear claims, rows, on the two
folded rows that the prover sent: one equality row, a sample row for each of the two, and, for
every draw in one of the two stored tables, the row of the column there. It keeps each row as a
short description made of tensors.
This file reads the rows' coefficients and targets in the field and shows that they are the rows
`rowsX` of OnBytes/Slice/RowsX.lean, which are a function of the statement that the library's
verifier holds after the link's five rounds. Nothing is said here on a run of the program's
blocks: what a run yields enters as hypotheses, gathered in three records.

Main definitions.
 `Sz.layU`   how a folded row is arranged in its oracle message.
 `XTie`      what ties the library's statement to what the program has drawn and received.
 `LinkRows`  what the program's rows are: the calls that made them, and the sample rows' values.
 `LinkFit`   what is asked of sizes and shapes.
Main theorems.
 `sum_laid_below`, `sum_laid_placed`: a cut tensor, placed on a table, for every reading.
 `coefAt_eqRow`, `coefAt_colRow`, `coefAt_smpRow`: the three kinds of rows have the coefficients
   `Sz.eqC`, `Sz.colC`, `Sz.smpC`. For the first two kinds also: the rows' targets and kinds, that
   they are 0 on all other tables, and that they hold no written-out factor. The like for a sample
   row is in OnBytes/Slice/BlkSend.lean.
 `readE_foldeqSymbol`, `foldSym₀_closed`, `foldSym₁_closed`: the program's and the library's fold of
   an opened column, as one sum.
 `rows_cfX`: the list of the program's rows has the targets `tgX` and the coefficients `cfX`.
 `stmG_rowsX`: a row on the group that is the sum of these rows under the powers of an element,
   read as a statement of the link's stage, is the combination `sumStm` of the rows `rowsX`.

Not claimed. That a run of the program's link yields the three records. Nothing on tables with a
record, nor on a folded row that is arranged row by row in the low digits.
-/
import OnBytes.Slice.BlkTens
import OnBytes.Slice.BlkRow
import OnBytes.Slice.BlkSend
import OnBytes.Slice.RowsX
import OnBytes.Iop.Link

set_option autoImplicit false

namespace OnBytes.Slice
open OnBytes.Model (Reading)

/-! ## Cut tensors, placed on a table -/

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A vector's tensor, cut at a length and placed on a table: at an index of the table the parts add
up to the tensor's entry at the number e of the vector's entry that is there if e is below the
length, and to 0 else. -/
theorem sum_laid_below (lay : VectorLay) (v : Tensor) (hv : v.denseVars = []) (len : ℕ)
    (l : List Tensor) (h : tensorBelow v 0 v.vars len = some l) (hlen : len ≤ 2 ^ v.vars)
    (hb : v.vars ≤ lay.bits) (i : ℕ) (hi : i < 2 ^ lay.bits) :
    (l.map fun w => ρ.val ((lay.onTable w).entry i)).sum =
      if lay.entryAt i < len then ρ.val (v.entry (lay.entryAt i)) else 0 := by
  have hs := tensorBelow_shape v hv v.vars len l h
  have e1 : (l.map fun w => ρ.val ((lay.onTable w).entry i)) =
      l.map fun w => if lay.entryAt i < 2 ^ v.vars then ρ.val (w.entry (lay.entryAt i)) else 0 :=
    List.map_congr_left fun w hw => by
      rw [entry_onTable ρ lay w (hs w hw).2 (by rw [(hs w hw).1]; exact hb) i hi, (hs w hw).1]
  rw [e1]
  by_cases h1 : lay.entryAt i < 2 ^ v.vars
  · simp only [if_pos h1]
    rw [sum_tensorBelow ρ v hv v.vars len l h, Nat.mod_eq_of_lt h1]
  · simp only [if_neg h1]
    rw [if_neg fun h2 => h1 (lt_of_lt_of_le h2 hlen)]
    simp

/-- The same for a tensor on c variables whose parts are placed at the aligned block of 2 ^ c
entries that begins at entry m * 2 ^ c. -/
theorem sum_laid_placed (lay : VectorLay) (v : Tensor) (hv : v.denseVars = []) (len m : ℕ)
    (l : List Tensor) (h : tensorBelow v 0 v.vars len = some l)
    (hb : v.vars ≤ lay.bits) (hm : m < 2 ^ (lay.bits - v.vars)) (i : ℕ) (hi : i < 2 ^ lay.bits)
    (he : lay.entryAt i < 2 ^ lay.bits) :
    ((l.map fun w => w.insertChoice v.vars (lay.bits - v.vars) m).map fun w =>
        ρ.val ((lay.onTable w).entry i)).sum =
      if lay.entryAt i / 2 ^ v.vars = m ∧ lay.entryAt i % 2 ^ v.vars < len then
        ρ.val (v.entry (lay.entryAt i % 2 ^ v.vars)) else 0 := by
  have hs := tensorBelow_shape v hv v.vars len l h
  have hq : lay.entryAt i / 2 ^ v.vars < 2 ^ (lay.bits - v.vars) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hb]
    exact he
  rw [List.map_map]
  have e1 : (l.map ((fun w => ρ.val ((lay.onTable w).entry i)) ∘
      fun w => w.insertChoice v.vars (lay.bits - v.vars) m)) =
      l.map fun w => (if lay.entryAt i / 2 ^ v.vars = m then (1 : K) else 0) *
        ρ.val (w.entry (lay.entryAt i % 2 ^ v.vars)) :=
    List.map_congr_left fun w hw => by
      have hw1 := (hs w hw).1
      have hw2 := (hs w hw).2
      have hd := insertChoice_plain w hw2 v.vars (lay.bits - v.vars) m
      have hvars : (w.insertChoice v.vars (lay.bits - v.vars) m).vars = lay.bits := by
        rw [vars_insertChoice w _ _ _ (by rw [hw1]), hw1, Nat.add_sub_cancel' hb]
      show ρ.val ((lay.onTable (w.insertChoice v.vars (lay.bits - v.vars) m)).entry i) = _
      rw [entry_onTable ρ lay _ hd (by rw [hvars]) i hi, hvars, if_pos he,
        Tensor.entry_insertChoice ρ w v.vars (lay.bits - v.vars) m _ (by rw [hw1]),
        Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hm]
      have hmod : ρ.val (w.entry (unshift v.vars (lay.bits - v.vars) (lay.entryAt i))) =
          ρ.val (w.entry (lay.entryAt i % 2 ^ v.vars)) := by
        rw [← entry_mod ρ w hw2 (unshift v.vars (lay.bits - v.vars) (lay.entryAt i)), hw1,
          unshift_mod]
      rw [hmod]
  rw [e1, List.sum_map_mul_left, sum_tensorBelow ρ v hv v.vars len l h, Nat.mod_mod]
  by_cases h1 : lay.entryAt i / 2 ^ v.vars = m
  · by_cases h2 : lay.entryAt i % 2 ^ v.vars < len
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, one_mul]
    · have hn : ¬ (lay.entryAt i / 2 ^ v.vars = m ∧ lay.entryAt i % 2 ^ v.vars < len) :=
        fun hh => h2 hh.2
      rw [if_neg h2, if_neg hn, mul_zero]
  · have hn : ¬ (lay.entryAt i / 2 ^ v.vars = m ∧ lay.entryAt i % 2 ^ v.vars < len) :=
      fun hh => h1 hh.1
    rw [if_neg h1, if_neg hn, zero_mul]

end

/-! ## Rows made of placed tensors -/

/-- Tensors on a vector's entries, added to a row as terms on the main table of the oracle message
number o: the row's coefficients on that table grow by the sum of the placed tensors' entries. -/
theorem coefAt_addLaid (o : ℕ) (lay : VectorLay) : ∀ (l : List Tensor) (row : Row) (o' : ℕ)
    (part : Part) (i : ℕ),
    coefAt (addLaid row o lay l) o' part i = coefAt row o' part i +
      if o == o' && Part.main == part then (l.map fun t => readE ((lay.onTable t).entry i)).sum
      else 0
  | [], row, o', part, i => by
    show coefAt row o' part i = _
    cases (o == o' && Part.main == part) <;> simp
  | t :: l, row, o', part, i => by
    show coefAt (addLaid (row.add o .main (lay.onTable t)) o lay l) o' part i = _
    rw [coefAt_addLaid o lay l, coefAt_add, List.map_cons, List.sum_cons]
    cases (o == o' && Part.main == part) <;> simp [add_assoc]

/-- Adding placed tensors changes neither the target nor the kind of a row. -/
theorem addLaid_keeps (o : ℕ) (lay : VectorLay) : ∀ (l : List Tensor) (row : Row),
    (addLaid row o lay l).target = row.target ∧ (addLaid row o lay l).kind = row.kind
  | [], _ => ⟨rfl, rfl⟩
  | t :: l, row => addLaid_keeps o lay l (row.add o .main (lay.onTable t))

/-- How a folded row is arranged in its oracle message: entry e is in row e / 2 ^ aP at place
e % 2 ^ aP. -/
def Sz.layU (S : Sz) : VectorLay := ⟨S.P.aR, S.P.aP, true⟩

/-- The entry that is at row r, place p. -/
theorem entryAt_layU (S : Sz) (r p : ℕ) (hr : r < 2 ^ S.P.aR) :
    S.layU.entryAt (r + 2 ^ S.P.aR * p) = r * 2 ^ S.P.aP + p := by
  rw [entryAt_eq, if_pos (show S.layU.rowsHigh = true from rfl)]
  show (r + 2 ^ S.P.aR * p) / 2 ^ S.P.aR + (r + 2 ^ S.P.aR * p) % 2 ^ S.P.aR * 2 ^ S.P.aP = _
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.add_comm]

/-- Row r, place p is within a table of 2 ^ a rows of 2 ^ b places, by index and by entry. -/
theorem within_table (a b r p : ℕ) (hr : r < 2 ^ a) (hp : p < 2 ^ b) :
    r + 2 ^ a * p < 2 ^ (a + b) ∧ r * 2 ^ b + p < 2 ^ (a + b) := by
  refine ⟨?_, ?_⟩
  · calc r + 2 ^ a * p < 2 ^ a + 2 ^ a * p := Nat.add_lt_add_right hr _
      _ = 2 ^ a * (p + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (a + b) := (Nat.pow_add 2 _ _).symm
  · calc r * 2 ^ b + p < r * 2 ^ b + 2 ^ b := Nat.add_lt_add_left hp _
      _ = (r + 1) * 2 ^ b := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul_right _ hr
      _ = 2 ^ (a + b) := (Nat.pow_add 2 _ _).symm

/-! ## The equality row -/

/-- What the program's equality row is made of. -/
theorem linkEqualityRow_inv (Λ : Params.LinkShape) (phi : List E) (u0 u1 : FoldedRow) (cut : ℕ)
    (row : Row) (h : linkEqualityRow Λ phi u0 u1 cut = some row) :
    phi.length = Λ.entryBits ∧ ∃ plus minus,
      tensorBelow (Tensor.eq phi oneE) 0 Λ.entryBits cut = some plus ∧
      tensorBelow (Tensor.eq phi (negE oneE)) 0 Λ.entryBits cut = some minus ∧
      row = u1.addAll (u0.addAll {} plus) minus := by
  unfold linkEqualityRow at h
  by_cases hl : phi.length = Λ.entryBits
  · cases hp : tensorBelow (Tensor.eq phi oneE) 0 Λ.entryBits cut with
    | none => simp [hl, hp] at h
    | some plus =>
      cases hm : tensorBelow (Tensor.eq phi (negE oneE)) 0 Λ.entryBits cut with
      | none => simp [hl, hp, hm] at h
      | some minus =>
        simp [hl, hp, hm] at h
        exact ⟨hl, plus, minus, rfl, rfl, h.symm⟩
  · simp [hl] at h

/-- The program's equality row, in the field. On the first folded row's oracle message it has
the coefficients of `Sz.eqC` at the point phi, on the second's their negatives. -/
theorem coefAt_eqRow (S : Sz) (Λ : Params.LinkShape) (phi : List E) (u0 u1 : FoldedRow) (row : Row)
    (hb : Λ.entryBits = S.P.aPhi) (hfit : S.P.aPhi ≤ S.P.aR + S.P.aP) (h0 : u0.lay = S.layU)
    (h1 : u1.lay = S.layU) (hne : u0.oracle ≠ u1.oracle)
    (h : linkEqualityRow Λ phi u0 u1 S.P.cut = some row) (r p : ℕ) (hr : r < 2 ^ S.P.aR)
    (hp : p < 2 ^ S.P.aP) :
    coefAt row u0.oracle .main (r + 2 ^ S.P.aR * p) =
        S.eqC (readP S.P.aPhi phi) (r * 2 ^ S.P.aP + p) ∧
      coefAt row u1.oracle .main (r + 2 ^ S.P.aR * p) =
        -S.eqC (readP S.P.aPhi phi) (r * 2 ^ S.P.aP + p) := by
  obtain ⟨hl, plus, minus, hplus, hminus, rfl⟩ := linkEqualityRow_inv Λ phi u0 u1 _ row h
  obtain ⟨hi, -⟩ := within_table S.P.aR S.P.aP r p hr hp
  have hlen : phi.length = S.P.aPhi := hl.trans hb
  have hcut : S.P.cut ≤ 2 ^ S.P.aPhi := le_trans (Nat.sub_le _ _) (le_two_pow_clog S.P.T.l)
  -- the sum of the placed parts of the equality vector with the factor s in front
  have key : ∀ (s : E) (l : List Tensor), tensorBelow (Tensor.eq phi s) 0 Λ.entryBits S.P.cut =
      some l → (l.map fun t => readE ((S.layU.onTable t).entry (r + 2 ^ S.P.aR * p))).sum =
        readE s * S.eqC (readP S.P.aPhi phi) (r * 2 ^ S.P.aP + p) := by
    intro s l hs
    have hv : (Tensor.eq phi s).vars = S.P.aPhi := by
      show (phi.map _).length = _
      rw [List.length_map, hlen]
    have h2 := sum_laid_below rdE S.layU (Tensor.eq phi s) rfl S.P.cut l
      (by rw [hv, ← hb]; exact hs) (by rw [hv]; exact hcut) (by rw [hv]; exact hfit) _ hi
    simp only [rdE_val] at h2
    rw [h2, entryAt_layU S r p hr, readE_eq, hlen]
    unfold Sz.eqC
    by_cases h3 : r * 2 ^ S.P.aP + p < S.P.cut
    · rw [if_pos h3, if_pos h3]
      rfl
    · rw [if_neg h3, if_neg h3, mul_zero]
  have hn1 : (u1.oracle == u0.oracle) = false := beq_eq_false_iff_ne.2 (Ne.symm hne)
  have hn0 : (u0.oracle == u1.oracle) = false := beq_eq_false_iff_ne.2 hne
  unfold FoldedRow.addAll
  rw [coefAt_addLaid, coefAt_addLaid, coefAt_empty, coefAt_addLaid, coefAt_addLaid, coefAt_empty,
    h0, h1, key _ _ hplus, key _ _ hminus, readE_one, readE_neg, readE_one]
  simp [hn0, hn1]

/-- The program's equality row has the target 0 and is a plain row. -/
theorem eqRow_target (Λ : Params.LinkShape) (phi : List E) (u0 u1 : FoldedRow) (cut : ℕ)
    (row : Row) (h : linkEqualityRow Λ phi u0 u1 cut = some row) :
    readE row.target = 0 ∧ row.kind = .plain := by
  obtain ⟨-, plus, minus, -, -, rfl⟩ := linkEqualityRow_inv Λ phi u0 u1 _ row h
  unfold FoldedRow.addAll
  obtain ⟨a1, a2⟩ := addLaid_keeps u1.oracle u1.lay minus (addLaid {} u0.oracle u0.lay plus)
  obtain ⟨b1, b2⟩ := addLaid_keeps u0.oracle u0.lay plus {}
  rw [a1, a2, b1, b2]
  exact ⟨readE_zero, rfl⟩

/-! ## The row of a drawn column -/

/-- What the program's row of a drawn column is made of. -/
theorem foldeqColumnRow_inv (Sf : Params.FoldeqShape) (x : ℕ) (y : E) (u : FoldedRow) (row : Row)
    (h : foldeqColumnRow Sf x y u = some row) :
    ∃ onMessage onTail,
      tensorBelow (Tensor.product ((generatorAt Sf.index.code x).f.take Sf.index.code.logEll)
        (OnBytes.ofF (generatorAt Sf.index.code x).messageScale)) 0 Sf.index.code.logEll
        Sf.index.code.ell = some onMessage ∧
      (if Sf.index.code.r == 0 then some []
        else tensorBelow (Tensor.product ((generatorAt Sf.index.code x).f.take Sf.index.code.logR)
          (OnBytes.ofF (generatorAt Sf.index.code x).tailScale)) 0 Sf.index.code.logR
          Sf.index.code.r) = some onTail ∧
      row = { u.addAll (u.addAll {} onMessage) (onTail.map fun t =>
        t.insertChoice Sf.index.code.logR (u.lay.bits - Sf.index.code.logR)
          (Sf.tailFirst / 2 ^ Sf.index.code.logR)) with kind := .generator, target := y } := by
  unfold foldeqColumnRow at h
  cases hm : tensorBelow (Tensor.product ((generatorAt Sf.index.code x).f.take
      Sf.index.code.logEll) (OnBytes.ofF (generatorAt Sf.index.code x).messageScale)) 0
      Sf.index.code.logEll Sf.index.code.ell with
  | none => simp [hm] at h
  | some onMessage =>
    by_cases hr : (Sf.index.code.r == 0) = true
    · simp [hm, hr] at h
      exact ⟨onMessage, [], rfl, by rw [if_pos hr], h.symm⟩
    · cases ht : tensorBelow (Tensor.product ((generatorAt Sf.index.code x).f.take
          Sf.index.code.logR) (OnBytes.ofF (generatorAt Sf.index.code x).tailScale)) 0
          Sf.index.code.logR Sf.index.code.r with
      | none => simp [hm, hr, ht] at h
      | some onTail =>
        simp [hm, hr, ht] at h
        exact ⟨onMessage, onTail, rfl, by rw [if_neg hr], h.symm⟩

/-- The first k of a code's factors, for k that spells at most the code's dimension. -/
theorem take_factors (c : OnBytes.Code) (x k : ℕ) (hk : k ≤ c.logDim) :
    (generatorAt c x).f.take k = squaresOf k (codePoint c.logN x) := by
  rw [generatorAt_f, take_squaresOf, Nat.min_eq_left hk]

/-- The message's part of the row of a drawn column, placed on a table: at the entry e of the folded
row, if e is an entry of the message, the point to the power r + e. -/
theorem msg_part (c : OnBytes.Code) (x : ℕ) (lay : VectorLay) (l : List Tensor)
    (h : tensorBelow (Tensor.product ((generatorAt c x).f.take c.logEll)
      (OnBytes.ofF (generatorAt c x).messageScale)) 0 c.logEll c.ell = some l)
    (hb : c.logEll ≤ lay.bits) (hell : 0 < c.ell) (i : ℕ) (hi : i < 2 ^ lay.bits) :
    (l.map fun t => readE ((lay.onTable t).entry i)).sum =
      if lay.entryAt i < c.ell then
        algebraMap GF GE (toF (codePoint c.logN x) ^ (c.r + lay.entryAt i)) else 0 := by
  have hk : c.logEll ≤ c.logDim := ceilLog2_le _ _ (ell_le_logDim c)
  have hle : c.ell ≤ 2 ^ c.logEll := le_two_pow_ceilLog2 c.ell
  rw [take_factors c x _ hk] at h
  have hv : (Tensor.product (squaresOf c.logEll (codePoint c.logN x))
      (OnBytes.ofF (generatorAt c x).messageScale)).vars = c.logEll := by
    show ((squaresOf c.logEll (codePoint c.logN x)).map _).length = _
    rw [List.length_map, length_squaresOf]
  have h2 := sum_laid_below rdE lay _ rfl c.ell l (by rw [hv]; exact h) (by rw [hv]; exact hle)
    (by rw [hv]; exact hb) i hi
  simp only [rdE_val] at h2
  rw [h2]
  by_cases h3 : lay.entryAt i < c.ell
  · rw [if_pos h3, if_pos h3, readE_product, readE_ofF, toF_messageScale c x hell,
      toF_productIndex_squares, Nat.mod_eq_of_lt (lt_of_lt_of_le h3 hle), ← map_mul, ← pow_add]
  · rw [if_neg h3, if_neg h3]

/-- The tail's part of the row of a drawn column, put at the aligned block number m and placed on a
table: at the entry e of the folded row, if e is in that block and e % 2 ^ logR is an entry of the
tail, the point to that power. -/
theorem tail_part (c : OnBytes.Code) (x : ℕ) (lay : VectorLay) (l : List Tensor) (m : ℕ)
    (h : tensorBelow (Tensor.product ((generatorAt c x).f.take c.logR)
      (OnBytes.ofF (generatorAt c x).tailScale)) 0 c.logR c.r = some l)
    (hb : c.logR ≤ lay.bits) (hm : m < 2 ^ (lay.bits - c.logR)) (i : ℕ) (hi : i < 2 ^ lay.bits)
    (he : lay.entryAt i < 2 ^ lay.bits) :
    ((l.map fun t => t.insertChoice c.logR (lay.bits - c.logR) m).map fun t =>
        readE ((lay.onTable t).entry i)).sum =
      if lay.entryAt i / 2 ^ c.logR = m ∧ lay.entryAt i % 2 ^ c.logR < c.r then
        algebraMap GF GE (toF (codePoint c.logN x) ^ (lay.entryAt i % 2 ^ c.logR)) else 0 := by
  have hk : c.logR ≤ c.logDim := ceilLog2_le _ _ (r_le_logDim c)
  rw [take_factors c x _ hk] at h
  have hv : (Tensor.product (squaresOf c.logR (codePoint c.logN x))
      (OnBytes.ofF (generatorAt c x).tailScale)).vars = c.logR := by
    show ((squaresOf c.logR (codePoint c.logN x)).map _).length = _
    rw [List.length_map, length_squaresOf]
  have h2 := sum_laid_placed rdE lay _ rfl c.r m l (by rw [hv]; exact h) (by rw [hv]; exact hb)
    (by rw [hv]; exact hm) i hi he
  simp only [rdE_val, hv] at h2
  rw [h2, readE_product, readE_ofF, toF_tailScale, map_one, one_mul, toF_productIndex_squares,
    Nat.mod_mod]

/-- An entry is among the first r entries of the aligned block number Q of C entries exactly if it
is at least Q * C and less than r further. -/
theorem block_iff (C Q r e : ℕ) (hC : 0 < C) (hr : r ≤ C) :
    (e / C = Q ∧ e % C < r) ↔ (Q * C ≤ e ∧ e - Q * C < r) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := Nat.div_add_mod e C
    rw [h1, Nat.mul_comm] at h3
    omega
  · rintro ⟨h1, h2⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
    have hd : d < C := by omega
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hC, Nat.div_eq_of_lt hd, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
    exact ⟨rfl, by omega⟩

/-- The place of an entry in its aligned block. -/
theorem block_mod (C Q e : ℕ) (h : e / C = Q) : e % C = e - Q * C := by
  have h3 := Nat.div_add_mod e C
  rw [h, Nat.mul_comm] at h3
  omega

/-- The program's row of a drawn column, in the field. On the folded row's oracle message it has
the coefficients of `Sz.colC` at the drawn location. -/
theorem coefAt_colRow (S : Sz) (Sf : Params.FoldeqShape) (x : S.Pos) (y : E) (u : FoldedRow)
    (row : Row) (hc : codeOf Sf.index.code = S.P.T) (hl2 : S.P.C.l = 2 ^ S.P.aP)
    (ha : S.P.T.a ≤ 32) (hell : 0 < S.P.T.l) (hu : u.lay = S.layU)
    (h : foldeqColumnRow Sf x.val y u = some row) (r p : ℕ) (hr : r < 2 ^ S.P.aR)
    (hp : p < 2 ^ S.P.aP) :
    coefAt row u.oracle .main (r + 2 ^ S.P.aR * p) = S.colC x (r * 2 ^ S.P.aP + p) := by
  obtain ⟨onMessage, onTail, hM, hT, rfl⟩ := foldeqColumnRow_inv Sf x.val y u row h
  obtain ⟨hi, he⟩ := within_table S.P.aR S.P.aP r p hr hp
  have ca : Sf.index.code.logN = S.P.T.a := congrArg (·.a) hc
  have cl : Sf.index.code.ell = S.P.T.l := congrArg (·.l) hc
  have cr : Sf.index.code.r = S.P.T.r := congrArg (·.r) hc
  have hz : toF (codePoint Sf.index.code.logN x.val) = ptOf S.P.T.a x := by
    rw [ca]
    exact toF_codePoint S.P.T.a x.val ha x.isLt
  have hRl : S.P.R * S.P.C.l ≤ 2 ^ (S.P.aR + S.P.aP) := by
    rw [Nat.pow_add, hl2]
    exact Nat.mul_le_mul_right _ (le_two_pow_clog S.P.R)
  have hTl : S.P.T.l ≤ 2 ^ (S.P.aR + S.P.aP) := le_trans S.fitM hRl
  have hTt : S.P.t0 + S.P.T.r ≤ 2 ^ (S.P.aR + S.P.aP) := le_trans S.fitT hRl
  have ht0 := le_t0 S.P
  -- where the tail begins
  have hq : Sf.tailFirst = S.P.t0 := by
    show (Sf.index.code.ell + 2 ^ ceilLog2 Sf.index.code.r - 1) / 2 ^ ceilLog2 Sf.index.code.r *
      2 ^ ceilLog2 Sf.index.code.r = _
    rw [cl, cr]
    rfl
  have hlogR : Sf.index.code.logR = Fmt.M2.clog S.P.T.r := by
    show ceilLog2 Sf.index.code.r = _
    rw [cr]
    rfl
  have hQ : S.P.t0 = (S.P.T.l + 2 ^ Fmt.M2.clog S.P.T.r - 1) / 2 ^ Fmt.M2.clog S.P.T.r *
      2 ^ Fmt.M2.clog S.P.T.r := rfl
  have hmul : S.P.t0 / 2 ^ Fmt.M2.clog S.P.T.r * 2 ^ Fmt.M2.clog S.P.T.r = S.P.t0 := by
    conv_lhs => rw [hQ, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    exact hQ.symm
  have hrle : S.P.T.r ≤ 2 ^ Fmt.M2.clog S.P.T.r := le_two_pow_clog S.P.T.r
  show coefAt (u.addAll (u.addAll {} onMessage) _) u.oracle .main _ = _
  unfold FoldedRow.addAll
  rw [coefAt_addLaid, coefAt_addLaid, coefAt_empty, hu, zero_add]
  simp only [beq_self_eq_true, Bool.and_self, if_true]
  rw [msg_part Sf.index.code x.val S.layU onMessage hM
    (ceilLog2_le _ _ (by rw [cl]; exact hTl)) (by rw [cl]; exact hell) _ hi]
  -- the tail's part
  have htail : ((onTail.map fun t => t.insertChoice Sf.index.code.logR
      (S.layU.bits - Sf.index.code.logR) (Sf.tailFirst / 2 ^ Sf.index.code.logR)).map fun t =>
        readE ((S.layU.onTable t).entry (r + 2 ^ S.P.aR * p))).sum =
      if S.P.t0 ≤ r * 2 ^ S.P.aP + p ∧ r * 2 ^ S.P.aP + p - S.P.t0 < S.P.T.r then
        algebraMap GF GE (ptOf S.P.T.a x ^ (r * 2 ^ S.P.aP + p - S.P.t0)) else 0 := by
    by_cases hr0 : (Sf.index.code.r == 0) = true
    · rw [if_pos hr0] at hT
      obtain rfl := Option.some.inj hT
      have hr0' : S.P.T.r = 0 := cr ▸ beq_iff_eq.1 hr0
      rw [if_neg (by rw [hr0']; omega)]
      rfl
    · rw [if_neg hr0] at hT
      have hrpos : 0 < S.P.T.r := by
        rw [← cr]
        exact Nat.pos_of_ne_zero fun h0 => hr0 (beq_iff_eq.2 h0)
      have hbR : Sf.index.code.logR ≤ S.layU.bits :=
        ceilLog2_le _ _ (by rw [cr]; exact le_trans (Nat.le_add_left _ _) hTt)
      have hm : Sf.tailFirst / 2 ^ Sf.index.code.logR < 2 ^ (S.layU.bits - Sf.index.code.logR) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hbR, hq]
        exact lt_of_lt_of_le (by omega) hTt
      rw [tail_part Sf.index.code x.val S.layU onTail _ hT hbR hm _ hi
        (by rw [entryAt_layU S r p hr]; exact he), entryAt_layU S r p hr, hz, hq, hlogR, cr]
      have hiff := block_iff (2 ^ Fmt.M2.clog S.P.T.r) (S.P.t0 / 2 ^ Fmt.M2.clog S.P.T.r) S.P.T.r
        (r * 2 ^ S.P.aP + p) (Nat.two_pow_pos _) hrle
      rw [hmul] at hiff
      by_cases h5 : (r * 2 ^ S.P.aP + p) / 2 ^ Fmt.M2.clog S.P.T.r =
          S.P.t0 / 2 ^ Fmt.M2.clog S.P.T.r ∧
          (r * 2 ^ S.P.aP + p) % 2 ^ Fmt.M2.clog S.P.T.r < S.P.T.r
      · rw [if_pos h5, if_pos (hiff.1 h5), block_mod _ _ _ h5.1, hmul]
      · rw [if_neg h5, if_neg fun h6 => h5 (hiff.2 h6)]
  rw [htail, entryAt_layU S r p hr, hz, cl, cr]
  unfold Sz.colC
  generalize r * 2 ^ S.P.aP + p = e
  by_cases h1 : e < S.P.T.l
  · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, if_neg h1, zero_add]
    by_cases h2 : S.P.t0 ≤ e
    · rw [if_pos h2]
      by_cases h3 : e - S.P.t0 < S.P.T.r
      · rw [if_pos ⟨h2, h3⟩, if_pos h3]
      · rw [if_neg fun h4 => h3 h4.2, if_neg h3]
    · rw [if_neg fun h4 => h2 h4.1, if_neg h2]

/-- The program's row of a drawn column has the given target and is a generator row. -/
theorem colRow_target (Sf : Params.FoldeqShape) (x : ℕ) (y : E) (u : FoldedRow) (row : Row)
    (h : foldeqColumnRow Sf x y u = some row) : row.target = y ∧ row.kind = .generator := by
  obtain ⟨_, _, -, -, rfl⟩ := foldeqColumnRow_inv Sf x y u row h
  exact ⟨rfl, rfl⟩

/-- The program's row of a drawn column is 0 on every table but the main table of the folded row's
oracle message. -/
theorem coefAt_colRow_else (Sf : Params.FoldeqShape) (x : ℕ) (y : E) (u : FoldedRow) (row : Row)
    (h : foldeqColumnRow Sf x y u = some row) (o : ℕ) (part : Part) (i : ℕ)
    (ho : ¬ (o = u.oracle ∧ part = .main)) : coefAt row o part i = 0 := by
  obtain ⟨onMessage, onTail, -, -, rfl⟩ := foldeqColumnRow_inv Sf x y u row h
  have hf : (u.oracle == o && Part.main == part) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases h1 : o = u.oracle
    · exact Or.inr (beq_eq_false_iff_ne.2 fun h2 => ho ⟨h1, h2.symm⟩)
    · exact Or.inl (beq_eq_false_iff_ne.2 fun h2 => h1 h2.symm)
  show coefAt (u.addAll (u.addAll {} onMessage) _) o part i = 0
  unfold FoldedRow.addAll
  rw [coefAt_addLaid, coefAt_addLaid, coefAt_empty, hf]
  simp

/-- The program's equality row is 0 on every table but the main tables of the two folded rows'
oracle messages. -/
theorem coefAt_eqRow_else (Λ : Params.LinkShape) (phi : List E) (u0 u1 : FoldedRow) (cut : ℕ)
    (row : Row) (h : linkEqualityRow Λ phi u0 u1 cut = some row) (o : ℕ) (part : Part) (i : ℕ)
    (ho : ¬ ((o = u0.oracle ∨ o = u1.oracle) ∧ part = .main)) : coefAt row o part i = 0 := by
  obtain ⟨-, plus, minus, -, -, rfl⟩ := linkEqualityRow_inv Λ phi u0 u1 _ row h
  have hf : ∀ u : FoldedRow, (u = u0 ∨ u = u1) → (u.oracle == o && Part.main == part) = false := by
    intro u hu
    rw [Bool.and_eq_false_iff]
    by_cases h1 : o = u.oracle
    · refine Or.inr (beq_eq_false_iff_ne.2 fun h2 => ho ⟨?_, h2.symm⟩)
      rcases hu with rfl | rfl
      · exact Or.inl h1
      · exact Or.inr h1
    · exact Or.inl (beq_eq_false_iff_ne.2 fun h2 => h1 h2.symm)
  unfold FoldedRow.addAll
  rw [coefAt_addLaid, coefAt_addLaid, coefAt_empty, hf u0 (Or.inl rfl), hf u1 (Or.inr rfl)]
  simp

/-! ## The fold of an opened column -/

/-- A sum that the program makes step by step, each step adding a word times an element. -/
theorem readE_foldl_maddS (f : ℕ → F) (g : ℕ → E) : ∀ (n : ℕ) (a : E),
    readE ((List.range n).foldl (fun s r => maddS s (f r) (g r)) a) =
      readE a + ∑ r ∈ Finset.range n, readE (g r) * algebraMap GF GE (toF (f r))
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, readE_maddS,
      readE_foldl_maddS f g n a, Finset.sum_range_succ, add_assoc, Algebra.smul_def, mul_comm]

/-- The program's fold of an opened column: its words under the weights of the point gamma. -/
theorem readE_foldeqSymbol (gamma : List E) (col : Array F) :
    readE (foldeqSymbol (foldeqWeights gamma) col) =
      ∑ b ∈ Finset.range (2 ^ gamma.length),
        eqW gamma.length (readL gamma) b * algebraMap GF GE (toF (col.getD b 0)) := by
  unfold foldeqSymbol foldeqWeights
  rw [readE_foldl_maddS (fun r => col.getD r 0) (fun r => (eqTable gamma).getD r zeroE),
    readE_zero, zero_add, size_eqTable]
  refine Finset.sum_congr rfl fun b hb => ?_
  have h1 := readV_eqTable gamma b
  unfold readV at h1
  rw [h1, if_pos (Finset.mem_range.1 hb)]

/-- The library's fold of a symbol read in the first table, as a sum over the rows' numbers. -/
theorem foldSym₀_closed (S : Sz) (z : ℕ → GE) (s : Run.PQ.SgX) :
    S.lk.foldSym₀ (fun t => z t.val) (some (.inl (.inl s))) =
      ∑ b ∈ Finset.range (2 ^ S.P.v), eqW S.P.v z b * algebraMap GF GE (toF (s.2.getD b 0)) := by
  rw [sum_range_cube]
  show (∑ r, Alg.eqk (fun t : Fin S.P.v => z t.val) r * S.lk.up s r) = _
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eqW_rowNo]

/-- The same for a symbol read in the copy. -/
theorem foldSym₁_closed (S : Sz) (z : ℕ → GE) (s : Run.PQ.SgX) :
    S.lk.foldSym₁ (fun t => z t.val) (some (.inl (.inr s))) =
      ∑ b ∈ Finset.range (2 ^ S.P.v), eqW S.P.v z b * algebraMap GF GE (toF (s.2.getD b 0)) := by
  rw [sum_range_cube]
  show (∑ r, Alg.eqk (fun t : Fin S.P.v => z t.val) r * S.lk.up s r) = _
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eqW_rowNo]

/-! ## A sample row -/

/-- The program's sample row of a folded row's oracle message, in the field. The message has R
main rows over the extension field, no mask rows and one answer. The row has the coefficients of
`Sz.smpC` at the seed. -/
theorem coefAt_smpRow (S : Sz) (codes : Codes) (s : OracleShape) (o : ℕ) (z : List E) (beta : E)
    (row : Row) (hrows : s.mainRows = S.P.R) (hdeg : s.mainDeg = 3) (hmask : s.maskRows = 0)
    (hans : s.answers = 1) (hell : (codes.base.getD s.code default).ell = S.P.C.l)
    (hl2 : S.P.C.l = 2 ^ S.P.aP) (hz : z.length = S.P.aR + S.P.aP)
    (h : Send.form codes s o ⟨z, beta⟩ 0 = some row) (β : GEˣ) (hβ : β.val = readE beta) (i : ℕ)
    (hi : i < 2 ^ (S.P.aR + S.P.aP)) :
    coefAt row o .main i = S.smpC (readP (S.P.aR + S.P.aP) z, β) i := by
  -- the message's cube
  have hM : (Send.cube codes s).hasMain = true := by
    rw [cube_hasMain_eq, hrows]
    exact decide_eq_true S.hR
  have hK : (Send.cube codes s).hasMask = false := by
    rw [cube_hasMask_eq, hmask]
    rfl
  have hRB : (Send.cube codes s).mainRowBits = S.P.aR := by
    rw [cube_mainRowBits_eq, hM, if_pos rfl, hrows]
    rfl
  have hMB : (Send.cube codes s).mainBits = S.P.aR + S.P.aP := by
    rw [cube_mainBits_eq, hM, if_pos rfl, hRB]
    show S.P.aR + ceilLog2 (codes.base.getD s.code default).ell = _
    rw [hell, hl2, ceilLog2_two_pow]
  have hKB : (Send.cube codes s).maskBits = 0 := by
    rw [cube_maskBits_eq, hK]
    rfl
  have hB : (Send.cube codes s).bits = S.P.aR + S.P.aP := by
    rw [cube_bits_eq, hM, hK, hMB, hKB]
    rfl
  have hPP : padPart (Send.cube codes s) = .main := by
    unfold padPart
    rw [hK]
    rfl
  have hPI : padIndex codes s = S.padIdx := by
    unfold padIndex padLen Sz.padIdx
    rw [hK]
    show (s.mainRows - 1) + ((codes.base.getD s.code default).ell - 1) *
      2 ^ (Send.cube codes s).mainRowBits = _
    rw [hrows, hell, hRB, Nat.mul_comm]
  have hP : hasPart (Send.cube codes s) .main = true := hM
  rw [coefAt_form_one codes s o ⟨z, beta⟩ row h hans (by rw [hK, hdeg]; rfl) (by rw [hPP]; exact hP)
    .main i, hPP, hPI, hP, if_pos rfl,
    tableW_eq_eqW codes s z .main i (by rw [hz, hB]) hP (by
      show i < 2 ^ (Send.cube codes s).mainBits
      rw [hMB]
      exact hi), hB]
  unfold Sz.smpC cubeIdx
  rw [hK]
  by_cases h1 : i = S.padIdx
  · rw [if_pos ⟨rfl, h1⟩, if_pos h1, hβ]
  · rw [if_neg fun h2 => h1 h2.2, if_neg h1]
    rw [Bool.and_false, Bool.false_and, if_neg Bool.false_ne_true, Nat.zero_add]
    rfl

/-! ## The rows hold no written-out factor -/

/-- A tensor without a written-out factor has none when it is placed on a table. -/
theorem onTable_plain (lay : VectorLay) (v : Tensor) (hv : v.denseVars = []) :
    (lay.onTable v).denseVars = [] := (onTable_plain_eq lay v hv).2.1

/-- The terms and the forms of a row to which placed tensors were added. -/
theorem addLaid_terms (o : ℕ) (lay : VectorLay) : ∀ (l : List Tensor) (row : Row),
    (addLaid row o lay l).terms.toList =
        row.terms.toList ++ l.map (fun t => (⟨o, .main, lay.onTable t⟩ : Term)) ∧
      (addLaid row o lay l).forms = row.forms
  | [], row => ⟨(List.append_nil _).symm, rfl⟩
  | t :: l, row => by
    obtain ⟨h1, h2⟩ := addLaid_terms o lay l (row.add o .main (lay.onTable t))
    refine ⟨?_, h2⟩
    show (addLaid (row.add o .main (lay.onTable t)) o lay l).terms.toList = _
    rw [h1]
    show (row.terms.push _).toList ++ _ = _
    rw [Array.toList_push, List.append_assoc]
    rfl

/-- Placed tensors without a written-out factor leave a row without one. -/
theorem addLaid_plain (o : ℕ) (lay : VectorLay) (l : List Tensor) (row : Row)
    (hl : ∀ t ∈ l, t.denseVars = []) (hr : ∀ t ∈ row.terms.toList, t.v.denseVars = []) :
    ∀ t ∈ (addLaid row o lay l).terms.toList, t.v.denseVars = [] := by
  intro t ht
  rw [(addLaid_terms o lay l row).1] at ht
  rcases List.mem_append.1 ht with h1 | h1
  · exact hr t h1
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h1
    exact onTable_plain lay w (hl w hw)

/-- Placed tensors are terms on main tables. -/
theorem addLaid_main (o : ℕ) (lay : VectorLay) (l : List Tensor) (row : Row)
    (hr : ∀ t ∈ row.terms.toList, t.part = .main) :
    ∀ t ∈ (addLaid row o lay l).terms.toList, t.part = .main := by
  intro t ht
  rw [(addLaid_terms o lay l row).1] at ht
  rcases List.mem_append.1 ht with h1 | h1
  · exact hr t h1
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 h1
    rfl

/-- The program's equality row has no term on a mask table. -/
theorem eqRow_main (Λ : Params.LinkShape) (phi : List E) (u0 u1 : FoldedRow) (cut : ℕ) (row : Row)
    (h : linkEqualityRow Λ phi u0 u1 cut = some row) : ∀ t ∈ row.terms.toList, t.part = .main := by
  obtain ⟨-, plus, minus, -, -, rfl⟩ := linkEqualityRow_inv Λ phi u0 u1 _ row h
  unfold FoldedRow.addAll
  exact addLaid_main _ _ _ _ (addLaid_main _ _ _ _ fun t ht => by cases ht)

/-- The program's row of a drawn column has no term on a mask table. -/
theorem colRow_main (Sf : Params.FoldeqShape) (x : ℕ) (y : E) (u : FoldedRow) (row : Row)
    (h : foldeqColumnRow Sf x y u = some row) : ∀ t ∈ row.terms.toList, t.part = .main := by
  obtain ⟨onMessage, onTail, -, -, rfl⟩ := foldeqColumnRow_inv Sf x y u row h
  show ∀ t ∈ (u.addAll (u.addAll {} onMessage) _).terms.toList, t.part = .main
  unfold FoldedRow.addAll
  exact addLaid_main _ _ _ _ (addLaid_main _ _ _ _ fun t ht => by cases ht)

/-- The program's equality row is made of tensors without a written-out factor, and of no form. -/
theorem eqRow_plain (Λ : Params.LinkShape) (phi : List E) (u0 u1 : FoldedRow) (cut : ℕ) (row : Row)
    (h : linkEqualityRow Λ phi u0 u1 cut = some row) :
    (∀ t ∈ row.terms.toList, t.v.denseVars = []) ∧ row.forms = #[] := by
  obtain ⟨-, plus, minus, hp, hm, rfl⟩ := linkEqualityRow_inv Λ phi u0 u1 _ row h
  unfold FoldedRow.addAll
  refine ⟨addLaid_plain _ _ _ _ (fun t ht => (tensorBelow_shape _ rfl _ _ _ hm t ht).2)
    (addLaid_plain _ _ _ _ (fun t ht => (tensorBelow_shape _ rfl _ _ _ hp t ht).2)
      fun t ht => by cases ht), ?_⟩
  rw [(addLaid_terms _ _ _ _).2, (addLaid_terms _ _ _ _).2]

/-- The program's row of a drawn column is made of tensors without a written-out factor, and of no
form. -/
theorem colRow_plain (Sf : Params.FoldeqShape) (x : ℕ) (y : E) (u : FoldedRow) (row : Row)
    (h : foldeqColumnRow Sf x y u = some row) :
    (∀ t ∈ row.terms.toList, t.v.denseVars = []) ∧ row.forms = #[] := by
  obtain ⟨onMessage, onTail, hM, hT, rfl⟩ := foldeqColumnRow_inv Sf x y u row h
  have hTail : ∀ t ∈ onTail, t.denseVars = [] := by
    by_cases hr0 : (Sf.index.code.r == 0) = true
    · rw [if_pos hr0] at hT
      obtain rfl := Option.some.inj hT
      intro t ht
      cases ht
    · rw [if_neg hr0] at hT
      exact fun t ht => (tensorBelow_shape _ rfl _ _ _ hT t ht).2
  show (∀ t ∈ (u.addAll (u.addAll {} onMessage) _).terms.toList, t.v.denseVars = []) ∧
    (u.addAll (u.addAll {} onMessage) _).forms = #[]
  unfold FoldedRow.addAll
  refine ⟨addLaid_plain _ _ _ _ (fun t ht => ?_)
    (addLaid_plain _ _ _ _ (fun t ht => (tensorBelow_shape _ rfl _ _ _ hM t ht).2)
      fun t ht => by cases ht), ?_⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
    exact insertChoice_plain w (hTail w hw) _ _ _
  · rw [(addLaid_terms _ _ _ _).2, (addLaid_terms _ _ _ _).2]

/-! ## All rows of the link -/

/-- A list that is made entry by entry, each step of which may fail: if it is there, it has the
length of the given list, and each of its entries is the step's result. -/
theorem mapM_getD {α β : Type} (f : α → Option β) (d : α) (d' : β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.length = l.length ∧ ∀ k, k < l.length →
      f (l.getD k d) = some (r.getD k d')
  | [], r, h => by
    obtain rfl : [] = r := Option.some.inj h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h
        obtain rfl := h
        obtain ⟨h1, h2⟩ := mapM_getD f d d' l bs hl
        refine ⟨by rw [List.length_cons, List.length_cons, h1], fun k hk => ?_⟩
        cases k with
        | zero => exact ha
        | succ k => exact h2 k (Nat.lt_of_succ_lt_succ hk)

/-- The rows of a table's draws, one by one. list, columns: the listed positions and the columns
that were opened there. Row number k is the row of draw number k, with the fold of the column at
that draw's position as its target. -/
theorem colRows_getD (Sf : Params.FoldeqShape) (eqGamma : Array E) (u : FoldedRow)
    (list : Array ℕ) (columns : Array (Array F)) (draws : List ℕ) (rows : List Row)
    (h : (draws.mapM fun x => do
      let i ← list.idxOf? x
      foldeqColumnRow Sf x (foldeqSymbol eqGamma (← columns[i]?)) u) = some rows) :
    rows.length = draws.length ∧ ∀ k, k < draws.length → ∃ i col,
      list.idxOf? (draws.getD k 0) = some i ∧ columns[i]? = some col ∧
      foldeqColumnRow Sf (draws.getD k 0) (foldeqSymbol eqGamma col) u =
        some (rows.getD k default) := by
  obtain ⟨h1, h2⟩ := mapM_getD _ 0 default draws rows h
  refine ⟨h1, fun k hk => ?_⟩
  have h3 := h2 k hk
  cases hi : list.idxOf? (draws.getD k 0) with
  | none =>
    rw [hi] at h3
    cases h3
  | some i =>
    rw [hi] at h3
    have h4 : (do
        let col ← columns[i]?
        foldeqColumnRow Sf (draws.getD k 0) (foldeqSymbol eqGamma col) u) =
        some (rows.getD k default) := h3
    cases hcol : columns[i]? with
    | none =>
      rw [hcol] at h4
      cases h4
    | some col =>
      rw [hcol] at h4
      exact ⟨i, col, rfl, hcol, h4⟩

/-- What ties the statement that the library's verifier holds after the five rounds to what the
program has drawn and received. phi: the point of comparison. z, beta: the seed. y0, y1: the two
answers. d0, d1: the two tables' draws. f0, f1: the folds of the columns at these draws. -/
structure XTie (S : Sz) (x : S.lk.X4) (phi z : List E) (beta y0 y1 : E) (d0 d1 : List ℕ)
    (f0 f1 : ℕ → E) : Prop where
  phi : x.2 = readP S.P.aPhi phi
  seed : ∀ a, ∃ β : GEˣ, (x.1.1.2 a).1 = (readP (S.P.aR + S.P.aP) z, β) ∧ β.val = readE beta
  ans0 : (x.1.1.2 false).2 () = readE y0
  ans1 : (x.1.1.2 true).2 () = readE y1
  loc0 : ∀ i : Fin S.P.nu0, (x.1.2.1.1 i).val = d0.getD i.val 0
  loc1 : ∀ i : Fin S.P.nuj, (x.1.2.2.1 i).val = d1.getD i.val 0
  fold0 : ∀ i : Fin S.P.nu0, x.1.2.1.2 i = readE (f0 i.val)
  fold1 : ∀ i : Fin S.P.nuj, x.1.2.2.2 i = readE (f1 i.val)

/-- What the rows of the program's link are. rE: the equality row. s0, s1: the two sample rows.
rs0, rs1: the rows of the two tables' draws. o0, o1: the numbers of the two folded rows' oracle
messages. -/
structure LinkRows (S : Sz) (Λ : Params.LinkShape) (Sf0 Sf1 : Params.FoldeqShape) (o0 o1 : ℕ)
    (phi z : List E) (beta y0 y1 : E) (d0 d1 : List ℕ) (f0 f1 : ℕ → E) (rE s0 s1 : Row)
    (rs0 rs1 : List Row) : Prop where
  eq : linkEqualityRow Λ phi ⟨o0, S.layU⟩ ⟨o1, S.layU⟩ S.P.cut = some rE
  smp0 : ∀ (β : GEˣ), β.val = readE beta → ∀ i, i < 2 ^ (S.P.aR + S.P.aP) →
    coefAt s0 o0 .main i = S.smpC (readP (S.P.aR + S.P.aP) z, β) i
  smp1 : ∀ (β : GEˣ), β.val = readE beta → ∀ i, i < 2 ^ (S.P.aR + S.P.aP) →
    coefAt s1 o1 .main i = S.smpC (readP (S.P.aR + S.P.aP) z, β) i
  smp0' : ∀ i, coefAt s0 o1 .main i = 0
  smp1' : ∀ i, coefAt s1 o0 .main i = 0
  tg0 : s0.target = y0
  tg1 : s1.target = y1
  len0 : rs0.length = S.P.nu0
  len1 : rs1.length = S.P.nuj
  col0 : ∀ k, k < S.P.nu0 →
    foldeqColumnRow Sf0 (d0.getD k 0) (f0 k) ⟨o0, S.layU⟩ = some (rs0.getD k default)
  col1 : ∀ k, k < S.P.nuj →
    foldeqColumnRow Sf1 (d1.getD k 0) (f1 k) ⟨o1, S.layU⟩ = some (rs1.getD k default)

/-- What is asked of the sizes and shapes. -/
structure LinkFit (S : Sz) (Λ : Params.LinkShape) (Sf0 Sf1 : Params.FoldeqShape) : Prop where
  bits : Λ.entryBits = S.P.aPhi
  code0 : codeOf Sf0.index.code = S.P.T
  code1 : codeOf Sf1.index.code = S.P.T
  pow : S.P.C.l = 2 ^ S.P.aP
  short : S.P.T.a ≤ 32
  some : 0 < S.P.T.l

/-- The rows of the program's link are the rows of `rowsX`. Row number b of the list that begins
with the equality row, goes on with the two sample rows and ends with the rows of the first and of
the second table's draws has the target `tgX` and, at row r, place p of member a's table, the
coefficient `cfX`. -/
theorem rows_cfX (S : Sz) (Λ : Params.LinkShape) (Sf0 Sf1 : Params.FoldeqShape) (o0 o1 : ℕ)
    (hne : o0 ≠ o1) (x : S.lk.X4) (phi z : List E) (beta y0 y1 : E) (d0 d1 : List ℕ)
    (f0 f1 : ℕ → E) (rE s0 s1 : Row) (rs0 rs1 : List Row) (hF : LinkFit S Λ Sf0 Sf1)
    (hx : XTie S x phi z beta y0 y1 d0 d1 f0 f1)
    (hR : LinkRows S Λ Sf0 Sf1 o0 o1 phi z beta y0 y1 d0 d1 f0 f1 rE s0 s1 rs0 rs1) (b : ℕ)
    (hb : b < S.nRows) :
    readE ((rE :: s0 :: s1 :: (rs0 ++ rs1)).getD b default).target = tgX S x b ∧
      ∀ (a : Bool) (r p : ℕ), r < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
        coefAt ((rE :: s0 :: s1 :: (rs0 ++ rs1)).getD b default) (if a then o1 else o0) .main
          (r + 2 ^ S.P.aR * p) = cfX S x b a r p := by
  have hb' : b < 3 + (S.P.nu0 + S.P.nuj) := hb
  have hRl : S.P.R * S.P.C.l ≤ 2 ^ (S.P.aR + S.P.aP) := by
    rw [Nat.pow_add, hF.pow]
    exact Nat.mul_le_mul_right _ (le_two_pow_clog S.P.R)
  have hfit : S.P.aPhi ≤ S.P.aR + S.P.aP := ceilLog2_le _ _ (le_trans S.fitM hRl)
  rcases b with _ | _ | _ | n
  · -- the equality row
    refine ⟨(eqRow_target Λ phi _ _ _ rE hR.eq).1, fun a r p hr hp => ?_⟩
    obtain ⟨e0, e1⟩ := coefAt_eqRow S Λ phi ⟨o0, S.layU⟩ ⟨o1, S.layU⟩ rE hF.bits hfit rfl rfl hne
      hR.eq r p hr hp
    cases a
    · show coefAt rE o0 .main _ = S.eqC x.2 _
      rw [hx.phi]
      exact e0
    · show coefAt rE o1 .main _ = -S.eqC x.2 _
      rw [hx.phi]
      exact e1
  · -- the first sample row
    refine ⟨?_, fun a r p hr hp => ?_⟩
    · show readE s0.target = (x.1.1.2 false).2 ()
      rw [hR.tg0, hx.ans0]
    · cases a
      · obtain ⟨β, h1, h2⟩ := hx.seed false
        show coefAt s0 o0 .main _ = S.smpC (x.1.1.2 false).1 _
        rw [h1]
        exact hR.smp0 β h2 _ (within_table _ _ r p hr hp).1
      · exact hR.smp0' _
  · -- the second sample row
    refine ⟨?_, fun a r p hr hp => ?_⟩
    · show readE s1.target = (x.1.1.2 true).2 ()
      rw [hR.tg1, hx.ans1]
    · cases a
      · exact hR.smp1' _
      · obtain ⟨β, h1, h2⟩ := hx.seed true
        show coefAt s1 o1 .main _ = S.smpC (x.1.1.2 true).1 _
        rw [h1]
        exact hR.smp1 β h2 _ (within_table _ _ r p hr hp).1
  · -- the draws' rows
    have e3 : n + 1 + 1 + 1 = 3 + n := by omega
    have hrow : (rE :: s0 :: s1 :: (rs0 ++ rs1)).getD (n + 1 + 1 + 1) default =
        (rs0 ++ rs1).getD n default := rfl
    rw [hrow, e3]
    rw [e3] at hb'
    by_cases hn : n < S.P.nu0
    · have hg : (rs0 ++ rs1).getD n default = rs0.getD n default := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [hR.len0]; exact hn)]
      have hc := hR.col0 n hn
      rw [← hx.loc0 ⟨n, hn⟩] at hc
      rw [hg]
      refine ⟨?_, fun a r p hr hp => ?_⟩
      · rw [(colRow_target _ _ _ _ _ hc).1, tgX_first S x ⟨n, hn⟩, hx.fold0 ⟨n, hn⟩]
      · rw [cfX_first S x ⟨n, hn⟩]
        cases a
        · exact coefAt_colRow S Sf0 _ _ ⟨o0, S.layU⟩ _ hF.code0 hF.pow hF.short hF.some rfl hc r p
            hr hp
        · exact coefAt_colRow_else _ _ _ _ _ hc _ _ _ fun h => hne h.1.symm
    · have hm : n - S.P.nu0 < S.P.nuj := by omega
      have e4 : 3 + n = 3 + S.P.nu0 + (n - S.P.nu0) := by omega
      have hg : (rs0 ++ rs1).getD n default = rs1.getD (n - S.P.nu0) default := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [hR.len0]; omega), hR.len0]
      have hc := hR.col1 (n - S.P.nu0) hm
      rw [← hx.loc1 ⟨n - S.P.nu0, hm⟩] at hc
      rw [hg, e4]
      refine ⟨?_, fun a r p hr hp => ?_⟩
      · rw [(colRow_target _ _ _ _ _ hc).1, tgX_further S x ⟨n - S.P.nu0, hm⟩,
          hx.fold1 ⟨n - S.P.nu0, hm⟩]
      · rw [cfX_further S x ⟨n - S.P.nu0, hm⟩]
        cases a
        · exact coefAt_colRow_else _ _ _ _ _ hc _ _ _ fun h => hne h.1
        · exact coefAt_colRow S Sf1 _ _ ⟨o1, S.layU⟩ _ hF.code1 hF.pow hF.short hF.some rfl hc r p
            hr hp

/-- The combined row, as a statement. G: a row on the group. If its target and its
coefficients are the sums of the rows' under the powers of θ, each member's table being in its
block of the group's main table, and if it is 0 on the one row of the group's mask table, then G,
read as a statement of the link's stage, is the combination of the rows of `rowsX`. -/
theorem stmG_rowsX (S : Sz) (t : ℕ) (hl2 : S.P.C.l = 2 ^ S.P.aP) (x : S.lk.X4) (rows : List Row)
    (o0 o1 : ℕ) (θ : GE) (G : GroupRow)
    (hrows : ∀ b, b < S.nRows → readE (rows.getD b default).target = tgX S x b ∧
      ∀ (a : Bool) (r p : ℕ), r < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
        coefAt (rows.getD b default) (if a then o1 else o0) .main (r + 2 ^ S.P.aR * p) =
          cfX S x b a r p)
    (hT : readE G.target =
      ∑ b ∈ Finset.range S.nRows, θ ^ b * readE (rows.getD b default).target)
    (hc : ∀ (a : Bool) (r p : ℕ), r < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
      formAt G.c (S.blk a + r + 2 ^ (S.P.aR + 1) * p) = ∑ b ∈ Finset.range S.nRows,
        θ ^ b * coefAt (rows.getD b default) (if a then o1 else o0) .main (r + 2 ^ S.P.aR * p))
    (hd : ∀ i, i < S.P.Z.l → readV G.d i = 0) :
    stmG (S.sg t) G = sumStm S t (rowsX S t x).1 (rowsX S t x).2 θ := by
  unfold stmG sumStm
  refine Prod.ext ?_ (funext fun j => ?_)
  · show readE G.target = ∑ b : Fin S.nRows, θ ^ b.val * tgX S x b.val
    rw [hT, Finset.sum_range]
    exact Finset.sum_congr rfl fun b _ => by rw [(hrows b.val b.isLt).1]
  · rcases j with ⟨β, p⟩ | j'
    · have hn : Sz.rowNo β < 2 ^ (S.P.aR + 1) :=
        lt_of_lt_of_eq (rowNo_lt β) (congrArg (fun n => 2 ^ n) (Nat.zero_add (S.P.aR + 1)))
      have hp : p.val < 2 ^ S.P.aP := hl2 ▸ p.isLt
      have hr : Sz.rowNo β % 2 ^ S.P.aR < 2 ^ S.P.aR := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hsplit : S.blk (decide (2 ^ S.P.aR ≤ Sz.rowNo β)) + Sz.rowNo β % 2 ^ S.P.aR =
          Sz.rowNo β := by
        rw [Nat.pow_succ] at hn
        by_cases h1 : 2 ^ S.P.aR ≤ Sz.rowNo β
        · rw [decide_eq_true h1, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
          show 2 ^ S.P.aR + _ = _
          omega
        · rw [decide_eq_false h1, Nat.mod_eq_of_lt (by omega)]
          exact Nat.zero_add _
      show formAt G.c (Sz.rowNo β + 2 ^ (0 + (S.P.aR + 1)) * p.val) =
        ∑ b : Fin S.nRows, cfX S x b.val (decide (2 ^ S.P.aR ≤ Sz.rowNo β))
          (Sz.rowNo β % 2 ^ S.P.aR) p.val * θ ^ b.val
      have h2 := hc (decide (2 ^ S.P.aR ≤ Sz.rowNo β)) (Sz.rowNo β % 2 ^ S.P.aR) p.val hr hp
      rw [hsplit] at h2
      have e0 : (0 + (S.P.aR + 1)) = S.P.aR + 1 := Nat.zero_add _
      generalize Sz.rowNo β = n at h2 hr ⊢
      rw [e0, h2, Finset.sum_range]
      exact Finset.sum_congr rfl fun b _ => by
        rw [(hrows b.val b.isLt).2 _ _ _ hr hp, mul_comm]
    · have h0 : Sz.rowNo j'.1 = 0 := Nat.lt_one_iff.1 (rowNo_lt j'.1)
      show readV G.d (Sz.rowNo j'.1 + 2 ^ 0 * j'.2.val) = ∑ b : Fin S.nRows, (0 : GE) * θ ^ b.val
      rw [h0, Nat.zero_add, pow_zero, Nat.one_mul, hd _ j'.2.isLt]
      simp

end OnBytes.Slice

#print axioms OnBytes.Slice.sum_laid_below
#print axioms OnBytes.Slice.sum_laid_placed
#print axioms OnBytes.Slice.coefAt_addLaid
#print axioms OnBytes.Slice.addLaid_keeps
#print axioms OnBytes.Slice.entryAt_layU
#print axioms OnBytes.Slice.within_table
#print axioms OnBytes.Slice.linkEqualityRow_inv
#print axioms OnBytes.Slice.coefAt_eqRow
#print axioms OnBytes.Slice.eqRow_target
#print axioms OnBytes.Slice.foldeqColumnRow_inv
#print axioms OnBytes.Slice.msg_part
#print axioms OnBytes.Slice.tail_part
#print axioms OnBytes.Slice.block_iff
#print axioms OnBytes.Slice.coefAt_colRow
#print axioms OnBytes.Slice.colRow_target
#print axioms OnBytes.Slice.coefAt_colRow_else
#print axioms OnBytes.Slice.coefAt_eqRow_else
#print axioms OnBytes.Slice.readE_foldl_maddS
#print axioms OnBytes.Slice.readE_foldeqSymbol
#print axioms OnBytes.Slice.foldSym₀_closed
#print axioms OnBytes.Slice.foldSym₁_closed
#print axioms OnBytes.Slice.coefAt_smpRow
#print axioms OnBytes.Slice.onTable_plain
#print axioms OnBytes.Slice.addLaid_terms
#print axioms OnBytes.Slice.addLaid_plain
#print axioms OnBytes.Slice.eqRow_main
#print axioms OnBytes.Slice.colRow_main
#print axioms OnBytes.Slice.eqRow_plain
#print axioms OnBytes.Slice.colRow_plain
#print axioms OnBytes.Slice.mapM_getD
#print axioms OnBytes.Slice.colRows_getD
#print axioms OnBytes.Slice.rows_cfX
#print axioms OnBytes.Slice.stmG_rowsX
#print axioms OnBytes.Slice.take_factors
#print axioms OnBytes.Slice.block_mod
#print axioms OnBytes.Slice.addLaid_main
