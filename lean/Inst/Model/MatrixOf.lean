-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/MatrixOf.lean: from the weight tensors back to the matrix W. The scheme's side of the
layout; to audit the relation `RinfPP` (Inst/Model/Scales.lean), nothing of this file need be read.
The index of `Rinf` (`Index`: well-formed `Weights`, Inst/Model/Program.lean) is the family of
weight tensors. The committer and the honest prover work on the matrix W. (Text in double quotes:
see the head of Inst/Model/Program.lean.)
    `matrixOf P k i`   the matrix that holds the tensors of i at the places of the layout
                       (Inst/Model/Layout.lean), each entry in balanced bytes. A computable term,
                       free of choice.
    `wfw_matrixOf`     WF(i) gives WF of the matrix (`Layout.WFW`)
    `weightsOf_matrixOf`   for WF(i), nq + nkv ≤ 64 and 0 < ch the layout reads from `matrixOf i`
                       the tensors of i again
-/
import Inst.Model.LayoutBridge

set_option autoImplicit false

namespace Inst.Model.Layout
open Inst.Model

/-! ## Definitions -/

/-- byte ȷ of v in balanced digits to the base 256: v = Σ_ȷ 256^ȷ b_ȷ with −128 ≤ b_ȷ ≤ 127 -/
def byteOf : ℤ → ℕ → ℤ
  | v, 0 => lowByte v
  | v, jj + 1 => byteOf ((v - lowByte v) / 256) jj

/-- the inverse of `split`: the index with the column part ic and the row part ir -/
def unsplit (c : Coord) (t ic ir : ℕ) : ℕ :=
  match c.kind with
  | .low => ir * 2 ^ t + ic
  | .high =>
    (ir / 2 ^ (sOf c.R - t)) * 2 ^ sOf c.R + ic * 2 ^ (sOf c.R - t) + ir % 2 ^ (sOf c.R - t)
  | .whole => if 0 < t then ic else ir

/-- the index tuple with the row part number r (the digits of r in the mixed radix l_1, l_2, ...)
and the column number q -/
def idxOf : List Coord → List ℕ → ℕ → ℕ → List ℕ
  | c :: cs, t :: ts, r, q =>
    unsplit c t (q % 2 ^ t) (r % lOf c t) :: idxOf cs ts (r / lOf c t) (q / 2 ^ t)
  | _, _, _, _ => []

/-- a unit together with the function that reads its entries from the tensors -/
abbrev Tagged : Type := UnitS × (List ℕ → ℤ)

/-- the unit that contains the row y, with the number of the row inside the unit -/
def findUnit (k : ℕ) : List Tagged → ℕ → Option (Tagged × ℕ)
  | [], _ => none
  | U :: us, y => if y < rows k U.1 then some (U, y) else findUnit k us (y - rows k U.1)

section Read
variable (P : Params) (w : LayerW)

/-- an entry (in, out) = (j, x) of a matrix; an entry (j, e, x) of the matrices of the routed
experts -/
def rd2 (W : Mat) : List ℕ → ℤ
  | [j, x] => W j x
  | _ => 0
def rd3 (W : ℕ → Mat) : List ℕ → ℤ
  | [j, e, x] => W e j x
  | _ => 0
/-- "W_q[j][128 h + n] is the entry (h, n, j), h < 40; W_k[j][128 g + n] the entry (40 + g, n, j), g
< 8"; the other heads hold nothing -/
def rdQK : List ℕ → ℤ
  | [h, n, j] =>
    if h < P.nq then w.Wq j (P.ch * h + n)
    else if h < P.nq + P.nkv then w.Wk j (P.ch * (h - P.nq) + n)
    else 0
  | _ => 0

/-- the units of layer L (`Layout.layerUnits`), each with its entries -/
def layerTagged (L : ℕ) : List Tagged :=
  [(uQK P, rdQK P w), (uV P, rd2 w.Wv), (uO P, rd2 w.Wo)] ++
    (if hasExperts L then
        [(uGU P P.fe, rd2 w.Wg), (uGU P P.fe, rd2 w.Wu), (uGUr P, rd3 w.Eg), (uGUr P, rd3 w.Eu),
          (uD P P.fe, rd2 w.Wd), (uDr P, rd3 w.Ed), (uR P, rd2 w.Wr)]
      else [(uGU P P.f, rd2 w.Wg), (uGU P P.f, rd2 w.Wu), (uD P P.f, rd2 w.Wd)])

end Read

/-- all units (Layout.units), each with its entries: "Emb[tok][j]: the entry (tok, j)"; "H[j][ι]:
the entry (ι, j)" -/
def tagged (P : Params) (i : Weights) : List Tagged :=
  (List.range P.layers).flatMap (fun L => layerTagged P (i.layer L) L) ++
    [(uEmb P, rd2 i.Emb), (uH P, rd2 fun v j => i.H j v)]

/-- The matrix that holds the tensors of i. -/
def matrixOf (P : Params) (k : ℕ) (i : Weights) : Mat := fun y c =>
  match findUnit k (tagged P i) y with
  | none => 0
  | some (U, r) =>
      if c < 2 ^ (bits U.1.coords k).sum then
        byteOf (U.2 (idxOf U.1.coords (bits U.1.coords k) (r % hU k U.1) c)) (r / hU k U.1)
      else 0

/-! ## Laws -/

namespace MatrixOf
open Bridge

/-! ### Bytes -/

theorem byteOf_range (v : ℤ) : ∀ jj, -128 ≤ byteOf v jj ∧ byteOf v jj ≤ 127 := by
  intro jj
  induction jj generalizing v with
  | zero => simp only [byteOf, lowByte]; omega
  | succ jj ih => exact ih _

theorem two_bytes {v : ℤ} (h1 : -2 ^ 12 ≤ v) (h2 : v ≤ 2 ^ 12 - 1) :
    byteOf v 0 + 256 * byteOf v 1 = v := by
  simp only [byteOf, lowByte]
  norm_num at h1 h2
  omega

theorem four_bytes {v : ℤ} (h1 : -2155905152 ≤ v) (h2 : v ≤ 2139062143) :
    byteOf v 0 + 256 * byteOf v 1 + 65536 * byteOf v 2 + 16777216 * byteOf v 3 = v := by
  simp only [byteOf, lowByte]
  omega

/-! ### One coordinate, and index tuples -/

theorem unsplit_split (c : Coord) (left i : ℕ) :
    unsplit c (tOf c left) (split c (tOf c left) i).1 (split c (tOf c left) i).2 = i := by
  obtain ⟨R, kind⟩ := c
  cases kind with
  | low => exact Nat.div_add_mod' i _
  | high =>
    have ht : min (sOf R) left ≤ sOf R := Nat.min_le_left _ _
    show ((i / 2 ^ sOf R * 2 ^ (sOf R - min (sOf R) left) + i % 2 ^ (sOf R - min (sOf R) left)) /
            2 ^ (sOf R - min (sOf R) left)) * 2 ^ sOf R +
        (i / 2 ^ (sOf R - min (sOf R) left) % 2 ^ min (sOf R) left) *
          2 ^ (sOf R - min (sOf R) left) +
        (i / 2 ^ sOf R * 2 ^ (sOf R - min (sOf R) left) + i % 2 ^ (sOf R - min (sOf R) left)) %
          2 ^ (sOf R - min (sOf R) left) = i
    generalize hs' : sOf R - min (sOf R) left = s'
    generalize ht' : min (sOf R) left = t at *
    have hs : sOf R = s' + t := by omega
    rw [hs]
    have hp : 0 < 2 ^ s' := by positivity
    have e1 : (i / 2 ^ (s' + t) * 2 ^ s' + i % 2 ^ s') / 2 ^ s' = i / 2 ^ (s' + t) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp,
        Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.zero_add]
    have e2 : (i / 2 ^ (s' + t) * 2 ^ s' + i % 2 ^ s') % 2 ^ s' = i % 2 ^ s' := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
    rw [e1, e2]
    have e3 : i / 2 ^ (s' + t) = i / 2 ^ s' / 2 ^ t := by rw [Nat.div_div_eq_div_mul, pow_add]
    rw [e3, pow_add]
    have a := Nat.div_add_mod (i / 2 ^ s') (2 ^ t)
    have b := Nat.div_add_mod i (2 ^ s')
    calc i / 2 ^ s' / 2 ^ t * (2 ^ s' * 2 ^ t) + i / 2 ^ s' % 2 ^ t * 2 ^ s' + i % 2 ^ s'
        = 2 ^ s' * (2 ^ t * (i / 2 ^ s' / 2 ^ t) + i / 2 ^ s' % 2 ^ t) + i % 2 ^ s' := by ring
      _ = i := by rw [a, b]
  | whole =>
    show (if 0 < tOf ⟨R, .whole⟩ left then (split ⟨R, .whole⟩ (tOf ⟨R, .whole⟩ left) i).1
        else (split ⟨R, .whole⟩ (tOf ⟨R, .whole⟩ left) i).2) = i
    by_cases h : 0 < tOf ⟨R, .whole⟩ left
    · have : split ⟨R, .whole⟩ (tOf ⟨R, .whole⟩ left) i = (i, 0) := if_pos h
      rw [if_pos h, this]
    · have : split ⟨R, .whole⟩ (tOf ⟨R, .whole⟩ left) i = (0, i) := if_neg h
      rw [if_neg h, this]

/-- from the row part number and the column number of an index tuple, the tuple again -/
theorem idxOf_place : ∀ (cs : List Coord) (left : ℕ) (i : List ℕ), InUnit cs i →
    idxOf cs (bits cs left) (row 0 cs (bits cs left) i) (col cs (bits cs left) i) = i
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | c :: cs, left, i :: is, h => by
      obtain ⟨a1, a2⟩ := (good_split c left).lt i h.1
      have ih := idxOf_place cs (left - tOf c left) is h.2
      show unsplit c (tOf c left)
            (((split c (tOf c left) i).1 +
                2 ^ tOf c left * col cs (bits cs (left - tOf c left)) is) % 2 ^ tOf c left)
            (((split c (tOf c left) i).2 +
                lOf c (tOf c left) * row 0 cs (bits cs (left - tOf c left)) is) %
              lOf c (tOf c left)) ::
          idxOf cs (bits cs (left - tOf c left))
            (((split c (tOf c left) i).2 +
                lOf c (tOf c left) * row 0 cs (bits cs (left - tOf c left)) is) /
              lOf c (tOf c left))
            (((split c (tOf c left) i).1 +
                2 ^ tOf c left * col cs (bits cs (left - tOf c left)) is) /
              2 ^ tOf c left) = i :: is
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a1, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt a2, Nat.add_mul_div_left _ _ (by omega : 0 < lOf c (tOf c left)),
        Nat.div_eq_of_lt a2, Nat.zero_add,
        Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ tOf c left), Nat.div_eq_of_lt a1,
        Nat.zero_add, unsplit_split, ih]

/-- for an index tuple in the unit (`InUnit`): a column number uses only the bits that the
coordinates take -/
theorem col_lt_sum :
    ∀ (cs : List Coord) (left : ℕ) (i : List ℕ),
      InUnit cs i → col cs (bits cs left) i < 2 ^ (bits cs left).sum
  | [], _, [], _ => by simp [col, bits]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | c :: cs, left, i :: is, h => by
      have h1 := ((good_split c left).lt i h.1).1
      have h2 := col_lt_sum cs (left - tOf c left) is h.2
      show (split c (tOf c left) i).1 + 2 ^ tOf c left * col cs (bits cs (left - tOf c left)) is
        < 2 ^ (tOf c left :: bits cs (left - tOf c left)).sum
      rw [List.sum_cons, pow_add]
      calc _ < 2 ^ tOf c left + 2 ^ tOf c left * col cs (bits cs (left - tOf c left)) is := by omega
        _ = 2 ^ tOf c left * (col cs (bits cs (left - tOf c left)) is + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h2

/-! ### Finding the unit of a row -/

/-- the rows of the first n units of a tagged list -/
def offT (k : ℕ) (us : List Tagged) (n : ℕ) : ℕ := ((us.take n).map fun U => rows k U.1).sum

theorem findUnit_at (k : ℕ) :
    ∀ (us : List Tagged) (n : ℕ) (U : Tagged) (r : ℕ),
      us[n]? = some U → r < rows k U.1 → findUnit k us (offT k us n + r) = some (U, r)
  | [], _, _, _, h, _ => by simp at h
  | U₀ :: us, 0, U, r, h, hr => by
      have e : U₀ = U := by simpa using h
      subst e
      simp [findUnit, offT, hr]
  | U₀ :: us, n + 1, U, r, h, hr => by
      have h' : us[n]? = some U := by simpa using h
      have ih := findUnit_at k us n U r h' hr
      have e : offT k (U₀ :: us) (n + 1) = rows k U₀.1 + offT k us n := by simp [offT]
      rw [e, findUnit, if_neg (by omega),
        show rows k U₀.1 + offT k us n + r - rows k U₀.1 = offT k us n + r by omega, ih]

theorem offT_eq (k : ℕ) (us : List Tagged) (n : ℕ) : offT k us n = off k (us.map Prod.fst) n := by
  simp only [offT, off, List.map_take, List.map_map]
  rfl

end MatrixOf

namespace MatrixOf
open Bridge

/-! ### The tagged units are the units -/

theorem layerTagged_fst (P : Params) (w : LayerW) (L : ℕ) :
    (layerTagged P w L).map Prod.fst = layerUnits P L := by
  unfold layerTagged layerUnits
  split_ifs <;> rfl

theorem tagged_fst (P : Params) (i : Weights) : (tagged P i).map Prod.fst = units P := by
  simp only [tagged, units, List.map_append, List.map_flatMap, layerTagged_fst,
    List.map_cons, List.map_nil]

theorem lenTo_tagged (P : Params) (i : Weights) (L : ℕ) :
    lenTo (fun L => layerTagged P (i.layer L) L) L = first P L := by
  have : ∀ L', (layerTagged P (i.layer L') L').length = (layerUnits P L').length := fun L' => by
    rw [← layerTagged_fst P (i.layer L') L', List.length_map]
  simp only [lenTo, first, this]

theorem tagged_at (P : Params) (i : Weights) {L m : ℕ} {U : Tagged} (hL : L < P.layers)
    (hU : (layerTagged P (i.layer L) L)[m]? = some U) :
    (tagged P i)[first P L + m]? = some U := by
  have hm : m < (layerTagged P (i.layer L) L).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hU
    cases hU
  have h1 := flat_get (fun L => layerTagged P (i.layer L) L) P.layers L m hL hm
  rw [lenTo_tagged] at h1
  have hlt : first P L + m <
      ((List.range P.layers).flatMap fun L => layerTagged P (i.layer L) L).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega), hU] at h1
    cases h1
  rw [tagged, List.getElem?_append_left hlt, h1, hU]

theorem tagged_emb (P : Params) (i : Weights) :
    (tagged P i)[first P P.layers]? = some (uEmb P, rd2 i.Emb) := by
  rw [tagged, ← lenTo_tagged P i, List.getElem?_append_right (by rw [length_flat]), length_flat]
  simp

theorem tagged_h (P : Params) (i : Weights) :
    (tagged P i)[first P P.layers + 1]? = some (uH P, rd2 fun v j => i.H j v) := by
  rw [tagged, ← lenTo_tagged P i,
    List.getElem?_append_right (by rw [length_flat]; omega), length_flat]
  simp

/-! ### The cells of the matrix -/

section Cells
variable (P : Params) (k : ℕ) (i : Weights)

/-- the cell in the row r of the unit with the number n -/
theorem cell_at {n : ℕ} {U : Tagged} (hg : (tagged P i)[n]? = some U) {r : ℕ}
    (hr : r < rows k U.1) (c : ℕ) :
    matrixOf P k i (off k (units P) n + r) c =
      if c < 2 ^ (bits U.1.coords k).sum then
        byteOf (U.2 (idxOf U.1.coords (bits U.1.coords k) (r % hU k U.1) c)) (r / hU k U.1)
      else 0 := by
  have h1 := findUnit_at k (tagged P i) n U r hg hr
  rw [offT_eq, tagged_fst] at h1
  simp only [matrixOf, h1]

/-- Under the hypotheses below, byte ȷ of the entry idx is at its place. -/
theorem cell_place {n : ℕ} {U : Tagged} (hg : (tagged P i)[n]? = some U) {jj : ℕ} (hj : jj < U.1.nU)
    {idx : List ℕ} (hi : InUnit U.1.coords idx) :
    matrixOf P k i (place k (units P) n U.1 jj idx).1 (place k (units P) n U.1 jj idx).2 =
      byteOf (U.2 idx) jj := by
  have h0 := row0_lt U.1.coords k idx hi
  rw [← hU_eq] at h0
  have e : (place k (units P) n U.1 jj idx).1 =
      off k (units P) n + (jj * hU k U.1 + row 0 U.1.coords (bits U.1.coords k) idx) := by
    show off k (units P) n + row jj U.1.coords (bits U.1.coords k) idx = _
    rw [row_shift jj U.1.coords k idx hi, hU_eq]
  have hr : jj * hU k U.1 + row 0 U.1.coords (bits U.1.coords k) idx < rows k U.1 := by
    have := row_lt k U.1 jj idx hj hi
    rwa [row_shift jj U.1.coords k idx hi, ← hU_eq] at this
  rw [e, cell_at P k i hg hr]
  have c1 : (place k (units P) n U.1 jj idx).2 = col U.1.coords (bits U.1.coords k) idx := rfl
  rw [c1, if_pos (col_lt_sum U.1.coords k idx hi)]
  have d1 : (jj * hU k U.1 + row 0 U.1.coords (bits U.1.coords k) idx) % hU k U.1 =
      row 0 U.1.coords (bits U.1.coords k) idx := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h0]
  have d2 : (jj * hU k U.1 + row 0 U.1.coords (bits U.1.coords k) idx) / hU k U.1 = jj := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h0, Nat.zero_add]
  rw [d1, d2, idxOf_place U.1.coords k idx hi]

/-- every cell is a signed byte -/
theorem cell_byte (y c : ℕ) : -128 ≤ matrixOf P k i y c ∧ matrixOf P k i y c ≤ 127 := by
  unfold matrixOf
  cases findUnit k (tagged P i) y with
  | none => norm_num
  | some Ur =>
    obtain ⟨U, r⟩ := Ur
    dsimp only
    split_ifs
    · exact byteOf_range _ _
    · norm_num

end Cells

/-! ### What the readers return -/

theorem two_all {r c : ℕ} {W : Mat} (h : Two r c W) (j x : ℕ) :
    -2 ^ 12 ≤ W j x ∧ W j x ≤ 2 ^ 12 - 1 := by
  have := h j x
  by_cases hin : j < r ∧ x < c
  · rwa [if_pos hin] at this
  · rw [if_neg hin] at this
    rw [this]
    norm_num

/-- the values of a reader are in the range of two-byte weights -/
def Small (f : List ℕ → ℤ) : Prop := ∀ idx, -2 ^ 12 ≤ f idx ∧ f idx ≤ 2 ^ 12 - 1

theorem small_rd2 {W : Mat} (h : ∀ j x, -2 ^ 12 ≤ W j x ∧ W j x ≤ 2 ^ 12 - 1) : Small (rd2 W) := by
  intro idx
  match idx with
  | [] => simp [rd2]
  | [_] => simp [rd2]
  | [j, x] => exact h j x
  | _ :: _ :: _ :: _ => simp [rd2]

theorem small_rd3 {W : ℕ → Mat} (h : ∀ e j x, -2 ^ 12 ≤ W e j x ∧ W e j x ≤ 2 ^ 12 - 1) :
    Small (rd3 W) := by
  intro idx
  match idx with
  | [] => simp [rd3]
  | [_] => simp [rd3]
  | [_, _] => simp [rd3]
  | [j, e, x] => exact h e j x
  | _ :: _ :: _ :: _ :: _ => simp [rd3]

theorem small_rdQK (P : Params) {w : LayerW}
    (hq : ∀ j x, -2 ^ 12 ≤ w.Wq j x ∧ w.Wq j x ≤ 2 ^ 12 - 1)
    (hk : ∀ j x, -2 ^ 12 ≤ w.Wk j x ∧ w.Wk j x ≤ 2 ^ 12 - 1) : Small (rdQK P w) := by
  intro idx
  match idx with
  | [] => simp [rdQK]
  | [_] => simp [rdQK]
  | [_, _] => simp [rdQK]
  | [h, n, j] =>
    simp only [rdQK]
    split_ifs
    · exact hq _ _
    · exact hk _ _
    · norm_num
  | _ :: _ :: _ :: _ :: _ => simp [rdQK]

/-- all readers of the units of a well-formed layer are small -/
theorem small_layer (P : Params) {w : LayerW} {L : ℕ} (hw : w.WF P L) :
    ∀ U ∈ layerTagged P w L, Small U.2 := by
  obtain ⟨hq, hk, hv, ho, hrest⟩ := hw
  intro U hU
  unfold layerTagged at hU
  by_cases hex : hasExperts L
  · rw [if_pos hex] at hrest hU
    obtain ⟨hg, hu, hd, hr, he⟩ := hrest
    have hE : ∀ e,
        (∀ j x, -2 ^ 12 ≤ w.Eg e j x ∧ w.Eg e j x ≤ 2 ^ 12 - 1) ∧
        (∀ j x, -2 ^ 12 ≤ w.Eu e j x ∧ w.Eu e j x ≤ 2 ^ 12 - 1) ∧
        (∀ j x, -2 ^ 12 ≤ w.Ed e j x ∧ w.Ed e j x ≤ 2 ^ 12 - 1) := by
      intro e
      have := he e
      by_cases hlt : e < P.nexp
      · rw [if_pos hlt] at this
        exact ⟨two_all this.1, two_all this.2.1, two_all this.2.2⟩
      · rw [if_neg hlt] at this
        exact ⟨two_all this.1, two_all this.2.1, two_all this.2.2⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact small_rdQK P (two_all hq) (two_all hk)
    · exact small_rd2 (two_all hv)
    · exact small_rd2 (two_all ho)
    · exact small_rd2 (two_all hg)
    · exact small_rd2 (two_all hu)
    · exact small_rd3 fun e => (hE e).1
    · exact small_rd3 fun e => (hE e).2.1
    · exact small_rd2 (two_all hd)
    · exact small_rd3 fun e => (hE e).2.2
    · exact small_rd2 (two_all hr)
  · rw [if_neg hex] at hrest hU
    obtain ⟨hg, hu, hd, -, -⟩ := hrest
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl
    · exact small_rdQK P (two_all hq) (two_all hk)
    · exact small_rd2 (two_all hv)
    · exact small_rd2 (two_all ho)
    · exact small_rd2 (two_all hg)
    · exact small_rd2 (two_all hu)
    · exact small_rd2 (two_all hd)

/-- for WF(i): the reader of every unit with two bytes is small -/
theorem small_tagged (P : Params) {i : Weights} (hi : i.WF P) :
    ∀ U ∈ tagged P i, U.1.nU = 2 → Small U.2 := by
  intro U hU h2
  rcases List.mem_append.1 hU with h | h
  · obtain ⟨L, hL, hUL⟩ := List.mem_flatMap.1 h
    have hw := hi.1 L
    rw [if_pos (List.mem_range.1 hL)] at hw
    exact small_layer P hw U hUL
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · simp [uEmb] at h2
    · exact small_rd2 fun v j => two_all hi.2.2 j v

/-! ### The first law -/

/-- WF(i) gives WF of the matrix: signed bytes everywhere, and the two-byte bound in every column of
every pair of rows. -/
theorem wfw_matrixOf (P : Params) (k h : ℕ) {i : Weights} (hi : i.WF P) :
    WFW P k (matrixOf P k i) h := by
  refine ⟨fun y _ c _ => by have := cell_byte P k i y c; norm_num; omega,
    fun n hn U hUn h2 idx hidx c _ => ?_⟩
  have hT : ∃ rdr, (tagged P i)[n]? = some (U, rdr) := by
    have h1 : ((tagged P i).map Prod.fst)[n]? = some U := by rw [tagged_fst]; exact hUn
    rw [List.getElem?_map] at h1
    cases hg : (tagged P i)[n]? with
    | none => rw [hg] at h1; cases h1
    | some T =>
      rw [hg] at h1
      obtain ⟨U', rdr⟩ := T
      have : U' = U := by simpa using h1
      exact ⟨rdr, by rw [this]⟩
  obtain ⟨rdr, hT⟩ := hT
  have hs : Small rdr := small_tagged P hi (U, rdr) (List.mem_of_getElem? hT) h2
  have h0 : row 0 U.coords (bits U.coords k) idx < hU k U := by
    rw [hU_eq]; exact row0_lt U.coords k idx hidx
  obtain ⟨p0, p1⟩ := place_pair k (units P) n U idx hidx
  have hrows : rows k U = 2 * hU k U := by rw [rows, h2]
  rw [p0, p1, Nat.add_assoc,
    cell_at P k i hT (r := row 0 U.coords (bits U.coords k) idx) (by show _ < rows k U; omega),
    cell_at P k i hT (r := hU k U + row 0 U.coords (bits U.coords k) idx)
      (by show _ < rows k U; omega)]
  have d1 : row 0 U.coords (bits U.coords k) idx % hU k U = row 0 U.coords (bits U.coords k) idx :=
    Nat.mod_eq_of_lt h0
  have d2 : row 0 U.coords (bits U.coords k) idx / hU k U = 0 := Nat.div_eq_of_lt h0
  have d3 : (hU k U + row 0 U.coords (bits U.coords k) idx) % hU k U =
      row 0 U.coords (bits U.coords k) idx := by
    rw [Nat.add_mod_left, d1]
  have d4 : (hU k U + row 0 U.coords (bits U.coords k) idx) / hU k U = 1 := by
    rw [Nat.add_div_left _ (by omega), d2]
  simp only [d1, d2, d3, d4]
  split_ifs
  · have hv := hs (idxOf U.coords (bits U.coords k) (row 0 U.coords (bits U.coords k) idx) c)
    rw [two_bytes hv.1 hv.2]
    exact ⟨hv.1, by have := hv.2; omega⟩
  · norm_num

end MatrixOf

namespace MatrixOf
open Bridge

/-! ### The second law -/

section Back
variable (P : Params) (k : ℕ) (i : Weights)

theorem rd_two {n : ℕ} {U : UnitS} {rdr : List ℕ → ℤ} (hg : (tagged P i)[n]? = some (U, rdr))
    (h2 : U.nU = 2) (hs : Small rdr) {idx : List ℕ} (hi : InUnit U.coords idx) :
    rd P k (matrixOf P k i) n U idx = rdr idx := by
  have c0 := cell_place P k i hg (jj := 0) (by show 0 < U.nU; omega) hi
  have c1 := cell_place P k i hg (jj := 1) (by show 1 < U.nU; omega) hi
  simp only [rd, entry, h2, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
    pow_one, one_mul, zero_add]
  rw [c0, c1]
  exact two_bytes (hs idx).1 (hs idx).2

theorem rd_four {n : ℕ} {U : UnitS} {rdr : List ℕ → ℤ}
    (hg : (tagged P i)[n]? = some (U, rdr)) (h4 : U.nU = 4) {idx : List ℕ}
    (hi : InUnit U.coords idx) (h1 : -2155905152 ≤ rdr idx) (h2 : rdr idx ≤ 2139062143) :
    rd P k (matrixOf P k i) n U idx = rdr idx := by
  have c0 := cell_place P k i hg (jj := 0) (by show 0 < U.nU; omega) hi
  have c1 := cell_place P k i hg (jj := 1) (by show 1 < U.nU; omega) hi
  have c2 := cell_place P k i hg (jj := 2) (by show 2 < U.nU; omega) hi
  have c3 := cell_place P k i hg (jj := 3) (by show 3 < U.nU; omega) hi
  simp only [rd, entry, h4, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
    pow_one, one_mul, zero_add]
  rw [c0, c1, c2, c3]
  have := four_bytes h1 h2
  norm_num
  linarith

end Back

theorem mat_eq {r c : ℕ} {lo hi : ℤ} {W : Mat} {f : ℕ → ℕ → ℤ} (hW : Box r c lo hi W)
    (hf : ∀ j < r, ∀ x < c, f j x = W j x) : mat r c f = W := by
  funext j x
  have := hW j x
  by_cases hin : j < r ∧ x < c
  · simp only [mat, if_pos hin]
    exact hf j hin.1 x hin.2
  · rw [if_neg hin] at this
    simp only [mat, if_neg hin, this]

theorem zero_of_two {W : Mat} (h : Two 0 0 W) : (fun _ _ => 0) = W := by
  funext j x
  have := h j x
  simpa using this.symm

theorem layerW_ext {a b : LayerW} (h1 : a.Wq = b.Wq) (h2 : a.Wk = b.Wk) (h3 : a.Wv = b.Wv)
    (h4 : a.Wo = b.Wo) (h5 : a.Wg = b.Wg) (h6 : a.Wu = b.Wu) (h7 : a.Wd = b.Wd) (h8 : a.Wr = b.Wr)
    (h9 : a.Eg = b.Eg) (h10 : a.Eu = b.Eu) (h11 : a.Ed = b.Ed) : a = b := by
  cases a
  cases b
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rfl

/-- one layer L < P.layers, under the hypotheses of `weightsOf_matrixOf`: the layout reads its
weights again -/
theorem layerOf_matrixOf (P : Params) (k : ℕ) {i : Weights} (hi : i.WF P) (h64 : P.nq + P.nkv ≤ 64)
    (hch : 0 < P.ch) {L : ℕ} (hL : L < P.layers) :
    layerOf P k (matrixOf P k i) L = i.layer L := by
  have hw := hi.1 L
  rw [if_pos hL] at hw
  have hsm := small_layer P hw
  obtain ⟨hq, hk, hv, ho, hrest⟩ := hw
  have hdiv : ∀ c n, c < n * P.ch → c / P.ch < n := fun c n hc =>
    Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hc)
  have g0 : (layerTagged P (i.layer L) L)[0]? = some (uQK P, rdQK P (i.layer L)) := by
    simp [layerTagged]
  have t0 : (tagged P i)[first P L]? = some (uQK P, rdQK P (i.layer L)) :=
    tagged_at P i (m := 0) hL g0
  have g1 : (layerTagged P (i.layer L) L)[1]? = some (uV P, rd2 (i.layer L).Wv) := by
    simp [layerTagged]
  have t1 : (tagged P i)[first P L + 1]? = some (uV P, rd2 (i.layer L).Wv) := tagged_at P i hL g1
  have g2 : (layerTagged P (i.layer L) L)[2]? = some (uO P, rd2 (i.layer L).Wo) := by
    simp [layerTagged]
  have t2 : (tagged P i)[first P L + 2]? = some (uO P, rd2 (i.layer L).Wo) := tagged_at P i hL g2
  have s0 : Small (rdQK P (i.layer L)) := hsm _ (List.mem_of_getElem? g0)
  have s1 : Small (rd2 (i.layer L).Wv) := hsm _ (List.mem_of_getElem? g1)
  have s2 : Small (rd2 (i.layer L).Wo) := hsm _ (List.mem_of_getElem? g2)
  have eq : (layerOf P k (matrixOf P k i) L).Wq = (i.layer L).Wq := mat_eq hq fun j hj c hc => by
    have hh := hdiv c _ hc
    rw [rd_two P k i t0 rfl s0 (show InUnit (uQK P).coords [c / P.ch, c % P.ch, j] from
      ⟨by show c / P.ch < 64; omega, Nat.mod_lt _ hch, hj, trivial⟩)]
    simp only [rdQK, if_pos hh, Nat.div_add_mod]
  have ek : (layerOf P k (matrixOf P k i) L).Wk = (i.layer L).Wk := mat_eq hk fun j hj c hc => by
    have hh := hdiv c _ hc
    rw [rd_two P k i t0 rfl s0 (show InUnit (uQK P).coords [P.nq + c / P.ch, c % P.ch, j] from
      ⟨by show P.nq + c / P.ch < 64; omega, Nat.mod_lt _ hch, hj, trivial⟩)]
    simp only [rdQK, if_neg (Nat.not_lt.2 (Nat.le_add_right P.nq (c / P.ch))),
      if_pos (Nat.add_lt_add_left hh P.nq), Nat.add_sub_cancel_left, Nat.div_add_mod]
  have ev : (layerOf P k (matrixOf P k i) L).Wv = (i.layer L).Wv :=
    mat_eq hv fun j hj x hx => rd_two P k i t1 rfl s1 ⟨hj, hx, trivial⟩
  have eo : (layerOf P k (matrixOf P k i) L).Wo = (i.layer L).Wo :=
    mat_eq ho fun j hj x hx => rd_two P k i t2 rfl s2 ⟨hj, hx, trivial⟩
  by_cases hex : hasExperts L
  · rw [if_pos hex] at hrest
    obtain ⟨hg, hu, hd, hr, he⟩ := hrest
    have g3 : (layerTagged P (i.layer L) L)[3]? = some (uGU P P.fe, rd2 (i.layer L).Wg) := by
      simp [layerTagged, hex]
    have t3 : (tagged P i)[first P L + 3]? = some (uGU P P.fe, rd2 (i.layer L).Wg) :=
      tagged_at P i hL g3
    have g4 : (layerTagged P (i.layer L) L)[4]? = some (uGU P P.fe, rd2 (i.layer L).Wu) := by
      simp [layerTagged, hex]
    have t4 : (tagged P i)[first P L + 4]? = some (uGU P P.fe, rd2 (i.layer L).Wu) :=
      tagged_at P i hL g4
    have g5 : (layerTagged P (i.layer L) L)[5]? = some (uGUr P, rd3 (i.layer L).Eg) := by
      simp [layerTagged, hex]
    have t5 : (tagged P i)[first P L + 5]? = some (uGUr P, rd3 (i.layer L).Eg) :=
      tagged_at P i hL g5
    have g6 : (layerTagged P (i.layer L) L)[6]? = some (uGUr P, rd3 (i.layer L).Eu) := by
      simp [layerTagged, hex]
    have t6 : (tagged P i)[first P L + 6]? = some (uGUr P, rd3 (i.layer L).Eu) :=
      tagged_at P i hL g6
    have g7 : (layerTagged P (i.layer L) L)[7]? = some (uD P P.fe, rd2 (i.layer L).Wd) := by
      simp [layerTagged, hex]
    have t7 : (tagged P i)[first P L + 7]? = some (uD P P.fe, rd2 (i.layer L).Wd) :=
      tagged_at P i hL g7
    have g8 : (layerTagged P (i.layer L) L)[8]? = some (uDr P, rd3 (i.layer L).Ed) := by
      simp [layerTagged, hex]
    have t8 : (tagged P i)[first P L + 8]? = some (uDr P, rd3 (i.layer L).Ed) := tagged_at P i hL g8
    have g9 : (layerTagged P (i.layer L) L)[9]? = some (uR P, rd2 (i.layer L).Wr) := by
      simp [layerTagged, hex]
    have t9 : (tagged P i)[first P L + 9]? = some (uR P, rd2 (i.layer L).Wr) := tagged_at P i hL g9
    have s3 : Small (rd2 (i.layer L).Wg) := hsm _ (List.mem_of_getElem? g3)
    have s4 : Small (rd2 (i.layer L).Wu) := hsm _ (List.mem_of_getElem? g4)
    have s5 : Small (rd3 (i.layer L).Eg) := hsm _ (List.mem_of_getElem? g5)
    have s6 : Small (rd3 (i.layer L).Eu) := hsm _ (List.mem_of_getElem? g6)
    have s7 : Small (rd2 (i.layer L).Wd) := hsm _ (List.mem_of_getElem? g7)
    have s8 : Small (rd3 (i.layer L).Ed) := hsm _ (List.mem_of_getElem? g8)
    have s9 : Small (rd2 (i.layer L).Wr) := hsm _ (List.mem_of_getElem? g9)
    refine layerW_ext eq ek ev eo ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (if_pos hex).trans (mat_eq hg fun j hj x hx => rd_two P k i t3 rfl s3 ⟨hj, hx, trivial⟩)
    · exact (if_pos hex).trans (mat_eq hu fun j hj x hx => rd_two P k i t4 rfl s4 ⟨hj, hx, trivial⟩)
    · exact (if_pos hex).trans (mat_eq hd fun j hj x hx => rd_two P k i t7 rfl s7 ⟨hj, hx, trivial⟩)
    · exact (if_pos hex).trans (mat_eq hr fun j hj x hx => rd_two P k i t9 rfl s9 ⟨hj, hx, trivial⟩)
    · funext e
      have := he e
      by_cases hlt : e < P.nexp
      · rw [if_pos hlt] at this
        exact (if_pos ⟨hex, hlt⟩).trans
          (mat_eq this.1 fun j hj x hx => rd_two P k i t5 rfl s5 ⟨hj, hlt, hx, trivial⟩)
      · rw [if_neg hlt] at this
        exact (if_neg fun hc => hlt hc.2).trans (zero_of_two this.1)
    · funext e
      have := he e
      by_cases hlt : e < P.nexp
      · rw [if_pos hlt] at this
        exact (if_pos ⟨hex, hlt⟩).trans
          (mat_eq this.2.1 fun j hj x hx => rd_two P k i t6 rfl s6 ⟨hj, hlt, hx, trivial⟩)
      · rw [if_neg hlt] at this
        exact (if_neg fun hc => hlt hc.2).trans (zero_of_two this.2.1)
    · funext e
      have := he e
      by_cases hlt : e < P.nexp
      · rw [if_pos hlt] at this
        exact (if_pos ⟨hex, hlt⟩).trans
          (mat_eq this.2.2 fun j hj x hx => rd_two P k i t8 rfl s8 ⟨hj, hlt, hx, trivial⟩)
      · rw [if_neg hlt] at this
        exact (if_neg fun hc => hlt hc.2).trans (zero_of_two this.2.2)
  · rw [if_neg hex] at hrest
    obtain ⟨hg, hu, hd, hr, he⟩ := hrest
    have g3 : (layerTagged P (i.layer L) L)[3]? = some (uGU P P.f, rd2 (i.layer L).Wg) := by
      simp [layerTagged, hex]
    have t3 : (tagged P i)[first P L + 3]? = some (uGU P P.f, rd2 (i.layer L).Wg) :=
      tagged_at P i hL g3
    have g4 : (layerTagged P (i.layer L) L)[4]? = some (uGU P P.f, rd2 (i.layer L).Wu) := by
      simp [layerTagged, hex]
    have t4 : (tagged P i)[first P L + 4]? = some (uGU P P.f, rd2 (i.layer L).Wu) :=
      tagged_at P i hL g4
    have g5 : (layerTagged P (i.layer L) L)[5]? = some (uD P P.f, rd2 (i.layer L).Wd) := by
      simp [layerTagged, hex]
    have t5 : (tagged P i)[first P L + 5]? = some (uD P P.f, rd2 (i.layer L).Wd) :=
      tagged_at P i hL g5
    have s3 : Small (rd2 (i.layer L).Wg) := hsm _ (List.mem_of_getElem? g3)
    have s4 : Small (rd2 (i.layer L).Wu) := hsm _ (List.mem_of_getElem? g4)
    have s5 : Small (rd2 (i.layer L).Wd) := hsm _ (List.mem_of_getElem? g5)
    refine layerW_ext eq ek ev eo ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (if_neg hex).trans (mat_eq hg fun j hj x hx => rd_two P k i t3 rfl s3 ⟨hj, hx, trivial⟩)
    · exact (if_neg hex).trans (mat_eq hu fun j hj x hx => rd_two P k i t4 rfl s4 ⟨hj, hx, trivial⟩)
    · exact (if_neg hex).trans (mat_eq hd fun j hj x hx => rd_two P k i t5 rfl s5 ⟨hj, hx, trivial⟩)
    · exact (if_neg hex).trans (zero_of_two hr)
    · funext e; exact (if_neg fun hc => hex hc.1).trans (zero_of_two (he e).1)
    · funext e; exact (if_neg fun hc => hex hc.1).trans (zero_of_two (he e).2.1)
    · funext e; exact (if_neg fun hc => hex hc.1).trans (zero_of_two (he e).2.2)

/-- Under `hi`, `h64`, `hch`: the layout reads from `matrixOf i` the tensors of i again. -/
theorem weightsOf_matrixOf (P : Params) (k : ℕ) {i : Weights} (hi : i.WF P)
    (h64 : P.nq + P.nkv ≤ 64) (hch : 0 < P.ch) :
    weightsOf P k (matrixOf P k i) = i := by
  have hl : (weightsOf P k (matrixOf P k i)).layer = i.layer := by
    funext L
    by_cases hL : L < P.layers
    · exact (if_pos hL).trans (layerOf_matrixOf P k hi h64 hch hL)
    · have hz := hi.1 L
      rw [if_neg hL] at hz
      obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := hz
      exact (if_neg hL).trans
        (layerW_ext (zero_of_two z1) (zero_of_two z2) (zero_of_two z3) (zero_of_two z4)
          (zero_of_two z5) (zero_of_two z6) (zero_of_two z7) (zero_of_two z8)
          (funext fun e => zero_of_two (z9 e).1) (funext fun e => zero_of_two (z9 e).2.1)
          (funext fun e => zero_of_two (z9 e).2.2))
  have he : (weightsOf P k (matrixOf P k i)).Emb = i.Emb := mat_eq hi.2.1 fun t ht j hj => by
    have hb := hi.2.1 t j
    rw [if_pos ⟨ht, hj⟩] at hb
    exact rd_four P k i (tagged_emb P i) rfl ⟨ht, hj, trivial⟩ hb.1 hb.2
  have hh : (weightsOf P k (matrixOf P k i)).H = i.H := mat_eq hi.2.2 fun j hj v hv =>
    rd_two P k i (tagged_h P i) rfl (small_rd2 fun v j => two_all hi.2.2 j v) ⟨hv, hj, trivial⟩
  cases hw : weightsOf P k (matrixOf P k i)
  cases i
  simp only [hw] at hl he hh
  subst hl he hh
  rfl

end MatrixOf

/-- at the reference parameters: the matrix of an index, with the two laws -/
def matrixRef (i : Index ppref) : Mat := matrixOf ppref kRef i.val
theorem wfw_matrixRef (i : Index ppref) : WFW ppref kRef (matrixRef i) hRef :=
  MatrixOf.wfw_matrixOf ppref kRef hRef i.property
theorem indexOf_matrixRef (i : Index ppref) : Bridge.indexOf (matrixRef i) (wfw_matrixRef i) = i :=
  Subtype.ext (MatrixOf.weightsOf_matrixOf ppref kRef i.property (by decide) (by decide))

end Inst.Model.Layout

