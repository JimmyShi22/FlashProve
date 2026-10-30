-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/UnitsCols.lean.

What is here. The columns of a unit, one by one: the honest side's weight and number of a column
with some groups left open (`colWeight`, `colNumber`, Johnson/Desc/K4/Honest/Units.lean), and the
verifier's value of a claim's factors on the columns at a corner (`wsEpsT`,
OnBytes/Model/Weights.lean), each as a product or a sum over the unit's groups in the library's
column halves (`colHalf`, Johnson/Road/FormsKeysFac.lean).

  `runs_le`, `colPart_lt`, `colPart_bit`   a group's column bits; its part of a column's number
  `corner_half`   a factor on its column bits at a corner is its column half at the group's part
  `colWeight_read`, `colNumber_read`   **the honest weight and number**
  `eps_corner`   **the verifier's value at a corner**

Limits. At the reading `Reading.gl`. The unit is asked to meet the library's condition `UnitOK`. The
verifier's value: for a column's number below two to the number of the layout's column bits; the
honest weight: below two to the number of the unit's own. Nothing on the rows or on a matrix.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsDelta

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE mulE)
open OnBytes.Model (Reading WsLay WsUnit WsGrp WsFac WsClaim wsEpsT)
open OnBytes.Road (GrpOK Runs UnitOK colHalf onColumns_at wsEpsT_value tail_bits bitsOf bitsOf_at)
open OnBytes.Desc.First.K4.Honest (grpIndex colPart strideOf colWeight colNumber)

/-- Each group's column bits lie inside the run. -/
theorem runs_le : ∀ (l : List WsGrp) (cb : ℕ), Runs l cb → ∀ g ∈ l,
    g.cb0 + g.t ≤ cb + (l.map (·.t)).sum
  | [], _, _ => fun _ hg => absurd hg List.not_mem_nil
  | x :: rest, cb, hr => by
    intro g hg
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hg with rfl | hg'
    · rw [hr.1]
      omega
    · have := runs_le rest (cb + x.t) hr.2 g hg'
      omega

theorem colPart_lt (g : WsGrp) (C : ℕ) : colPart g C < 2 ^ g.t :=
  Nat.mod_lt _ (Nat.pow_pos (by norm_num))

/-- Bit i of a group's part is the column's bit at the group's i-th column bit. -/
theorem colPart_bit (g : WsGrp) (C : ℕ) {i : ℕ} (hi : i < g.t) :
    (colPart g C).testBit i = C.testBit (g.cb0 + i) := by
  unfold colPart
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.add_comm]

/-- **A factor on its column bits at a corner**: its column half at the group's part of the column's
number. X: coordinates that spell C on the group's column bits. -/
theorem corner_half (x : WsFac) {g : WsGrp} (hg : GrpOK g) (C : ℕ) (X : ℕ → E)
    (hX : ∀ i, i < g.t → X (g.cb0 + i) = if C.testBit (g.cb0 + i) then oneE else zeroE) :
    Reading.gl.val (x.onColumns g X) = colHalf Reading.gl x g (colPart g C) :=
  onColumns_at Reading.gl hg (colPart_lt g C) fun i hi => by rw [hX i hi, colPart_bit g C hi]

variable (st : List (String × ℕ))

/-- A loop each of whose steps multiplies the reading by a number. -/
theorem foldl_factor {α : Type} (f : E → α → E) (k : α → Cb.Gl.E) : ∀ (l : List α),
    (∀ p, ∀ y ∈ l, Reading.gl.val (f p y) = Reading.gl.val p * k y) → ∀ p : E,
    Reading.gl.val (l.foldl f p) = Reading.gl.val p * (l.map k).prod
  | [], _, p => by simp
  | y :: l, h, p => by
    rw [List.foldl_cons, foldl_factor f k l (fun q z hz => h q z (List.mem_cons_of_mem _ hz)),
      h p y List.mem_cons_self, List.map_cons, List.prod_cons, mul_assoc]

/-- A loop each of whose steps adds a number. -/
theorem foldl_addend {α : Type} (f : ℕ → α → ℕ) (k : α → ℕ) (h : ∀ n y, f n y = n + k y) :
    ∀ (l : List α) (n : ℕ), l.foldl f n = n + (l.map k).sum
  | [], n => by simp
  | y :: l, n => by
    rw [List.foldl_cons, foldl_addend f k h l, h, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **THE HONEST WEIGHT OF A COLUMN**: the closed groups' column halves; of an open group the guard.
-/
theorem colWeight_read (u : WsUnit) (fs : List (WsFac × WsGrp)) (hok : ∀ y ∈ fs, GrpOK y.2)
    {C : ℕ} (hC : C < 2 ^ u.ncb) :
    Reading.gl.val (colWeight u fs st C) = (fs.map fun y => match strideOf st y.2 with
      | none => colHalf Reading.gl y.1 y.2 (colPart y.2 C)
      | some _ => if grpGuard y.2 (colPart y.2 C) = true then 1 else 0).prod := by
  unfold colWeight
  rw [if_neg (by omega)]
  refine (foldl_factor _ _ fs (fun p y hy => ?_) oneE).trans (by rw [Reading.gl.one, one_mul])
  cases strideOf st y.2 with
  | none =>
    show Reading.gl.val (mulE p _) = _
    rw [Reading.gl.mul, corner_half y.1 (hok y hy) C _ fun _ _ => rfl]
  | some s =>
    show Reading.gl.val (if (y.2.aTaken && decide (y.2.R ≤ colPart y.2 C)) = true then zeroE
      else p) = Reading.gl.val p * if grpGuard y.2 (colPart y.2 C) = true then 1 else 0
    unfold grpGuard
    by_cases h : (y.2.aTaken && decide (y.2.R ≤ colPart y.2 C)) = true
    · rw [if_pos h, h, if_neg (by decide), Reading.gl.zero, mul_zero]
    · have h' : (y.2.aTaken && decide (y.2.R ≤ colPart y.2 C)) = false := by simpa using h
      rw [if_neg h, h', if_pos (by decide), mul_one]

/-- **THE HONEST NUMBER OF A COLUMN.** -/
theorem colNumber_read (fs : List (WsFac × WsGrp)) (C : ℕ) :
    colNumber fs st C = (fs.map fun y => match strideOf st y.2 with
      | none => 0
      | some s => s * grpIndex y.2 (colPart y.2 C) 0).sum := by
  unfold colNumber
  refine (foldl_addend _ _ (fun n y => ?_) fs 0).trans (Nat.zero_add _)
  cases strideOf st y.2 <;> rfl

/-- **THE VERIFIER's VALUE OF A CLAIM's FACTORS ON THE COLUMNS AT A CORNER**: the product of the
factors' column halves, for a column that the unit's groups can spell; 0 for another. -/
theorem eps_corner {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (U : UnitOK lay.lk u) {C : ℕ} (hC : C < 2 ^ lay.lk) :
    Reading.gl.val (wsEpsT lay c (bitsOf lay.lk C)) =
      ((c.f.zip u.g).map fun y => colHalf Reading.gl y.1 y.2 (colPart y.2 C)).prod *
        if C < 2 ^ u.ncb then 1 else 0 := by
  rw [wsEpsT_value Reading.gl hu,
    tail_bits Reading.gl hC (fun b => (bitsOf lay.lk C).getD (lay.lk - 1 - b) zeroE)
      fun b hb => bitsOf_at hb]
  congr 2
  refine List.map_congr_left fun y hy => ?_
  have hy2 : y.2 ∈ u.g := (List.of_mem_zip hy).2
  refine corner_half y.1 (U.grp y.2 hy2) C _ fun i hi => bitsOf_at ?_
  have h1 := runs_le u.g 0 U.runs y.2 hy2
  have h2 := U.ncb
  have h3 := U.le
  omega

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.runs_le
#print axioms ProofFile.Honest.K4.colPart_lt
#print axioms ProofFile.Honest.K4.colPart_bit
#print axioms ProofFile.Honest.K4.corner_half
#print axioms ProofFile.Honest.K4.foldl_factor
#print axioms ProofFile.Honest.K4.foldl_addend
#print axioms ProofFile.Honest.K4.colWeight_read
#print axioms ProofFile.Honest.K4.colNumber_read
#print axioms ProofFile.Honest.K4.eps_corner
