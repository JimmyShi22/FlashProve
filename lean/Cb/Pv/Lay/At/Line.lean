-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Line.lean: the affine side of the lookup's join of a layers' sub-proof, at the
library's description (Inst/Model/FF/Objects.lean), as an affine form in the entries.

Main names:
  `lineS`: the sum over the eight calls, under the calls' weights, of the padding's share and of the
    affine parts of all keys (LINE), under the layers' weights. `accS`: the like sum of the matrix
    products (ACC).
  `lnTg`, `lnInc`: the constant and the coefficients of lineS as a function of the entries: its
    value at the entries 0; at entry j, its value at the unit vector less that.
  `val_comb`, `lin_comb`, `LINE_comb`, `lineS_comb`: the library's value of an array, the affine
    part lin of a key at all 34 families, LINE and lineS are affine in the cells: at a t + b t' they
    are worth a times the value at t, plus b times that at t', plus (1 - a - b) times that at the
    cells 0.
  `lin_w`: lin reads no weight.
  `form_of_comb`: a function of the entries with that law is its value at 0 plus the sum of its
    coefficients times the entries.
  `lineS_form`: so, for a reading rd of the cells that is linear in the entries,
    lineS D (rd m) tb L0 w z = lnTg .. z + the sum over j of lnInc .. z j times m j, for every w.

Limits: that the programs' forms are these is not said here. Nothing is said on an honest prover or
on hiding.


-/
import Inst.Model.FF.Objects
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin val xS gw lw led LINE ACC PADW wc el famsIn lut
  zpos ew len)

noncomputable section

variable {E : Type} [Field E] [scl : Scl]

/-- The affine side of the join. -/
def lineS (D : Dim) (t : Cell → E) (tb : Tables) (L0 : ℕ) (w : ℕ → LW E) (z : ℕ → E) : E :=
  ∑ c : Fin 8, wc D z c * ((((lut tb c).pad : ℤ) : E) * PADW D z c +
    ∑ l ∈ range D.nl, el D z c l * ((famsIn c l).map fun s => LINE D t tb L0 w z s l).sum)

/-- The matrix products' side of the join. -/
def accS (D : Dim) (t : Cell → E) (w : ℕ → LW E) (z : ℕ → E) : E :=
  ∑ c : Fin 8, wc D z c *
    ∑ l ∈ range D.nl, el D z c l * ((famsIn c l).map fun s => ACC D t w z s l).sum

/-- A combination of two contents of the cells. -/
def comb (a b : E) (t t' : Cell → E) : Cell → E := fun c => a * t c + b * t' c

omit scl in
theorem val_comb (a b : E) (t t' : Cell → E) (X : Arr) (inst j i : ℕ) :
    val (comb a b t t') X inst j i =
      a * val t X inst j i + b * val t' X inst j i + (1 - a - b) * ((X.off : ℤ) : E) := by
  unfold Inst.Model.FFSeg.val comb
  have h : ∑ k ∈ range X.nCell,
        (256 : E) ^ k * (a * t ⟨X, k, inst, j, i⟩ + b * t' ⟨X, k, inst, j, i⟩) =
      a * ∑ k ∈ range X.nCell, (256 : E) ^ k * t ⟨X, k, inst, j, i⟩ +
        b * ∑ k ∈ range X.nCell, (256 : E) ^ k * t' ⟨X, k, inst, j, i⟩ := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [h]
  ring

omit scl in
theorem val_zero (X : Arr) (inst j i : ℕ) :
    val (fun _ => (0 : E)) X inst j i = ((X.off : ℤ) : E) := by
  unfold Inst.Model.FFSeg.val
  simp

/-- **The affine part of a key is affine in the cells: all 34 families.** -/
theorem lin_comb (D : Dim) (tb : Tables) (L0 : ℕ) (w : ℕ → LW E) (a b : E) (t t' : Cell → E)
    (s : Fam) (l x i : ℕ) :
    lin D (comb a b t t') tb L0 w s l x i =
      a * lin D t tb L0 w s l x i + b * lin D t' tb L0 w s l x i +
        (1 - a - b) * lin D (fun _ => 0) tb L0 w s l x i := by
  cases s <;>
    simp only [lin, key, gw, lw, led, xS, val_comb, val_zero, Inst.Model.Site.ssite_eq,
      Inst.Model.Site.shigh_eq, Inst.Model.Site.site, Inst.Model.Site.high, sum_add_distrib,
      ← mul_sum] <;>
    (try split_ifs) <;> ring

/-- The affine part of a key reads no weight. -/
theorem lin_w (D : Dim) (tb : Tables) (L0 : ℕ) (w w' : ℕ → LW E) (t : Cell → E) (s : Fam)
    (l x i : ℕ) : lin D t tb L0 w s l x i = lin D t tb L0 w' s l x i := by
  cases s <;> rfl

theorem LINE_comb (D : Dim) (tb : Tables) (L0 : ℕ) (w : ℕ → LW E) (z : ℕ → E) (a b : E)
    (t t' : Cell → E) (s : Fam) (l : ℕ) :
    LINE D (comb a b t t') tb L0 w z s l =
      a * LINE D t tb L0 w z s l + b * LINE D t' tb L0 w z s l +
        (1 - a - b) * LINE D (fun _ => 0) tb L0 w z s l := by
  unfold LINE
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  simp only [lin_comb]
  rw [Blocks.ext_add, Blocks.ext_add, Blocks.ext_smul, Blocks.ext_smul, Blocks.ext_smul]
  ring

theorem LINE_w (D : Dim) (tb : Tables) (L0 : ℕ) (w w' : ℕ → LW E) (z : ℕ → E) (t : Cell → E)
    (s : Fam) (l : ℕ) : LINE D t tb L0 w z s l = LINE D t tb L0 w' z s l := by
  unfold LINE
  simp only [lin_w D tb L0 w w']

omit scl in
theorem sum_map_comb {α : Type} (L : List α) (f g h : α → E) (a b c : E) :
    (L.map fun s => a * f s + b * g s + c * h s).sum =
      a * (L.map f).sum + b * (L.map g).sum + c * (L.map h).sum := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- **The affine side of the join is affine in the cells.** -/
theorem lineS_comb (D : Dim) (tb : Tables) (L0 : ℕ) (w : ℕ → LW E) (z : ℕ → E) (a b : E)
    (t t' : Cell → E) :
    lineS D (comb a b t t') tb L0 w z =
      a * lineS D t tb L0 w z + b * lineS D t' tb L0 w z +
        (1 - a - b) * lineS D (fun _ => 0) tb L0 w z := by
  unfold lineS
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  simp only [LINE_comb, sum_map_comb]
  have h : ∀ A B C : ℕ → E, ∑ l ∈ range D.nl, el D z c l * (a * A l + b * B l + (1 - a - b) * C l) =
      a * ∑ l ∈ range D.nl, el D z c l * A l + b * ∑ l ∈ range D.nl, el D z c l * B l +
        (1 - a - b) * ∑ l ∈ range D.nl, el D z c l * C l := by
    intro A B C
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  rw [h]
  ring

theorem lineS_w (D : Dim) (tb : Tables) (L0 : ℕ) (w w' : ℕ → LW E) (z : ℕ → E) (t : Cell → E) :
    lineS D t tb L0 w z = lineS D t tb L0 w' z := by
  unfold lineS
  simp only [LINE_w D tb L0 w w']

/-! ### From the law to a form -/

omit scl in
/-- A function of the entries that is affine is its value at 0 plus a linear form. -/
theorem form_of_comb {J : Type} [Fintype J] [DecidableEq J] (g : (J → E) → E)
    (hg : ∀ (a b : E) (m m' : J → E),
      g (fun j => a * m j + b * m' j) = a * g m + b * g m' + (1 - a - b) * g 0) (m : J → E) :
    g m = g 0 + ∑ j, (g (fun i => if j = i then 1 else 0) - g 0) * m j := by
  let f : (J → E) →ₗ[E] E :=
    { toFun := fun m => g m - g 0
      map_add' := fun m m' => by
        have h := hg 1 1 m m'
        simp only [one_mul] at h
        show g (m + m') - g 0 = _
        rw [show m + m' = fun j => m j + m' j from rfl, h]
        ring
      map_smul' := fun a m => by
        have h := hg a 0 m m
        simp only [zero_mul, add_zero] at h
        show g (a • m) - g 0 = a • (g m - g 0)
        rw [show a • m = fun j => a * m j from rfl, h, smul_eq_mul]
        ring }
  have h := LinearMap.pi_apply_eq_sum_univ f m
  have h' : g m - g 0 = ∑ j, m j • (g (fun i => if j = i then 1 else 0) - g 0) := h
  rw [sub_eq_iff_eq_add'] at h'
  rw [h']
  congr 1
  exact sum_congr rfl fun j _ => by rw [smul_eq_mul, mul_comm]

section Form
variable {J : Type} [Fintype J] [DecidableEq J] (D : Dim) (tb : Tables) (L0 : ℕ)
  (rd : (J → E) → Cell → E)

/-- A layer's weights, all 0: lineS reads none. -/
def w0 : ℕ → LW E := fun _ =>
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- The constant of the affine side of the join, as a form in the entries. -/
def lnTg (z : ℕ → E) : E := lineS D (rd 0) tb L0 w0 z

/-- Its coefficient at entry j. -/
def lnInc (z : ℕ → E) (j : J) : E :=
  lineS D (rd fun i => if j = i then 1 else 0) tb L0 w0 z - lineS D (rd 0) tb L0 w0 z

/-- **The affine side of the join is an affine form in the entries**, for a reading of the cells
that is linear in the entries. -/
theorem lineS_form
    (hrd : ∀ (a b : E) (m m' : J → E) (c : Cell),
      rd (fun j => a * m j + b * m' j) c = a * rd m c + b * rd m' c)
    (w : ℕ → LW E) (z : ℕ → E) (m : J → E) :
    lineS D (rd m) tb L0 w z = lnTg D tb L0 rd z + ∑ j, lnInc D tb L0 rd z j * m j := by
  have h0 : rd 0 = fun _ => 0 := by
    funext c
    have h := hrd 0 0 0 0 c
    simp only [zero_mul, add_zero] at h
    exact h
  rw [lineS_w D tb L0 w w0]
  refine form_of_comb (fun m => lineS D (rd m) tb L0 w0 z) (fun a b m m' => ?_) m
  show lineS D (rd fun j => a * m j + b * m' j) tb L0 w0 z = _
  rw [show (rd fun j => a * m j + b * m' j) = comb a b (rd m) (rd m') from
      funext fun c => hrd a b m m' c, lineS_comb]
  show _ = a * lineS D (rd m) tb L0 w0 z + b * lineS D (rd m') tb L0 w0 z +
    (1 - a - b) * lineS D (rd 0) tb L0 w0 z
  rw [h0]

end Form
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.lin_comb
#print axioms Cb.Pv.Lay.At.lineS_comb
#print axioms Cb.Pv.Lay.At.form_of_comb
#print axioms Cb.Pv.Lay.At.lineS_form
