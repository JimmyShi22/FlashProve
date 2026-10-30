-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/Trace.lean: the head segment's cells and arrays, the tables of its looked-up values,
and the parts of which its field relation is made. The relation itself: `RF`,
Policy/Rel/LedgerHead.lean.

At the reference parameters (`ppref`). Cells are integers. Arrays and the functions formed of them
are polynomials in cells and weights. They are written over any commutative ring K, on cells mapped
into K: the integers for no wrap-around and for the honest trace, F for the relation, E for the
protocol.

  `xv`, `bl`, `nw`, `rn`, `d1`, `d2`, `ex`, `nrm`, `Dv`; `lg`, `K1`, `K2`, `mg`
                         the arrays; the functions of the cells that are not sent
  `hidC`, `hidB`, `hidU`, `hidK`, `hidZ`, `hidS`; `dB4`, `dZ`, `sB2`, `sB3`
                         the six hidden numbers of a position, read from ledger bytes 99 to 119;
                         (B4), (Z), (B2), (B3), each as left side minus right side
  `tableOf`, `InLut`     the table of a family of looked-up values; "a is an entry of the table". At
                         HD0 `tableOf` is the table of the third digit of a margin (R16); the
                         relation's key there is 2^23 times that digit, with a table of its own
  `Small`                each cell of the head and of the borrowed x is below 2^18 in absolute value
  `Hof`                  H[j][ι] read from the matrix W; by `Hof_weightsOf` it is the H of
                         `Layout.weightsOf`, for j < 5,120, ι < 202,048
Elsewhere: the looked-up values (`key`), their tables in the relation (`tableOf`) and the field
relation (`RF`, with the clauses `jc` ((B4), (Z)) and `sums` ((B2), (B3))):
Policy/Rel/LedgerHead.lean; the identities (JH1) to (JH9): `N.idn`, Inst/Model/Head/TraceN.lean,
from Inst/Model/Common/Ledger.lean, where they are (J1) to (J9).

The acceptance policy. The hidden numbers are live, under the names of
Inst/Model/Head/PolicyDefs.lean:
  the margin (B1) has the term ρC (c + 2^37 b);
  (B4) and (Z) at each position and the sums (B2), (B3) are clauses of the field relation;
  (Z) reads ex.
All this at sh = 8, F = 24 (a number, not the field), BIG = 2^37, the step table, Pub = 0, JV = V
(Pub: Inst/Model/Head/PolicyDefs.lean; JV: Inst/Model/Head/PolicyCells.lean).
Limits ("the programs": lean/GLOSSARY.md):
That these clauses are the programs' has been compared by reading, against the verifier's source;
Lean ties them only to this library's own integers (PolicyDefs.lean).

The request. `K1`, `K2`, `mg` depend on a request y : `Req` (Inst/Model/Head/Index.lean): on ρ_i =
[r ≤ i < e] and on the token y.win i that is checked at position i; `mg` also on ρC_i; `dB4`, `dZ`,
`sB2`, `sB3` on ρC, and on the policy's three numbers and NB. At `Req.last`, ρ_i = [i = 1,023]
(`Req.rho_last`, Inst/Model/Head/Index.lean).

The final normalisation (M, K, ϵ) is read by no definition of this file: the looked-up values of NF
and NFH use the shift K, the identities M and ϵ, and both take it as an argument np
(Policy/Rel/LedgerHead.lean, Inst/Model/Head/TraceN.lean). At the reference scales the three are 44,
30 and 53,687 (`Scl.ref`, Inst/Model/Scl.lean; `ppref`, Inst/Model/Program.lean).
Notation:
  `y : Req` (Inst/Model/Head/Index.lean): what the head reads of a request and of the policy: `y.r`,
    `y.e`: the two numbers that bound the covered positions; `y.win i`: the token that is checked at
    position i; `y.pol`: the three numbers of the acceptance policy.
  ρ, ρC (covered, counted): `Req.rho`, `Req.rhoC` (Inst/Model/Head/Index.lean): the indicator of the
    covered positions, [r ≤ i < e]; the indicator of the counted positions: covered, and the checked
    token is a token of the request.
  `AcceptancePolicy` (Inst/Model/ProgramR.lean): the three numbers of the acceptance policy: the clip (C), the
    bound on the mean cost (θ), the limit on the number of positions above the clip (cap).
Definitions, and one theorem, `Hof_weightsOf` (with three small evaluations for it).
-/
import Inst.Model.Head.Index
import Inst.Model.Common.Ledger
import Inst.Model.Tables
import Inst.Model.Scl
import Inst.Model.LayoutSanity

set_option autoImplicit false

namespace Inst.Model.Head

/-- The cells of the head's own matrices and of the borrowed x: (feature, position) ↦ number. B is
not part of the trace. (B: Inst/Model/Head/Index.lean) -/
structure Cells (K : Type) where
  hf : ℕ → ℕ → K
  hd : ℕ → ℕ → K
  hr : ℕ → ℕ → K
  x : ℕ → ℕ → K

/-- the cells mapped by f -/
def Cells.map {K K' : Type} (f : K → K') (t : Cells K) : Cells K' :=
  ⟨fun φ i => f (t.hf φ i), fun φ i => f (t.hd φ i),
    fun φ i => f (t.hr φ i), fun φ i => f (t.x φ i)⟩

section Arrays
variable {K : Type} [CommRing K] (t : Cells K)

/-- "A value with m cells c_0, ..., c_{m−1} at the same index is read as Σ_{l<m} 256^l c_l, plus the
offset in the table" (`rd` is the sum alone; `rn`, `ex`, `Dv` add their offsets) -/
def rd (m : ℕ) (c : ℕ → K) : K := ∑ l ∈ Finset.range m, 256 ^ l * c l

/-- x (five cells b_0..b_4, borrowed): the residual stream after the last layer -/
def bl (l j i : ℕ) : K := t.x (fX l j) i
def xv (j i : ℕ) : K := rd 5 fun l => bl t l j i
/-- nw (2 cells): quotient of the normalisation; rn (2 cells, +32,896): high digit of its
remainder -/
def nw (j i : ℕ) : K := rd 2 fun l => t.hf (fNw l j) i
def rn (j i : ℕ) : K := 32896 + rd 2 fun l => t.hf (fRn l j) i
/-- d1 (2 cells), d2 (1 cell): cells of the middle and of the low digit of a margin; ex (3 cells,
+8,421,505): the looked-up value EX[K_1], which (Z) adds up -/
def d1 (v i : ℕ) : K := rd 2 fun l => t.hf (fD1 l v) i
def d2 (v i : ℕ) : K := t.hf (fD2 v) i
def ex (v i : ℕ) : K := 8421505 + rd 3 fun l => t.hf (fEx l v) i
/-- nrm (2 cells): clamped output of the normalisation -/
def nrm (j i : ℕ) : K := rd 2 fun l => t.hd (fNrm l j) i
/-- D_n (1 cell, +128): ledger byte n -/
def Dv (n i : ℕ) : K := 128 + t.hr n i
/-- the six hidden numbers of position i: c (ledger bytes 99..103), b (104), u (105..109), k
(110..114), z (115, 116), zs (117..119), low byte first -/
def hidC (i : ℕ) : K := Ledger.b256 (fun n => Dv t n i) 99 5
def hidB (i : ℕ) : K := Ledger.b256 (fun n => Dv t n i) 104 1
def hidU (i : ℕ) : K := Ledger.b256 (fun n => Dv t n i) 105 5
def hidK (i : ℕ) : K := Ledger.b256 (fun n => Dv t n i) 110 5
def hidZ (i : ℕ) : K := Ledger.b256 (fun n => Dv t n i) 115 2
def hidS (i : ℕ) : K := Ledger.b256 (fun n => Dv t n i) 117 3

variable (H : ℕ → ℕ → K) (y : Req)

/-- lg_i[ι] = Σ_{j<5120} nrm_i[j] H[j][ι] -/
def lg (i v : ℕ) : K := ∑ j ∈ Finset.range nD, nrm t j i * H j v
/-- K_{1,i}[ι] = d1_i[ι] + 32,896 ρ_i; K_{2,i}[ι] = d2_i[ι] + 128 ρ_i; ρ_i = [r ≤ i < e] of the
request y -/
def K1 (v i : ℕ) : K := d1 t v i + 32896 * (y.rho i : K)
def K2 (v i : ℕ) : K := d2 t v i + 128 * (y.rho i : K)
/-- the margin (B1): mg_i[ι] = ρ_i (lg_i[w_i] − lg_i[ι] − [ι < w_i]) + ρC_i (c_i + 2^37 b_i), w_i =
y.win i the token that is checked at position i -/
def mg (v i : ℕ) : K :=
  (y.rho i : K) * (lg t H i (y.win i) - lg t H i v - if v < y.win i then 1 else 0) +
    (y.rhoC i : K) * (hidC t i + 2 ^ 37 * hidB t i)
/-- (B4), (Z) at position i, masked, each as "left side minus right side": ρC_i (c_i + k_i − C);
ρC_i (zs_i + Σ_{ι<V} ex_i[ι] − 2^24) -/
def dB4 (i : ℕ) : K := (y.rhoC i : K) * (hidC t i + hidK t i - (y.pol.C : K))
def dZ (i : ℕ) : K := (y.rhoC i : K) * (hidS t i + ∑ v ∈ Finset.range nV, ex t v i - 2 ^ 24)
/-- (B2), (B3): sums over the positions, each as "left side minus right side": Σ_i ρC_i (c_i + C
b_i + u_i) − θ NB; Σ_i ρC_i (b_i + z_i) − cap [NB > 0] -/
def sB2 : K :=
  ∑ i ∈ Finset.range nT, (y.rhoC i : K) * (hidC t i + (y.pol.C : K) * hidB t i + hidU t i) -
    (y.pol.theta : K) * (y.NB : K)
def sB3 : K :=
  ∑ i ∈ Finset.range nT, (y.rhoC i : K) * (hidB t i + hidZ t i) -
    if 0 < y.NB then (y.pol.cap : K) else 0

end Arrays

/-- the table of a family (Inst/Model/Tables.lean) -/
def tableOf : Fam → Lut
  | .NF => R16 | .NFH => R16 | .HD0 => R16 | .HD1 => R16 | .ROW => R8 | .HD2 => R8 | .HE0 => FE
  | .HE1 => FE | .CNF => FC

/-- integer cells mapped into a ring -/
def Cells.cast (F : Type) [CommRing F] (t : Cells ℤ) : Cells F := t.map fun (c : ℤ) => (c : F)

/-- a is an entry of the table, in the ring K -/
def InLut {K : Type} [CommRing K] (T : Lut) (a : K) : Prop := ∃ u < T.rows, a = (T.row u : K)

/-- every cell of the trace that belongs to the head, and every cell of the borrowed x, is below 2^β
in absolute value, β = 18 -/
def Small (t : Cells ℤ) : Prop :=
  ∀ i < nT,
    (∀ φ < nFeat .hf, |t.hf φ i| < 2 ^ 18) ∧
    (∀ φ < nFeat .hd, |t.hd φ i| < 2 ^ 18) ∧
    (∀ φ < nFeat .hr, |t.hr φ i| < 2 ^ 18) ∧
    ∀ φ < nFeat .x, |t.x φ i| < 2 ^ 18

/-! ## H in the matrix W -/

/-- the first row of the unit "output matrix", the last of the 386 units -/
def oH : ℕ := 3065840

/-- "H[j][ι] = W_W[ι, j]": two bytes, in the rows o_U + j and o_U + 5,120 + j of column ι -/
def Hof {K : Type} [CommRing K] (W : ℕ → ℕ → K) (j v : ℕ) : K :=
  W (oH + j) v + 256 * W (oH + 5120 + j) v

open Layout in
theorem oH_eq : Layout.off kRef (units ppref) 385 = oH := by decide +kernel

open Layout in
theorem first_layers : first ppref ppref.layers + 1 = 385 := by decide +kernel

open Layout in
theorem bits_uH : bits (uH ppref).coords kRef = [18, 0] := by decide +kernel

open Layout in
/-- For j < 5,120 and ι < 202,048, `Hof` is the H that the layout reads from W. -/
theorem Hof_weightsOf (W : Mat) {j v : ℕ} (hj : j < nD) (hv : v < nV) :
    (weightsOf ppref kRef W).H j v = Hof W j v := by
  have hin : j < ppref.d ∧ v < ppref.V := ⟨hj, hv⟩
  show mat ppref.d ppref.V
      (fun j v => Layout.rd ppref kRef W (first ppref ppref.layers + 1) (uH ppref) [v, j]) j v = _
  simp only [mat, if_pos hin, first_layers, Layout.rd, entry]
  have h2 : (uH ppref).nU = 2 := rfl
  have hp : ∀ jj,
      place kRef (units ppref) 385 (uH ppref) jj [v, j] = (oH + (5120 * jj + j), v) := by
    intro jj
    simp only [place, oH_eq, bits_uH]
    simp [uH, row, col, split, lOf, ppref]
    omega
  simp only [h2, Finset.sum_range_succ, Finset.sum_range_zero, hp, pow_zero, pow_one, one_mul,
    zero_add, Hof, Nat.mul_zero, Nat.mul_one, Nat.add_assoc]

end Inst.Model.Head
