-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/WfKeys.lean: membership of a matrix in the index set, written as a lookup. No protocol.
Definitions, statements and proofs.

The keys are finitely many affine functions of the matrix's columns; each must take a value in a
range of the form {0, .., 2^t - 1}, its table.

Main names:
  `Keys`: the data that a configuration fixes (see its fields; `off`, `coeff`: offsets and
    coefficients); table i is {0, .., 2^(tabVars i) - 1} in F. Key number (u, v) of table i
    (`Keys.key`), for a matrix B with "rows" rows and 2^colVars columns, is
        off i u + ∑_y coeff i u y · B[y][v],                u < 2^rowVars,  v < 2^colVars:
    an affine function of one column. Every table has the same number 2^(rowVars + colVars) of keys.
  `Keys.Describes WF`: for every matrix over F, WF holds of it if and only if its keys lie in their
    tables (`Keys.InTables`).
  `Keys.ext_key`: the multilinear extension of the keys of a table, at a point (z_row, z_col) over
    an extension field, is a public constant plus a tensor form in the matrix:
    ~off_i(z_row) + ⟨rowForm_i(z_row) ⊗ eq(z_col, ·), B⟩.
  `Keys.Fits p w`: the conditions on the width w of a multiplicity that the lookup asks for (three
    clauses).







Keys are the look-up plans of Blocks/RngPlan.lean without the two fields that belong to that
library's own look-up argument (`Keys.plan`). So the valid plans (`Plan.Valid`) that are there carry
over (`Keys.describes_of_valid`): `Plan.ofPairs` (signed bytes and two-byte weights; valid under the
hypotheses of `Plan.ofPairs_valid`).

Notation: `ext g v pt` (Blocks/Ext.lean): the multilinear extension of the vector v of length 2^g at
the point pt; `eqN m _ a z` (Blocks/Basic.lean): eq(a, z) for m coordinates of a and the m-bit
number z; `InTab d a` (Blocks/RngPlan.lean): a lies in the table {0, .., 2^d - 1}.




Limits: this file says nothing on any protocol. It says nothing on the cost of evaluating the public
constant and the row form (Lean models no running time; the condition "few non-zero coefficients in
a row" is therefore not rendered). That the model's keys meet `Fits` at a given width is not here.
The notions follow definitions of this protocol's technical report (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Blocks.RngPlan
import Hiop.Enc

set_option autoImplicit false

namespace Cb
open Finset Blocks Blocks.Rng

/-- The keys: the data. -/
structure Keys (F : Type) where
  /-- the matrix has "rows" rows and 2^colVars columns -/
  rows    : ℕ
  colVars : ℕ
  /-- a table has 2^rowVars rows of keys, one key for each column in each -/
  rowVars : ℕ
  /-- the number of tables; table i is {0, .., 2^(tabVars i) - 1} -/
  tables  : ℕ
  tabVars : ℕ → ℕ
  off     : ℕ → ℕ → F
  coeff   : ℕ → ℕ → ℕ → F

namespace Keys
variable {F : Type} [Field F] (K : Keys F)

/-- the number of variables of the cube of keys -/
abbrev vars : ℕ := K.rowVars + K.colVars

/-- The keys as a look-up plan of Blocks/RngPlan.lean. The two fields B, lp of a plan are read by
that library's look-up argument only. -/
def plan : Plan F := ⟨K.rows, K.colVars, K.tables, K.vars, 0, 0, K.tabVars, K.off, K.coeff⟩

/-- Key number j = u · 2^colVars + v of table i. -/
def key (i : ℕ) (B : ℕ → ℕ → F) (j : ℕ) : F :=
  K.off i (j / 2 ^ K.colVars) +
    ∑ y ∈ range K.rows, K.coeff i (j / 2 ^ K.colVars) y * B y (j % 2 ^ K.colVars)

theorem key_eq_plan (i : ℕ) (B : ℕ → ℕ → F) (j : ℕ) : K.key i B j = K.plan.key i B j := rfl

/-- Every key of every table lies in its table. -/
def InTables (B : ℕ → ℕ → F) : Prop :=
  ∀ i, i < K.tables → ∀ j, j < 2 ^ K.vars → InTab (K.tabVars i) (K.key i B j)

theorem inTables_iff_plan (B : ℕ → ℕ → F) : K.InTables B ↔ K.plan.KeysAll B := Iff.rfl

/-- The keys and tables describe the set WF of matrices. -/
def Describes (WF : (ℕ → ℕ → F) → Prop) : Prop := ∀ B, WF B ↔ K.InTables B

/-- The keys read the matrix on its rows and columns only. -/
theorem key_congr {B B' : ℕ → ℕ → F}
    (h : ∀ y, y < K.rows → ∀ v, v < 2 ^ K.colVars → B y v = B' y v) (i j : ℕ) :
    K.key i B j = K.key i B' j := by
  unfold key
  refine congrArg _ (sum_congr rfl fun y hy => ?_)
  rw [h y (mem_range.mp hy) _ (Nat.mod_lt _ (by positivity))]

/-! ### The extension of the keys -/

section Ext
variable {E : Type} [Field E] [Algebra F E]

/-- The extension of the offsets of table i at the row part of a point (its first rowVars
coordinates): a public constant. -/
def offExt (i : ℕ) (z : ℕ → E) : E := ext K.rowVars (fun u => algebraMap F E (K.off i u)) z

/-- the row form of table i at the row part of a point: ∑_u eq(z_row, u) coeff i u -/
def rowForm (i : ℕ) (z : ℕ → E) (y : ℕ) : E :=
  ext K.rowVars (fun u => algebraMap F E (K.coeff i u y)) z

/-- The tensor form ⟨a ⊗ eq(z_col, ·), B⟩; the column part of z are its coordinates from rowVars
on. -/
def tensor (a : ℕ → E) (z : ℕ → E) (B : ℕ → ℕ → F) : E :=
  ∑ y ∈ range K.rows,
    ∑ v ∈ range (2 ^ K.colVars), a y * eqN K.colVars K.rowVars z v * algebraMap F E (B y v)

/-- The extension of the keys of a table is a public constant plus a tensor form in the matrix. -/
theorem ext_key (i : ℕ) (B : ℕ → ℕ → F) (z : ℕ → E) :
    ext K.vars (fun j => algebraMap F E (K.key i B j)) z =
        K.offExt i z + K.tensor (K.rowForm i z) z B := by
  have h := K.plan.ext_key (E := E) (Nat.le_add_left K.colVars K.rowVars) i B z
  have e : K.plan.D - K.plan.k = K.rowVars := Nat.add_sub_cancel K.rowVars K.colVars
  unfold Plan.offExt Plan.gOf at h
  rw [e] at h
  exact h

/-- A claim on the extension of the keys at a point is a tensor constraint on the matrix. -/
theorem tensor_iff (i : ℕ) (B : ℕ → ℕ → F) (z : ℕ → E) (t : E) :
    ext K.vars (fun j => algebraMap F E (K.key i B j)) z = t ↔
    K.tensor (K.rowForm i z) z B = t - K.offExt i z := by
  rw [K.ext_key, eq_sub_iff_add_eq, add_comm]

end Ext

/-! ### The width of a multiplicity -/

/-- The conditions on numbers: 1 ≤ w, a multiplicity of w bits can count all keys of a table, and
the multiplicities of a whole table do not add up to the characteristic p. -/
structure Fits (p w : ℕ) : Prop where
  pos   : 1 ≤ w
  count : 2 ^ K.vars < 2 ^ w
  sum   : ∀ i, i < K.tables → 2 ^ K.tabVars i * (2 ^ w - 1) < p

omit [Field F] in
/-- If `K.Fits p w`, with at least one table, there are fewer keys in a table than p. -/
theorem Fits.keys_lt {p w : ℕ} (h : K.Fits p w) (h0 : 0 < K.tables) : 2 ^ K.vars < p := by
  have h1 := h.sum 0 h0
  have h2 := h.count
  have h3 : 1 ≤ 2 ^ K.tabVars 0 := Nat.one_le_two_pow
  calc 2 ^ K.vars ≤ 2 ^ w - 1 := by omega
    _ = 1 * (2 ^ w - 1) := (Nat.one_mul _).symm
    _ ≤ 2 ^ K.tabVars 0 * (2 ^ w - 1) := Nat.mul_le_mul_right _ h3
    _ < p := h1

/-- The condition 2^(tabVars i + w) ≤ p, which the plans of Blocks/RngPlan.lean ask for, implies the
third clause. -/
theorem sum_of_pow_le {p w t : ℕ} (h : 2 ^ (t + w) ≤ p) : 2 ^ t * (2 ^ w - 1) < p := by
  have h1 : 0 < 2 ^ t := by positivity
  have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have h3 : 2 ^ t * (2 ^ w - 1) + 2 ^ t = 2 ^ (t + w) := by
    rw [pow_add, Nat.mul_sub, Nat.mul_one,
      Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by omega))]
  omega

end Keys

/-- The keys of a look-up plan of Blocks/RngPlan.lean whose key cube has at least the column
variables. -/
def Keys.ofPlan {F : Type} (P : Plan F) : Keys F := ⟨P.h, P.k, P.D - P.k, P.nc, P.d, P.off, P.Γ⟩

/-- A valid plan gives keys that describe the same set. -/
theorem Keys.describes_of_valid
    {F : Type} [Field F] {P : Plan F} {p : ℕ} {WF : (ℕ → ℕ → F) → Prop} (h : P.Valid p WF) :
    (Keys.ofPlan P).Describes WF := by
  intro B
  rw [h.pl1 B, P.keysOK_iff_keysAll B]
  have e : (Keys.ofPlan P).vars = P.D := Nat.sub_add_cancel h.k_le
  constructor
  · intro hK i hi j hj
    exact hK i hi j (by rw [← e]; exact hj)
  · intro hK i hi j hj
    exact hK i hi j (by rw [e]; exact hj)

end Cb
