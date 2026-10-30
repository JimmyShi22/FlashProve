-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegHead.lean: the vertices and the tables of the plain head's families (Cm/Head.lean).

The plain head is the model's last segment: the final normalisation, and margins in three digits. A
family (`Fam`) has one value at each vertex of a cube.
Definitions. Lemmas: Cm/SegHeadProofs.lean (vertices), Cm/SegHeadAsm.lean (names read). The
families, over `Gl.E`: Cm/TargetSegHead.lean.

Vertices. A key family with indices (a, i), a < len, i < 1,024, stands on vx + 10 variables,
2^vx ≥ len: the vertex b encodes a = b / 2^10 mod 2^vx (`va`) and i = b mod 2^10 (`vi`). A vertex
with a ≥ len is dead. An identity stands on the 10 variables of i: no dead vertex. In a sum over
the 5,120 channels: 13 further variables, j = b' mod 2^13; channels from 5,120 on are dead: the
cells' form is the constant 0 there.

Main names:
  `XI`: requests: `Instance ppref` (Inst/Model/Program.lean).
  `va`, `vi`, `vOf`: the index and the position that a vertex encodes; the vertex of (a, i).
  `vxH f`: the number of variables for the index of a family f (`Plain.Fam`, Cm/Head.lean).
  `tabLog f`: the logarithm of the number of rows of a family's table.
  `allFam`: the list of the seven families of keys.
  `Spec.ReadsAt t M`: integer cells t are what the integer matrices M hold at the places of the
    names that the plain head reads.

Limits: this file says nothing on the request's form (r < e; y = 0 if e < 1,024): a public test. It
says nothing on bounds of cells. It says nothing on protocols.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegHeadLedger
import Cm.SegLayoutPlain
import Cm.SegIdxModel
import Cm.SegIdxRun
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.Head Inst.Model.Layout Finset Cm.Seg.Ex

/-- requests -/
abbrev XI : Type := Instance ppref

/-! ## Vertices -/

/-- the index and the position that a vertex encodes -/
def va (vx b : ℕ) : ℕ := b / 2 ^ 10 % 2 ^ vx
def vi (b : ℕ) : ℕ := b % 2 ^ 10
/-- the vertex of (a, i) -/
def vOf (a i : ℕ) : ℕ := a * 2 ^ 10 + i

/-- the number of variables for the index of a family -/
def vxH : Plain.Fam → ℕ
  | .NF => 13 | .NFH => 13 | .HD0 => 18 | .HD1 => 18 | .ROW => 7 | .HD2 => 18 | .CNF => 13

/-! ## Tables and the list of families -/

/-- the logarithm of the number of rows of a family's table -/
def tabLog : Plain.Fam → ℕ
  | .ROW => 8 | .HD2 => 8 | _ => 16

def allFam : List Plain.Fam := [.NF, .NFH, .HD0, .HD1, .ROW, .HD2, .CNF]

end Cm.Seg

namespace Cm.Spec
open Cb Code Inst.Model Inst.Model.Head Cm.Seg

/-- integer cells t are what the integer matrices M hold at the places of the names that the plain
head reads -/
structure ReadsAt (t : Head.Cells ℤ) (M : ℕ → ℕ → ℕ → ℤ) : Prop where
  hf : ∀ φ < Plain.nHf, ∀ i < nT, t.hf φ i = at' M (Name.hf φ i).place
  hd : ∀ φ < nFeat .hd, ∀ i < nT, t.hd φ i = at' M (Name.hd φ i).place
  hr : ∀ φ < Plain.nHr, ∀ i < nT, t.hr φ i = at' M (Name.hr φ i).place
  x : ∀ φ < nFeat .x, ∀ i < nT, t.x φ i = at' M (ownX φ i).place

end Cm.Spec
