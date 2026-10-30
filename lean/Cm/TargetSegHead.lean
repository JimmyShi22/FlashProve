-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegHead.lean: the conditions of the plain head with the scaled table (Cm/TargetPHead.lean)
as families of Cb/Req/ReqSpec.lean, over p = 2^64 - 2^32 + 1.

In standard terms: the constraints of the model's last part (lookups and zero identities), written
as sums of products of atoms.
The plain head is the model's last segment, but for the identity on y (see Limits): the final
normalisation, and margins in three digits. The scaled table is `Plain.TP.R23`: the range table of
width 16, every entry multiplied by 2^23. A family (`Fam`) has one value at each vertex of a cube.
Definitions and statements (`Cm.Seg.TS.Spec.head_key_live` and the like). Proofs:
Cm/TargetSegHeadProofs.lean (values), Cm/TargetSegHeadAsm.lean (well-formedness, places, assembly).
The fields are `Gl.F`, `Gl.E` (Cb/Gl/GlField.lean); the format is `Cm.Seg.TS.fmtRef`
(Cm/TargetSegAll.lean); the head's keys and tables are those of the plain head with the scaled table
(Cm/TargetPHead.lean). The key of the family HD0 is mg - 2^8 K_1 - K_2, and its table is the scaled
one, through `Plain.TP.tableOf`.

Readings. `tH A`: the matrices A over E, read as the head's cells: an own cell at its place,
a borrowed cell at its owner's place (Cm/SegLayout.lean: `Name.hf`, `Name.hd`, `Name.hr`, `ownX`).
`HW W`: the output matrix, read from the index matrix W over F as the weights' layout reads it
(`uH`, Inst/Model/Layout.lean), in E.
Forms. `cXv`, `cNw`, `cRn`, `cD1`, `cD2`, `cNrm`, `cDv`: the arrays `xv`, `nw`, `rn`, `d1`,
`d2`, `nrm`, `Dv` of Inst/Model/Head/Trace.lean as affine forms in cells.

Main names:
  `keyEx np f`: the seven families of keys as expressions (Cm/SegHeadExp.lean), each the mirror of
    `Plain.TP.key` (Cm/TargetPHead.lean). Among these:
    NF: a product of two forms (the stream's value times the ledger's reciprocal) + a form.
    CNF: at a dead vertex the constant "row 0 of the clamp's table".
    HD1, HD2: a form + a public table (the offset, masked by the covered positions).
    HD0: mg - 2^8 K_1 - K_2, mg = ρ_i (lg_i[w_i] - lg_i[v] - [v < w_i]), with two sum atoms.
      `lgV` = Σ_j nrm_i[j] · H[j][v], over the channels: cell form times the index atom of the
      output matrix (Cm/TargetSegIdxModel.lean: `aH`) at the family's own token variables.
      `lgW` = Σ_t Σ_j [t = w_i] · nrm_i[j] · H[j][t]: a sum atom over vocabulary and channels (31
      further variables) with the public indicator of the checked token as coefficient; the
      indicator is 0 at t ≥ 202,048, where the index atom reads entries of the index matrix at
      which no weight lies. Public tables that read the request: ρ_i (covered positions),
      [v < w_i], [t = w_i]; the outer coefficient is 0 at dead vertices.
  `idnEx np k`: the 17 identities of the final normalisation's ledger (Cm/SegHeadLedger.lean).
  `segHead np`: the head's segment (`SegSpec`): shape 2^19 × 4,816, 17 families of identities, 7
    families of keys with their tables.
  `Spec.head_key_live`: for all matrices A over `Gl.E`, all W, all requests: at the vertex of (a,
    i), a < `Plain.len f`, i < `nT`, the family's value is `Plain.TP.key` at (tH A, HW W).
  `Spec.head_key_dead`: at a vertex whose index a is not below `Plain.len f` the value is the image
    of an element of the table.
  `Spec.head_idn_val`: at the vertex i < `nT` the value of identity k is `Plain.idn` at tH A.
  `Spec.head_wf`, `Spec.head_places`: every family is well formed; every place read is among those
    that the cells' layout says the head reads (`reads Hd.plain 24`, Cm/SegLayout.lean).
  `Spec.head_holds`: the assembly: the segment's conditions hold at (x, W, A) ⇔ every key of the
    plain head with the scaled table (`Plain.TP.key`) at (tH A, HW W) is the image of an element of
    its table, and every identity is 0.
  `Spec.head_holds_int`: see its docstring.

Notation: `np`: `NormPar` (Inst/Model/Program.lean), "exponent of the reciprocal; shift; constant"
of a normalisation (fields `M`, `K`, `eps`); `f`: `Plain.Fam` (Cm/Head.lean), the families of keys:
NF, NFH, HD0, HD1, ROW, HD2, CNF; in the doc comment of `Plain.TP.key` (Cm/TargetPHead.lean): NF is
the low key of the rounding nw = rhu(x R, K) with the high digit rn, NFH its high key; CNF the
clamp; ROW a ledger byte; HD2, HD1 the two low digits of a margin, HD0 what is left of it (2^23
times the third digit) (in that sentence x, R, K are `xv`, `Ledger.R`, `np.K` of `Plain.TP.key`'s
body; `rhu`: Inst/Model/Program.lean); `x`: `XI` := `Instance ppref`; `Instance`
(Inst/Model/Program.lean): a request: T tokens, the announced token y, and the two numbers r, e (T:
`ppref.T`); r, e: `x.r`, `x.e` (Inst/Model/Program.lean), natural numbers: the two numbers that
bound the covered positions: r ≤ t < e, each at most T (t in that sentence: a position); `reqOf x`
(Cm/Rel2.lean): `Head.Req` (Inst/Model/Head/Index.lean), what the head reads of a request: r, e, the
checked tokens; ρ_i: `(reqOf x).rho i`, an integer; `Req.rho` (Inst/Model/Head/Index.lean): ρ_i = [r
≤ i < e]: the indicator of the covered positions; w_i: `x.w i`, a natural number; `Instance.w`
(Inst/Model/ProgramR.lean): the checked token of position t, here at t = i; K_1, K_2: `Head.K1`,
`Head.K2` (Inst/Model/Head/Trace.lean), values in the ring of the cells: K_{1,i}[ι] = d1_i[ι] +
32,896 ρ_i; K_{2,i}[ι] = d2_i[ι] + 128 ρ_i (ι in these: the binder `v` of `K1`, `K2`); mg:
`Plain.mg` (Cm/Head.lean), a value in the ring of the cells: the plain margin.

Limits: this file says nothing on the request's form (r < e; y = 0 if e < 1,024), and nothing on
bounds of cells. It says nothing on protocols. The identity on y is one more family of the last
segment in Cm/TargetSegHeadY.lean. `XI`, `va`, `vi`, `vOf`, `vxH` and the like are
Cm/SegHead.lean's.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegHead
import Cm.TargetSegAll
import Cm.TargetSegIdxModel
noncomputable section -- Lean tags what it cannot compile


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.Head Inst.Model.Layout Finset Cm.Seg.Ex

/-! ## Readings -/

/-- Matrices at a place. -/
def atE (A : ℕ → ℕ → ℕ → Cb.Gl.E) (p : Cb.Place) : Cb.Gl.E := A p.1 p.2.1 p.2.2

/-- The matrices, read as the head's cells. -/
def tH (A : ℕ → ℕ → ℕ → Cb.Gl.E) : Head.Cells Cb.Gl.E :=
  ⟨fun φ i => atE A (Name.hf φ i).place,
    fun φ i => atE A (Name.hd φ i).place,
    fun φ i => atE A (Name.hr φ i).place,
    fun φ i => atE A (ownX φ i).place⟩

/-- The output matrix as the weights' layout reads it from an index matrix W over F. -/
def HF (W : ℕ → ℕ → Cb.Gl.F) : ℕ → ℕ → Cb.Gl.F :=
  FFSeg.matR ppref.d ppref.V fun j t =>
    FFSeg.entryR ppref kRef W (first ppref ppref.layers + 1) (uH ppref) [t, j]
/-- `HF W`, carried into E -/
def HW (W : ℕ → ℕ → Cb.Gl.F) : ℕ → ℕ → Cb.Gl.E := fun j t => algebraMap Cb.Gl.F Cb.Gl.E (HF W j t)

/-! ## Forms -/

def cHf (φ i : ℕ) : CForm Cb.Gl.E := cAt (Name.hf φ i).place
def cHd (φ i : ℕ) : CForm Cb.Gl.E := cAt (Name.hd φ i).place
def cHr (φ i : ℕ) : CForm Cb.Gl.E := cAt (Name.hr φ i).place
def cX (φ i : ℕ) : CForm Cb.Gl.E := cAt (ownX φ i).place
/-- "a value with m cells is read as Σ 256^l c_l" (`Head.rd`, Inst/Model/Head/Trace.lean) -/
def cRd (m : ℕ) (c : ℕ → CForm Cb.Gl.E) : CForm Cb.Gl.E :=
  cSum m fun l => ((256 : Cb.Gl.E) ^ l) • c l
def cBl (l j i : ℕ) : CForm Cb.Gl.E := cX (fX l j) i
def cXv (j i : ℕ) : CForm Cb.Gl.E := cRd 5 fun l => cBl l j i
def cNw (j i : ℕ) : CForm Cb.Gl.E := cRd 2 fun l => cHf (fNw l j) i
def cRn (j i : ℕ) : CForm Cb.Gl.E := cK 32896 + cRd 2 fun l => cHf (fRn l j) i
def cD1 (v i : ℕ) : CForm Cb.Gl.E := cRd 2 fun l => cHf (fD1 l v) i
def cD2 (v i : ℕ) : CForm Cb.Gl.E := cHf (fD2 v) i
def cNrm (j i : ℕ) : CForm Cb.Gl.E := cRd 2 fun l => cHd (fNrm l j) i
def cDv (n i : ℕ) : CForm Cb.Gl.E := cK 128 + cHr n i

/-! ## Vertices -/

/-- A form at the live vertices of a family with len indices; the constant 0 at the dead ones. -/
def gd (vx len : ℕ) (f : ℕ → ℕ → CForm Cb.Gl.E) : ℕ → CForm Cb.Gl.E := fun b =>
  if va vx b < len then f (va vx b) (vi b) else cK 0
/-- The indicator of the live vertices. -/
def lv (vx len : ℕ) : XI → ℕ → Cb.Gl.E := fun _ b => if va vx b < len then 1 else 0

/-! ## The logits -/

/-- `nrm` at the inner vertex b' = b · 2^13 + j of a sum over the channels (position:
b' / 2^o mod 2^10); 0 at dead channels. -/
def nrmIn (o : ℕ) : ℕ → CForm Cb.Gl.E := fun b' =>
  if b' % 2 ^ 13 < 5120 then cNrm (b' % 2 ^ 13) (b' / 2 ^ o % 2 ^ 10) else cK 0

/-- lg_i[v] on the 28 variables (v, i), at v < 202,048. -/
def lgV : Ex1 XI Cb.Gl.E :=
  sumA 28 13 (aff0 (nrmIn 13) * idx0 (aH (Src.run 0 18) (Src.run 28 13)))

/-- The public indicator of the checked token, at the inner vertex
b' = (b · 2^18 + t) · 2^13 + j. -/
def isW : XI → ℕ → Cb.Gl.E := fun x b' =>
  if b' / 2 ^ 13 % 2 ^ 18 = x.w (b' / 2 ^ 31 % 2 ^ 10) then 1 else 0

/-- lg_i[w_i] on the 28 variables (v, i); it does not read v. -/
def lgW : Ex1 XI Cb.Gl.E :=
  sumA 28 31 (Ex.sc isW (aff0 (nrmIn 31) * idx0 (aH (Src.run 28 18) (Src.run 46 13))))

/-! ## The families -/

/-- ρ_i of the request, at live vertices of a family on the vocabulary. -/
def rhoT : XI → ℕ → Cb.Gl.E := fun x b =>
  if va 18 b < 202048 then (((reqOf x).rho (vi b) : ℤ) : Cb.Gl.E) else 0
/-- [v < w_i] -/
def ltW : XI → ℕ → Cb.Gl.E := fun x b => if va 18 b < x.w (vi b) then 1 else 0

/-- K_1, K_2, and the plain margin. -/
def k1Ex : Ex1 XI Cb.Gl.E := aff (gd 18 202048 cD1) + (32896 : Cb.Gl.E) • Ex.pub rhoT
def k2Ex : Ex1 XI Cb.Gl.E := aff (gd 18 202048 cD2) + (128 : Cb.Gl.E) • Ex.pub rhoT
def mgEx : Ex1 XI Cb.Gl.E := Ex.sc rhoT (lgW - lgV - Ex.pub ltW)

/-- The keys of the plain head as expressions: the mirror of `Plain.TP.key`. -/
def keyEx (np : NormPar) : Plain.Fam → Ex1 XI Cb.Gl.E
  | .NF =>
    aff (gd 13 5120 cXv) * aff (fun b => lR fun n => cDv n (vi b)) +
      aff (gd 13 5120 fun j i =>
          cK (2 ^ (np.K - 1)) - ((2 : Cb.Gl.E) ^ np.K) • cNw j i - ((2 : Cb.Gl.E) ^ 16) • cRn j i)
  | .NFH => aff (gd 13 5120 fun j i => (((2 ^ (32 - np.K) : ℕ) : Cb.Gl.E)) • cRn j i)
  | .HD0 => mgEx - ((2 : Cb.Gl.E) ^ 8) • k1Ex - k2Ex
  | .HD1 => k1Ex
  | .ROW => aff (gd 7 99 fun n i => (((Ledger.mu n : ℤ) : Cb.Gl.E)) • cDv n i)
  | .HD2 => k2Ex
  | .CNF =>
    aff fun b =>
      if va 13 b < 5120 then
        (cNw (va 13 b) (vi b) + cK (2 ^ 15)) +
          ((2 : Cb.Gl.E) ^ 28) • (cNrm (va 13 b) (vi b) + cK (2 ^ 11))
      else cK (((FC.row 0 : ℤ) : Cb.Gl.E))

/-- The cells of the stream at the inner vertex b' = i · 2^13 + j; 0 at dead channels. -/
def blIn (l : ℕ) : ℕ → CForm Cb.Gl.E := fun b' =>
  if b' % 2 ^ 13 < 5120 then cBl l (b' % 2 ^ 13) (b' / 2 ^ 13 % 2 ^ 10) else cK 0

/-- The 17 identities as expressions. -/
def idnEx (np : NormPar) (k : ℕ) : Ex1 XI Cb.Gl.E :=
  ledEx np (wsEx 10 13 blIn) (fun n b => cDv n (vi b)) k

def keyFam (np : NormPar) (f : Plain.Fam) : Fam XI Cb.Gl.E :=
  Ex1.fam (vxH f + 10) (keyEx np f)
def idnFam (np : NormPar) (k : ℕ) : Fam XI Cb.Gl.E := Ex1.fam 10 (idnEx np k)

def keyTab (f : Plain.Fam) : Tab Cb.Gl.F := tabOf (Plain.TP.tableOf f) (tabLog f)

/-- The head's segment. -/
def segHead (np : NormPar) : SegSpec XI Cb.Gl.F Cb.Gl.E where
  rowsLog := rowsLog 24
  cols := cols 24
  idn := (List.range 17).map (idnFam np)
  keys := allFam.map fun f => (keyFam np f, keyTab f)

end Cm.Seg.TS

namespace Cm.Seg.TS.Spec
open Cm.Spec
open Cb Code Inst.Model Inst.Model.Head Cm.Seg

def head_key_live : Prop :=
  ∀ (np : NormPar) (f : Plain.Fam) (x : XI) (W : ℕ → ℕ → Cb.Gl.F)
      (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a i : ℕ),
    a < Plain.len f → i < nT →
    (keyFam np f).val fmtRef x W A (vOf a i) = Plain.TP.key np (tH A) (HW W) (reqOf x) f a i

def head_key_dead : Prop :=
  ∀ (np : NormPar) (f : Plain.Fam) (x : XI) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (b : ℕ),
    b < 2 ^ (vxH f + 10) → Plain.len f ≤ va (vxH f) b →
    ∃ u ∈ (keyTab f).set, (keyFam np f).val fmtRef x W A b = algebraMap Cb.Gl.F Cb.Gl.E u

def head_idn_val : Prop :=
  ∀ (np : NormPar) (k : ℕ) (x : XI) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (i : ℕ),
    i < nT → (idnFam np k).val fmtRef x W A i = Plain.idn np (tH A) i k

def head_wf : Prop := ∀ np : NormPar, (segHead np).WF fmtRef

def head_places : Prop := ∀ np : NormPar, ∀ p ∈ (segHead np).places, p ∈ reads Hd.plain 24

def head_holds : Prop :=
  ∀ (np : NormPar) (x : XI) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E),
    (segHead np).Holds fmtRef x W A ↔
    (∀ f a i, a < Plain.len f → i < nT →
      ∃ u < (Plain.TP.tableOf f).rows, Plain.TP.key np (tH A) (HW W) (reqOf x) f a i =
        algebraMap Cb.Gl.F Cb.Gl.E (((Plain.TP.tableOf f).row u : ℤ) : Cb.Gl.F)) ∧
    ∀ i < nT, ∀ k < 17, Plain.idn np (tH A) i k = 0

/-- For integer matrices M of cells, an integer index matrix and integer cells t (`ReadsAt t M`),
the segment's conditions are the clauses headKey and headIdn of Cm/TargetPRel.lean (`Cm.TP.Cond` at
`Gl.p`) at t. `ReadsAt t M` (Cm/SegHead.lean): M holds t at the places of the names that the plain
head reads: so the head's cells of the trace of M, or of a trace whose matrices are M. -/
def head_holds_int : Prop :=
  ∀ (np : NormPar) (x : XI) (Wz : Mat) (M : ℕ → ℕ → ℕ → ℤ) (t : Head.Cells ℤ), ReadsAt t M →
    ((segHead np).Holds fmtRef x (fun y c => ((Wz y c : ℤ) : Cb.Gl.F))
        (Partition.castM (E := Cb.Gl.E) M) ↔
      (∀ f a i, a < Plain.len f → i < nT →
        InLut (Plain.TP.tableOf f)
          (Plain.TP.key np (t.cast Cb.Gl.F) (TP.castH Cb.Gl.p Wz) (reqOf x) f a i)) ∧
      ∀ i < nT, ∀ k < 17, Plain.idn np (t.cast Cb.Gl.F) i k = 0)

end Cm.Seg.TS.Spec
