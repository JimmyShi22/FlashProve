-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartCells.lean: the one reading of cells: how the entries that a block of a segment reads
are read as matrices of cells (segment, row, column); and the claims that a segment's sumchecks
leave on cell atoms, as the claims of the step "read" (`ReadCl`, Cb/Ld/LdRead.lean).

Between the sumchecks and the range check with packing: how the evaluation claims that the sumchecks
leave on affine forms in cells are written as linear claims on the range check's matrix of cells.
Definitions and statements (`Cb.Spec.ldPartCells_item` to `Cb.Spec.ldPartCells_honest`); the proofs
are in Cb/Part/LdPartCellsProofs.lean. Generic: any parameters p of a range check with packing
(`RngPar`, Cb/Ld/LdRng.lean: its fields P, ϱ (`rdx`), D are used below; `Uniq`:
Cb/Ld/LdRngAlg.lean), any field E, any type of states, any (for `Spec.ldPartCells_claims`: finite)
type of entries. No protocol occurs; nothing is assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs.

Why: cells are packed in messages (`pack`, Cb/Ld/LdRngAlg.lean: P integer cells in one field
element, weighted with the powers of the radix ϱ), and their reading off the entries is not linear
(see `nm.A` below). A family's polynomial (`Fam.ext`, Cb/Part/LdPart.lean) reads matrices A :
segment → row → column → E through the record `LdPartRd`. All blocks of a segment, and the body's
read stage behind them, must read the same cells. So the value of that record is defined once, here;
and the step from "the value of a cell atom's extension at the sumcheck's end point, masked, is v"
to the read stage's claims is stated once (`Spec.ldPartCells_claims`).
The body's matrix: one matrix of integer cells, rows p.Row = (packed row, lane), columns p.C. It
holds the segment's own rows and the kept earlier rows that the segment reads (by inspection a
write-up of ours (lean/CREDITS.md) sends reads for earlier matrices too, and range-checks
them again in the reading
segment).

Main names:
  `LdPartNm p`: the naming: shapes R s, C s of the matrices that this body holds (R s = 0: the
    segment s is not read here); rowAt s r, colAt s c: where row r, column c of the segment s's
    matrix are in the body's matrix. A product, segment by segment: so that weights on the rows
    times weights on the columns of one segment's matrix are one read of the body's matrix. Two
    layouts are cases: an earlier matrix on columns of its own (the write-up's: along the
    diagonal), or all matrices on the same columns.
  `nm.OK`: inside the shapes, different (segment, row) have different rows; different columns of one
    segment have different columns.
  `nm.mats Y`, `nm.matsE E Y`: the matrices (segment, row, column) read off a matrix Y of the body:
    Y (rowAt s r) (colAt s c) inside the shape, 0 outside; the same in E.
  `nm.A pkJ m`: the one reading. pkJ i κ: at which entry the packed entry (i, κ) is. A := `nm.matsE`
    of the virtual matrix of cells of the packed entries of m (`cells`, Cb/Ld/LdRngAlg.lean, at the
    relaxed bound 2 D). Not linear in m. Where the packed entries of m are no packing of cells below
    2 D in absolute value, it is the zero matrix (the convention of "cells"): whoever uses it
    carries "packed" along.
  `nm.lay Z`: the way back, for the honest side: integer matrices (segment, row, column) laid into
    one matrix of the body; 0 at the places that no cell names.
  `LdPartCl p E St J`: the claims left on cell atoms: names Jc; for each: the atom f on v variables,
    a reading rg of it (`LdPartRg`, Cb/Part/LdPartRead.lean), for each item of the reading the read
    rdAt that serves it (several items may name one read); read off the state: the end point pt, the
    dummy variable's challenge β, the revealed value val; cAt: the entry of the atom's own mask.
  `K.Says st A e`: what the sumchecks' output rows say: for every claim j,
    ext (v j) (b ↦ (f j b).val A) (pt st j) + e (cAt j) · β st j = val st j.
  `K.toCl nm`: the read stage's claims: k0 := the reading's constant at the point; cw := the items'
    column weights, laid at their reads; ms := β at the mask's entry; v := val.
  `K.stdW nm rdOf`: weight vectors for reads that are not shared: rdOf k: the (claim, item) that the
    read k serves.
  `Spec.ldPartCells_item`: for every matrix Y of the body,
    Σ_κ colW κ · (Σ_ρ rowW ρ · Y ρ κ) = the item's value at `nm.matsE E Y`. No injectivity is asked.
  `Spec.ldPartCells_claims`: if each rg j is a reading of f j in the naming's shapes, and
    `K.Ties nm W`, then for all states, all matrices Y, all entries: (K.toCl nm).OnCells W st Y e ⇔
    K.Says st (nm.matsE E Y) e. It is applied in the proof of the front's last step
    (Cb/Part/LdPartPostProofs.lean).
  `Spec.ldPartCells_stdW`: rdOf (rdAt j i) = (j, i) ⇒ `K.Ties nm (K.stdW nm rdOf)`.
  `Spec.ldPartCells_lay`: `nm.OK` ⇒ nm.mats (nm.lay Z) = Z inside the shapes; and a bound b > 0 on
    all |Z s r c| is a bound on nm.lay Z.
  `Spec.ldPartCells_honest`: under the two conditions on the radix (`Uniq` (2 D) ϱ P at the
    characteristic) and `nm.OK` and whatever the arguments hold as proofs: if the packed entries of
    m are the packing of nm.lay Z with cells below b' in absolute value, b' ≤ 2 D, then nm.A pkJ m s
    r c = Z s r c (in E) inside the shapes: the reading of honest entries is the integer cells.

Limits:
How this stands to the write-up (by inspection, on these statements): towards, and wider.
The write-up's layout is one value of the naming (the earlier matrices follow the own ones
along the diagonal); "all on the same columns" is wider. There a read's weight vector is always the
equality vector at a row point on the rows of one part of one matrix; the sum over the parts, with
the map's public coefficients, and the equality vector at the column point stand in the claim (here:
cw): items with any row weights are wider. There each pair (matrix, row point) stands once in the
list of reads: sharing is made; here it is allowed. One inner mask entry for each revealed map of
each sumcheck, times the challenge of the further, last variable, which is never 0: as K.Says has
it. Here β is any function of the state: no clause of `LdPartCl` or `K.Says` asks that it is not 0.
Two things that the naming leaves to whoever fills it (the same reading). (i) A kept unit is no
single row of cells: P lanes share an entry; in the write-up whole matrices are kept, each
filled with zero rows until P divides its number of rows. A kept matrix is never sent again, but
every closing that it survives re-encodes its message: pkJ has to point, at each body, at the
entries of the message that is open there. (ii) The bound on the window event counts all columns of
the body's matrix: along the diagonal their number is the sum over the matrices, own and kept.
This file does not say which entries hold packed cells, or that a block's entries and the body's
packed matrix are the same entries (a clause of the wiring: one type of entries for all blocks of a
segment). It does not say that reads are few: sharing is allowed (rdAt), not made. It says nothing
on packing factor 1, where the write-up sends no reads. Nothing on masks' places, hiding,
errors.
This file gives no instance that meets its hypotheses, so as far as this file shows its theorems may
hold of nothing.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Part.LdPart
import Cb.Part.LdPartRead
import Cb.Ld.LdRead
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

/-- The naming of the body's matrix. -/
structure LdPartNm (p : RngPar) where
  R : ℕ → ℕ
  C : ℕ → ℕ
  rowAt : ℕ → ℕ → p.Row
  colAt : ℕ → ℕ → p.C

namespace LdPartNm
variable {p : RngPar} (nm : LdPartNm p)

structure OK : Prop where
  row : ∀ s r s' r', r < nm.R s → r' < nm.R s' → nm.rowAt s r = nm.rowAt s' r' → s = s' ∧ r = r'
  col : ∀ s c c', c < nm.C s → c' < nm.C s → nm.colAt s c = nm.colAt s c' → c = c'

/-- the matrices (segment, row, column) read off a matrix of the body -/
def mats (Y : p.Cells) : ℕ → ℕ → ℕ → ℤ := fun s r c =>
  if r < nm.R s ∧ c < nm.C s then Y (nm.rowAt s r) (nm.colAt s c) else 0
def matsE (E : Type) [CommRing E] (Y : p.Cells) : ℕ → ℕ → ℕ → E := fun s r c =>
  ((nm.mats Y s r c : ℤ) : E)

/-- The one reading of cells (see the head for its convention where m is not packed). -/
def A {E J : Type} [CommRing E] (pkJ : p.Rp → p.C → J) (m : J → E) : ℕ → ℕ → ℕ → E :=
  nm.matsE E (cells p.P (2 * p.D) p.rdx fun i κ => m (pkJ i κ))

/-- the record `LdPartRd` of Cb/Part/LdPart.lean, filled -/
def rd {E J : Type} [CommRing E] (W : (J → E) → ℕ → ℕ → E) (pkJ : p.Rp → p.C → J) :
    LdPartRd E J := ⟨W, nm.A pkJ⟩

open Classical in
/-- Integer matrices laid into one matrix of the body. -/
def lay (Z : ℕ → ℕ → ℕ → ℤ) : p.Cells := fun ρ κ =>
  if h : ∃ x : ℕ × ℕ × ℕ, x.2.1 < nm.R x.1 ∧ x.2.2 < nm.C x.1 ∧
        nm.rowAt x.1 x.2.1 = ρ ∧ nm.colAt x.1 x.2.2 = κ then
      Z h.choose.1 h.choose.2.1 h.choose.2.2
    else 0

variable {E : Type} [Field E]

open Classical in
/-- an item's weights on the body's rows -/
def rowW (t : LdPartItem E) (γ : ℕ → E) : p.Row → E := fun ρ =>
  ∑ r ∈ range (nm.R t.seg), if nm.rowAt t.seg r = ρ then t.row γ r else 0

/-- an item's weights on the body's columns -/
def colW (t : LdPartItem E) (γ : ℕ → E) : p.C → E := fun κ =>
  ∑ c ∈ range (nm.C t.seg), if nm.colAt t.seg c = κ then t.col γ c else 0

end LdPartNm

/-- The claims that a segment's sumchecks leave on cell atoms: the data. -/
structure LdPartCl (p : RngPar) (E St J : Type) where
  Jc   : Type
  v    : Jc → ℕ
  f    : Jc → ℕ → CForm E
  rg   : Jc → LdPartRg E
  rdAt : ∀ j, Fin (rg j).items.length → p.Rd
  pt   : St → Jc → ℕ → E
  β    : St → Jc → E
  val  : St → Jc → E
  cAt  : Jc → J

namespace LdPartCl
variable {p : RngPar} {E St J : Type} [Field E] (K : LdPartCl p E St J)

/-- What the sumchecks' output rows say. -/
def Says (st : St) (A : ℕ → ℕ → ℕ → E) (e : J → E) : Prop :=
  ∀ j, ext (K.v j) (fun b => (K.f j b).val A) (K.pt st j) + e (K.cAt j) * K.β st j = K.val st j

open Classical in
/-- The read stage's claims. -/
def toCl (nm : LdPartNm p) : ReadCl p E St J where
  Jc := K.Jc
  k0 := fun st j => (K.rg j).k0 (K.pt st j)
  cw := fun st j k κ =>
    ∑ i : Fin (K.rg j).items.length, if K.rdAt j i = k then
      nm.colW ((K.rg j).items.get i) (K.pt st j) κ
    else 0
  ms := fun st j n => if n = K.cAt j then K.β st j else 0
  v  := K.val

/-- the read that serves an item has the item's row weights at the claim's point -/
def Ties (nm : LdPartNm p) (W : St → p.Rd → p.Row → E) : Prop :=
  ∀ st j i, W st (K.rdAt j i) = nm.rowW ((K.rg j).items.get i) (K.pt st j)

/-- weight vectors for reads that are not shared -/
def stdW (nm : LdPartNm p) (rdOf : p.Rd → Σ j, Fin (K.rg j).items.length) :
    St → p.Rd → p.Row → E :=
  fun st k => nm.rowW ((K.rg (rdOf k).1).items.get (rdOf k).2) (K.pt st (rdOf k).1)

end LdPartCl

namespace Spec

/-- An item is one read. -/
def ldPartCells_item : Prop :=
  ∀ (p : RngPar) (E : Type) [Field E] (nm : LdPartNm p) (t : LdPartItem E)
      (γ : ℕ → E) (Y : p.Cells),
    ∑ κ, nm.colW t γ κ * ∑ ρ, nm.rowW t γ ρ * ((Y ρ κ : ℤ) : E) = t.val nm.R nm.C γ (nm.matsE E Y)

/-- Under the hypotheses below, the claims on cell atoms are the read stage's claims. -/
def ldPartCells_claims : Prop :=
  ∀ (p : RngPar) (E St J : Type) [Field E] [Fintype J] (nm : LdPartNm p)
      (K : LdPartCl p E St J) (W : St → p.Rd → p.Row → E),
    (∀ j, (K.rg j).Of nm.R nm.C (K.v j) (K.f j)) → K.Ties nm W →
    ∀ (st : St) (Y : p.Cells) (e : J → E), (K.toCl nm).OnCells W st Y e ↔ K.Says st (nm.matsE E Y) e

def ldPartCells_stdW : Prop :=
  ∀ (p : RngPar) (E St J : Type) [Field E] (nm : LdPartNm p) (K : LdPartCl p E St J)
      (rdOf : p.Rd → Σ j, Fin (K.rg j).items.length),
    (∀ j i, rdOf (K.rdAt j i) = ⟨j, i⟩) → K.Ties nm (K.stdW nm rdOf)

/-- Laid, and read again. -/
def ldPartCells_lay : Prop :=
  ∀ (p : RngPar) (nm : LdPartNm p) (Z : ℕ → ℕ → ℕ → ℤ), nm.OK →
    (∀ s r c, r < nm.R s → c < nm.C s → nm.mats (nm.lay Z) s r c = Z s r c) ∧
    ∀ b : ℤ, 0 < b → (∀ s r c, |Z s r c| < b) → ∀ ρ κ, |nm.lay Z ρ κ| < b

/-- Under the hypotheses below, the reading of honest entries is the integer cells. -/
def ldPartCells_honest : Prop :=
  ∀ (p : RngPar) (E J : Type) [Field E] (pp : ℕ) [CharP E pp] (nm : LdPartNm p)
      (pkJ : p.Rp → p.C → J) (m : J → E) (Z : ℕ → ℕ → ℕ → ℤ) (b' : ℤ),
    nm.OK → Uniq (2 * p.D) p.rdx p.P pp → b' ≤ 2 * p.D →
    PackBy b' p.rdx (nm.lay Z) (fun i κ => m (pkJ i κ)) →
    ∀ s r c, r < nm.R s → c < nm.C s → nm.A pkJ m s r c = ((Z s r c : ℤ) : E)

end Spec
end Cb
