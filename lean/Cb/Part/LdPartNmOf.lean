-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartNmOf.lean: the naming of a body's matrix of cells, computed from a partition
(Cb/Part/LdPartDef.lean) and the public parameters of packing, with readings in its shapes.

Definitions and statements (the statements in `Cb.Spec`); the proofs are in
Cb/Part/LdPartNmOfProofs.lean. Nothing assumed beyond the hypotheses of the statements and whatever
the arguments hold as proofs. In standard terms: book-keeping for how a request's cells are laid
out: for each row of each matrix of cells at hand, in which row and lane of the one matrix that a
body's range check treats it is.
A naming (`LdPartNm`, Cb/Part/LdPartCells.lean) says where row r and column c of segment s are in a
body's one matrix of cells. A reading (`LdPartRg`, Cb/Part/LdPartRead.lean) writes a claim on a cell
atom as weights on rows times weights on columns.

Why: the front's last step asks, of whoever fills it: a naming nm of
the body's matrix; for each claim on a cell atom a reading in nm's shapes; reads that serve its
items, with tied weight vectors. Here all four are defined terms, and what is asked becomes
conditions on numbers and one condition on places, under the partition's laws `P.Props p`. (`nm.OK`
is a premise in Cb/Part/LdPartCells.lean: `Spec.ldPartCells_lay`, `Spec.ldPartCells_honest`.)
Whole matrices: a naming names, of a segment s, the rows r < R s: an initial segment. A partition's
`kept k` is an arbitrary finite set of (segment, row). So a matrix is named whole or not at all: a
parameter `on` says which segments' matrices are in the matrix at hand. It closes `kept` under "same
packed row" (K.P lanes share an entry), and more. The partition's `kept k` stays a set of rows (it
says what is read later); the builder keeps the matrices that hold them. A write-up of ours
(lean/CREDITS.md)
keeps whole matrices too: true of the words, not of the sizes: see Limits.

Main names:
  `P.parS K on Rd U wd nd`: the parameters of the range check: packed rows are the pairs (segment s
    < P.n, packed row below `P.rpS K on s`, the number of packed rows of segment s in the matrix at
    hand): one type of names of segments for all bodies; columns: the one public width K.Cw, which
    is not 0 (the instance `NeZero K.Cw`, here and wherever `parS` occurs); packing factor, radix:
    K's; honest bound, window: P's; reads, combinations, width and number of digits: parameters.
  `P.nmS K on Rd U wd nd d0`: the naming, in the standard order: row r of segment s in the packed
    row (s, r / K.P), lane r mod K.P; column c at c mod K.Cw (all matrices on the same columns); d0:
    a row of the matrix for arguments outside the shapes (idle).
  `P.onBody k`, `P.onKept k`: body k: segment k's own matrix, and every matrix of which a row is
    kept after k - 1 (read by k or not); the kept messages after k: every matrix of which a row is
    in `P.kept k`.
  `P.rgS on v g`: see its docstring.
  `P.ReadsS on v f`: see its docstring: not shared.
  `Spec.ldPartNmOf_ok`: if 0 < K.P and, for every s with on s, s < P.n and cols s ≤ K.Cw, then the
    naming has `LdPartNm.OK`.
  `Spec.ldPartNmOf_shape`: `P.Props p`, k < P.n: every place of `(P.seg k).places` lies in body
    k's shapes (from the laws `reads` and `keeps`).
  `Spec.ldPartNmOf_reading`: so, under the same two: an atom g on v variables all of whose places
    are places of segment k has the reading `P.rgS (P.onBody k) v g` in body k's shapes.

Limits: this file does not say that the cell atoms of a glued family (the front's fI, fK) have their
places among `(P.seg k).places`: the premise of `Spec.ldPartNmOf_reading`, owed by whoever glues. It
does not say that messages hold whole matrices. It says nothing on the ties between the namings of
two stages (`PartOf`, `OwnAt`, Cb/Part/LdPartTieNm.lean) for these values. This file gives no
instance of `LdPartD`. `ldPartNmOf_ties` is named by no other file of the tree but for its
proof (by a search by name).



Declared (by reading, on these statements: towards; zero rows until `K.P` divides, and no packed row
that straddles two matrices, are the write-up's). The dearest difference: a segment
has one matrix here (Cb/Req/ReqSpec.lean). In the write-up a segment has a tuple of
matrices, each in an oracle message of its own, and what later segments read stands in separate
matrices: only these are kept. Here one kept row makes onKept true for the segment: all its cells
are kept, encoded anew at each closing that they cross, and range-checked again in every body that
they cross. By reading, no theorem: this layout differs from the write-up's in cost only
(rows under the ternary combinations, digits, the digits' lookup, the closings' new messages); that
it proves the same relation, no less and no more, is our reading and is stated by no theorem of this
library. At the model, by the same reading: a body of the second kind would hold its own rows and
the whole of the segment before it (segment k has 2 ^ `rowsLog k` rows: Cm/SegLayout.lean), where
the write-up's count for that kind already includes what it borrows.
The reads at real sizes (an estimate, by the same reading): one item a column of every matrix at
hand, not shared: for one claim about (matrices at hand) × 6,000 reads, each a row of 7,200 entries:
some 10^8 entries for each claim on a cell atom; with some hundreds of claims a segment the message
of reads would dwarf the cells. No clause forbids it; it is a reason to take a reading by bits
before any number is quoted.
Reads are not shared, and the reading has one item a column of every matrix at hand: far more reads
than the write-up's (one for each pair (matrix, row point) and part): a difference in
cost; a reading by bits (Cm/TargetRead.lean) would mend it. All kept matrices stand in every body
that they cross. One width.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Part.LdPartRide
import Cb.Part.LdPartCells
import Cb.Ld.LdRng2

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

namespace LdPartD
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
  (P : LdPartD Cf) (K : LdPartPk)

/-- The number of packed rows of segment s in the matrix at hand. -/
def rpS (on : ℕ → Bool) (s : ℕ) : ℕ := if on s then P.rp K s else 0

/-- The shapes: 2^rowsLog rows and cols columns of segment s if `on s`, else 0. -/
def rowsS (on : ℕ → Bool) (s : ℕ) : ℕ := if on s then 2 ^ (P.seg s).rowsLog else 0
def colsS (on : ℕ → Bool) (s : ℕ) : ℕ := if on s then (P.seg s).cols else 0

/-- The parameters of the range check. -/
@[reducible] def parS (on : ℕ → Bool) (Rd U : Type) [Fintype Rd] [Fintype U] [DecidableEq U]
    [NeZero K.Cw] (wd nd : ℕ) : RngPar2 :=
  { Rp := Σ s : Fin P.n, Fin (P.rpS K on s), Rd := Rd, C := Fin K.Cw, U := U, P := K.P,
    rdx := K.rdx, B := P.B, D := P.D, wd := wd, nd := nd }

/-- The naming. -/
def nmS (on : ℕ → Bool) (Rd U : Type) [Fintype Rd] [Fintype U] [DecidableEq U] [NeZero K.Cw]
    (wd nd : ℕ) (d0 : (P.parS K on Rd U wd nd).one.Row) :
    LdPartNm (P.parS K on Rd U wd nd).one where
  R := P.rowsS on
  C := P.colsS on
  rowAt := fun s r =>
    if h : s < P.n ∧ r / K.P < P.rpS K on s ∧ r % K.P < K.P then
      (⟨⟨s, h.1⟩, ⟨r / K.P, h.2.1⟩⟩, ⟨r % K.P, h.2.2⟩)
    else d0
  colAt := fun _ c => ⟨c % K.Cw, Nat.mod_lt _ (NeZero.pos _)⟩

/-- The rows that are kept after segment k - 1; none for k = 0. -/
def keptBefore : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | k + 1 => P.kept k

/-- Which matrices are in body k (`onBody`); in the kept messages after k (`onKept`). -/
def onBody (k : ℕ) : ℕ → Bool := fun s => decide (s = k) || decide (∃ q ∈ P.keptBefore k, q.1 = s)
def onKept (k : ℕ) : ℕ → Bool := fun s => decide (∃ q ∈ P.kept k, q.1 = s)

/-- The reading `ldPartByCol` (Cb/Part/LdPartRead.lean), in these shapes. -/
def rgS (on : ℕ → Bool) (v : ℕ) (g : ℕ → CForm E) : LdPartRg E := ldPartByCol P.n (P.colsS on) v g

/-- The reads: one for each (claim, item). -/
abbrev ReadsS (on : ℕ → Bool) {Jc : Type} (v : Jc → ℕ) (f : Jc → ℕ → CForm E) : Type :=
  Σ j : Jc, Fin (P.rgS on (v j) (f j)).items.length

/-- The claims, with these readings and reads. -/
def clS (on : ℕ → Bool) {Jc : Type} [Fintype Jc] (v : Jc → ℕ) (f : Jc → ℕ → CForm E) (U : Type)
    [Fintype U] [DecidableEq U] [NeZero K.Cw] (wd nd : ℕ) {St J : Type} (pt : St → Jc → ℕ → E)
    (β val : St → Jc → E) (cAt : Jc → J) :
    LdPartCl (P.parS K on (P.ReadsS on v f) U wd nd).one E St J where
  Jc := Jc
  v := v
  f := f
  rg := fun j => P.rgS on (v j) (f j)
  rdAt := fun j i => ⟨j, i⟩
  pt := pt
  β := β
  val := val
  cAt := cAt

end LdPartD

namespace Spec

/-- States: under the hypotheses below, the naming has `LdPartNm.OK`. -/
def ldPartNmOf_ok : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (on : ℕ → Bool) (Rd U : Type) [Fintype Rd] [Fintype U] [DecidableEq U]
      [NeZero K.Cw] (wd nd : ℕ) (d0 : (P.parS K on Rd U wd nd).one.Row),
    0 < K.P → (∀ s, on s = true → s < P.n ∧ (P.seg s).cols ≤ K.Cw) → (P.nmS K on Rd U wd nd d0).OK

def ldPartNmOf_on : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (p k : ℕ),
    P.Props p → k < P.n →
    (∀ s, P.onBody k s = true → s < P.n) ∧
    (∀ s, P.onKept k s = true → s < P.n) ∧
    ∀ s, P.onKept k s = true → P.onBody (k + 1) s = true

/-- States: under the hypotheses below, every place that segment k reads lies in body k's shapes. -/
def ldPartNmOf_shape : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (p k : ℕ),
    P.Props p → k < P.n →
    ∀ q ∈ (P.seg k).places,
      q.1 < P.n ∧ q.2.1 < P.rowsS (P.onBody k) q.1 ∧ q.2.2 < P.colsS (P.onBody k) q.1

/-- States: under the hypotheses below, every cell atom of segment k has a reading in body k's
shapes. -/
def ldPartNmOf_reading : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (p k : ℕ),
    P.Props p → k < P.n →
    ∀ (v : ℕ) (g : ℕ → CForm E), (∀ b < 2 ^ v, ∀ t ∈ (g b).terms, t.2 ∈ (P.seg k).places) →
      (P.rgS (P.onBody k) v g).Of (P.rowsS (P.onBody k)) (P.colsS (P.onBody k)) v g

/-- States: for K.Cw not 0, the reads are tied. -/
def ldPartNmOf_ties : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (on : ℕ → Bool) (Jc : Type) [Fintype Jc] (v : Jc → ℕ) (f : Jc → ℕ → CForm E)
      (U : Type) [Fintype U] [DecidableEq U] [NeZero K.Cw] (wd nd : ℕ) (St J : Type)
      (pt : St → Jc → ℕ → E) (β val : St → Jc → E) (cAt : Jc → J)
      (d0 : (P.parS K on (P.ReadsS on v f) U wd nd).one.Row),
    (P.clS K on v f U wd nd pt β val cAt).Ties (P.nmS K on (P.ReadsS on v f) U wd nd d0)
      ((P.clS K on v f U wd nd pt β val cAt).stdW (P.nmS K on (P.ReadsS on v f) U wd nd d0) id)

end Spec
end Cb
