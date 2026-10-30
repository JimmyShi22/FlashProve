-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegLayout.lean: where every cell of the model is in the 25 matrices of cells: the dictionary
between names of cells and places.

Definitions and statements (Cm.Spec.lay_..); the proofs are in Cm/SegLayoutProofs.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

Why: In the protocol of a print of the technical report (lean/CREDITS.md) the prover sends
the cells of a segment as ONE integer matrix.
The model's relations (Cm/TargetPRel.lean, Policy/Rel/LedgerRel.lean) have as witness `All.Trace`:
functions on names of cells. This file is the dictionary.

Conventions: segments are numbered from 0: 2 g is the feed-forward segment of group g (g < 12),
2 g + 1 its attention segment, 24 the head. A family of matrices is a function (segment, row,
column) ↦ integer; no type depends on a size. Only a segment's own cells stand in its matrix. A
borrowed cell is read at its owner's place. Multiplicity bits are no cells.

Main names:
  `Hd`: how many features of the head's matrices hf and hr are cells: `Hd.main` (the head of
    Inst/Model/Head/), `Hd.plain` (the plain head of Cm/Head.lean). A parameter, because the valid
    names must be exactly those on which a relation puts its bound. `Hd.OK`: no more than the
    matrices hold; the statements that require it say so.
  `Name`, `Name.Valid`: the own names of all segments: a cell of ff g (x0 for g = 0 only), an own
    cell of att g, a feature of hf, hd, hr at a position.
  `stack`, `Name.place`: the place. Inside a segment the matrices of Inst/Model/ are one below the
    other in slots of 2^16 rows (the height of the tallest); a matrix with more columns than the
    segment's width is cut into parts of that width, which take consecutive slots
    (af: 3 parts, hf: 4). Row and column inside a matrix are the addresses of Inst/Model/
    (`FFSeg.addr`, `AttSeg.addr`, `Head.rowOf`, `Head.colOf`).
  `rowsLog`, `cols`: the shapes: 2^19 rows and 5,990 columns; 2^18 and 7,200; 2^19 and 4,816.
  `kept`: the rows that are handed on after a segment: after 2 g the slots qa and xout of 2 g;
    after 2 g + 1 the slot xout of 2 g.
Stated (`Cm.Spec`); these six are each told whole in their docstrings. For `h.OK` and under the
further hypotheses of the statements: every own cell is inside the matrix of its segment
(`lay_inShape`); two own cells do not stand at one place (`lay_inj`); from a trace to matrices and
back gives the same cells at all valid names (`lay_ofMat_toMat`); all own cells are below B if and
only if all entries of the matrices are (`lay_below`); a cell of an earlier segment is read in a
row that is kept after every segment in between (`lay_keeps`). Without `h.OK`, under the hypotheses
of its statement: what a segment reads of the trace of matrices is the entry at the owner's place
(`lay_read_ofMat`).

Limits, declared. (1) Slots. A matrix of fewer than 2^16 rows (ad, ar, ah, hd, hr) is followed by
zero rows up to the next slot; "one below the other without gaps" would give the same numbers of
rows (2^19, 2^18, 2^19) after padding to a power of two.
(2) The slot xin of a feed-forward segment holds cells for g = 0 only; it is zero in the others.
(3) `toMat` is defined with "the valid name that stands at this place, if there is one", by choice;
as, for `h.OK`, places are injective on valid names (`lay_inj`) nothing depends on the choice
(`lay_toMat_place`). `ofMat`, which the extractor uses, is defined without choice. At `Hd.plain` it
is the field `ofMat` of the model's partition (`targetPart`,
Cm/TargetPart.lean).
This file says nothing on conditions, keys or identities, but that which names of identities are
valid, and the numbers `used`, do not depend on the table of scales (`lay_valid_refK`); nothing on
codes or protocols.
Terms: lean/GLOSSARY.md.
-/
import Cm.RelBase
import Cm.Head
import Inst.Model.All.Addr
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg

open Inst.Model Inst.Model.All

/- DF, DA, KA (Inst/Model/All): the reference sizes of the two kinds of segments of the layers, and
the number of bits fh: 2^fh features stand in a column of the attention segment's matrix ah
(`AttSeg.Cols`) -/

/-- a place: (segment, row, column) -/
abbrev Place : Type := ℕ × ℕ × ℕ

/-- a family of matrices at a place -/
def at' (M : ℕ → ℕ → ℕ → ℤ) (p : Place) : ℤ := M p.1 p.2.1 p.2.2

/-- How many features of hf and of hr are cells. -/
structure Hd where
  nf : ℕ
  nr : ℕ

def Hd.main : Hd := ⟨Head.nFeat .hf, Head.nFeat .hr⟩
def Hd.plain : Hd := ⟨Plain.nHf, Plain.nHr⟩
/-- no more than the matrices hold -/
def Hd.OK (h : Hd) : Prop := h.nf ≤ Head.nFeat .hf ∧ h.nr ≤ Head.nFeat .hr

/-! ## Names -/

/-- The names among which the own names of all segments are (`Name.Valid`). -/
inductive Name
  | ff (g : ℕ) (c : FFSeg.Cell)
  | att (g : ℕ) (c : AttSeg.Raw)
  | hf (φ i : ℕ)
  | hd (φ i : ℕ)
  | hr (φ i : ℕ)

/-- which names are own cells -/
def Name.Valid (h : Hd) : Name → Prop
  | .ff g c => g < nGr ∧ c.Valid DF ∧ (c.X = .x0 → g = 0)
  | .att g c => g < nGr ∧ c.Valid DA ∧ c.Own = true
  | .hf φ i => φ < h.nf ∧ i < Head.nT
  | .hd φ i => φ < Head.nFeat .hd ∧ i < Head.nT
  | .hr φ i => φ < h.nr ∧ i < Head.nT

instance (h : Hd) (n : Name) : Decidable (n.Valid h) := by
  cases n <;> unfold Name.Valid <;> infer_instance

/-! ## Places -/

/-- rows of a slot -/
def hSlot : ℕ := 2 ^ 16

/-- the widths of the three kinds of segments -/
def colsFF : ℕ := FFSeg.afCols DF
def colsAtt : ℕ := AttSeg.nCol DA KA AttSeg.Calls.ref .as
def colsHead : ℕ := Head.n2 .hf / 4

/-- (row, column) of a matrix that begins at a slot, in a segment of width W: column c lies in part
c / W -/
def stack (W slot row col : ℕ) : ℕ × ℕ := ((slot + col / W) * hSlot + row, col % W)

def slotFF : FFSeg.Mx → ℕ
  | .af => 0 | .ad => 3 | .ar => 4 | .qa => 5 | .xin => 6 | .xout => 7 | .b => 8

def slotAtt : AttSeg.Mx → ℕ
  | .as => 0 | .ah => 1 | .ao => 2 | .b => 3 | .qa => 3

def plFF (c : FFSeg.Cell) : ℕ × ℕ :=
  stack colsFF (slotFF (FFSeg.addr DF c).1) (FFSeg.addr DF c).2.1 (FFSeg.addr DF c).2.2
def plAtt (c : AttSeg.Raw) : ℕ × ℕ :=
  stack colsAtt (slotAtt (AttSeg.addr DA KA c).1)
    (AttSeg.addr DA KA c).2.1 (AttSeg.addr DA KA c).2.2

/-- The place of a name. -/
def Name.place : Name → Place
  | .ff g c => (2 * g, plFF c)
  | .att g c => (2 * g + 1, plAtt c)
  | .hf φ i => (24, stack colsHead 0 (Head.rowOf .hf φ i) (Head.colOf .hf φ))
  | .hd φ i => (24, stack colsHead 4 (Head.rowOf .hd φ i) (Head.colOf .hd φ))
  | .hr φ i => (24, stack colsHead 5 (Head.rowOf .hr φ i) (Head.colOf .hr φ))

/-- the number of segments -/
def nSeg : ℕ := 25

/-- the matrix of segment s has 2^(rowsLog s) rows and cols s columns -/
def rowsLog (s : ℕ) : ℕ := if s % 2 = 1 then 18 else 19
def cols (s : ℕ) : ℕ := if s = 24 then colsHead else if s % 2 = 1 then colsAtt else colsFF

/-- a place lies in the matrix of its segment -/
def InShape (p : Place) : Prop := p.1 < nSeg ∧ p.2.1 < 2 ^ rowsLog p.1 ∧ p.2.2 < cols p.1

/-! ## Traces and matrices -/

/-- a trace at a name -/
def get (T : Trace) : Name → ℤ
  | .ff g c => T.ff g c
  | .att g c => T.att g c
  | .hf φ i => T.hf φ i
  | .hd φ i => T.hd φ i
  | .hr φ i => T.hr φ i

open Classical in
/-- The matrices of a trace: at the place of a valid name the cell (for `h.OK`: Limits (3)), 0
elsewhere. -/
def toMat (h : Hd) (T : Trace) : ℕ → ℕ → ℕ → ℤ := fun s r c =>
  if e : ∃ n : Name, n.Valid h ∧ n.place = (s, r, c) then get T e.choose else 0

/-- matrices at a name: the entry at its place if the name is valid, 0 if not -/
def rd (h : Hd) (M : ℕ → ℕ → ℕ → ℤ) (n : Name) : ℤ := if n.Valid h then at' M n.place else 0

/-- The trace of matrices. -/
def ofMat (h : Hd) (M : ℕ → ℕ → ℕ → ℤ) : Trace where
  ff g c := rd h M (.ff g c)
  att g c := rd h M (.att g c)
  hf φ i := rd h M (.hf φ i)
  hd φ i := rd h M (.hd φ i)
  hr φ i := rd h M (.hr φ i)

/-! ## Who owns what a segment reads -/

/-- the feed-forward segment of group g reads the cell c under this own name: x0 of a later group
is x8 of the group before -/
def ownFF (g : ℕ) (c : FFSeg.Cell) : Name :=
  if c.X = .x0 ∧ 0 < g then .ff (g - 1) { c with X := .x8 } else .ff g c

/-- the attention segment of group g reads the cell c under this own name: qry, out, key, val are
q, o, kx, v of the feed-forward segment of the group -/
def ownAtt (g : ℕ) : AttSeg.Raw → Name
  | .qry k b g' i n => .ff g ⟨.q, k, DA.lamOf b, DA.ch * DA.head g' b + n, i⟩
  | .out k b g' i n => .ff g ⟨.o, k, DA.lamOf b, DA.ch * DA.head g' b + n, i⟩
  | .key k lam g' j n => .ff g ⟨.kx, k, lam, DA.ch * g' + n, j⟩
  | .val k lam g' j n => .ff g ⟨.v, k, lam, DA.ch * g' + n, j⟩
  | c => .att g c

/-- the head reads feature φ of x at position i under this own name: x8 of the last feed-forward
segment -/
def ownX (φ i : ℕ) : Name := .ff (nGr - 1) ⟨.x8, φ / 5120, 0, φ % 5120, i⟩

/-- The places that a segment reads. -/
def reads (h : Hd) (s : ℕ) : Set Place :=
  {p | (∃ g c, s = 2 * g ∧ g < nGr ∧ c.Valid DF ∧ p = (ownFF g c).place) ∨
    (∃ g c, s = 2 * g + 1 ∧ g < nGr ∧ c.Valid DA ∧ p = (ownAtt g c).place) ∨
    (s = 24 ∧ ((∃ n : Name, n.Valid h ∧ n.place.1 = 24 ∧ p = n.place) ∨
        ∃ φ i, φ < Head.nFeat .x ∧ i < Head.nT ∧ p = (ownX φ i).place))}

/-- the rows of a slot of a segment -/
def slotRows (s slot : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range hSlot).image fun r => (s, slot * hSlot + r)

/-- The rows that are handed on after segment k. -/
def kept (k : ℕ) : Finset (ℕ × ℕ) :=
  if k < 24 then (if k % 2 = 0 then slotRows k 5 ∪ slotRows k 7 else slotRows (k - 1) 7) else ∅

/-- every own cell is below B in absolute value -/
def BelowN (h : Hd) (B : ℤ) (T : Trace) : Prop := ∀ n : Name, n.Valid h → |get T n| < B

end Cm.Seg

namespace Cm.Spec
open Cm.Seg Inst.Model Inst.Model.All

/-- States the figures, and `Hd.OK` of `Hd.main` and `Hd.plain`. -/
def lay_figures : Prop :=
  hSlot = 65536 ∧ colsFF = 5990 ∧ colsAtt = 7200 ∧ colsHead = 4816 ∧ Hd.main.OK ∧ Hd.plain.OK

/-- States: for `h.OK`, every own cell is inside the matrix of its segment. -/
def lay_inShape : Prop := ∀ h : Hd, h.OK → ∀ n : Name, n.Valid h → InShape n.place

/-- States: for `h.OK`, two own cells do not stand at one place. -/
def lay_inj : Prop :=
  ∀ h : Hd, h.OK → ∀ n n' : Name, n.Valid h → n'.Valid h → n.place = n'.place → n = n'

/-- States: for `h.OK`, the matrices of a trace hold a cell at its place, and (`lay_toMat_off`, for
every h) 0 where no cell stands. -/
def lay_toMat_place : Prop :=
  ∀ h : Hd, h.OK → ∀ (T : Trace) (n : Name), n.Valid h → at' (toMat h T) n.place = get T n
def lay_toMat_off : Prop :=
  ∀ (h : Hd) (T : Trace) (p : Place),
    (¬ ∃ n : Name, n.Valid h ∧ n.place = p) → at' (toMat h T) p = 0

/-- States: the trace of matrices holds at a valid name the entry at its place, at every other name
0. -/
def lay_ofMat_get : Prop := ∀ (h : Hd) (M : ℕ → ℕ → ℕ → ℤ) (n : Name), get (ofMat h M) n = rd h M n

/-- States: for `h.OK`, from a trace to matrices and back: the same cells at all valid names. -/
def lay_ofMat_toMat : Prop :=
  ∀ h : Hd, h.OK → ∀ (T : Trace) (n : Name), n.Valid h → get (ofMat h (toMat h T)) n = get T n

/-- States: for `h.OK`, from matrices to a trace and back: the same entries at places of cells, 0
elsewhere. -/
def lay_toMat_ofMat : Prop :=
  ∀ h : Hd, h.OK →
    ∀ (M : ℕ → ℕ → ℕ → ℤ),
      (∀ n : Name, n.Valid h → at' (toMat h (ofMat h M)) n.place = at' M n.place) ∧
      ∀ p : Place, (¬ ∃ n : Name, n.Valid h ∧ n.place = p) → at' (toMat h (ofMat h M)) p = 0

/-- States: for `h.OK`, `ofMat` reads the matrices inside their shapes only. -/
def lay_ofMat_congr : Prop :=
  ∀ h : Hd, h.OK →
    ∀ M M' : ℕ → ℕ → ℕ → ℤ, (∀ p : Place, InShape p → at' M p = at' M' p) → ofMat h M = ofMat h M'

/-- States: what a segment reads is the trace at the owner's name (that this name is valid, under
the hypotheses of its statement: `lay_own_valid`): the three readings of Inst/Model/All/Trace.lean,
for every trace and all names. -/
def lay_own : Prop :=
  ∀ T : Trace,
    (∀ g c, T.vFF g c = get T (ownFF g c)) ∧
    (∀ g c, T.vAtt g c = get T (ownAtt g c)) ∧
    T.vHead.hf = T.hf ∧ T.vHead.hd = T.hd ∧ T.vHead.hr = T.hr ∧
    ∀ φ i, T.vHead.x φ i = get T (ownX φ i)

/-- States: for g < `nGr` and a valid cell (for the head: a feature and a position in range), the
owner's name is valid. -/
def lay_own_valid : Prop :=
  ∀ h : Hd,
    (∀ g < nGr, ∀ c : FFSeg.Cell, c.Valid DF → (ownFF g c).Valid h) ∧
    (∀ g < nGr, ∀ c : AttSeg.Raw, c.Valid DA → (ownAtt g c).Valid h) ∧
    ∀ φ < Head.nFeat .x, ∀ i < Head.nT, (ownX φ i).Valid h

/-- States: for g < `nGr` and a valid cell (for the head: a feature and a position in range), every
reading of a segment, own or borrowed, is an entry of the matrices at the owner's place: for the
trace of matrices .. -/
def lay_read_ofMat : Prop :=
  ∀ h : Hd, ∀ M : ℕ → ℕ → ℕ → ℤ,
    (∀ g < nGr, ∀ c : FFSeg.Cell, c.Valid DF → (ofMat h M).vFF g c = at' M (ownFF g c).place) ∧
    (∀ g < nGr, ∀ c : AttSeg.Raw, c.Valid DA → (ofMat h M).vAtt g c = at' M (ownAtt g c).place) ∧
    (∀ φ < h.nf, ∀ i < Head.nT, (ofMat h M).vHead.hf φ i = at' M (Name.hf φ i).place) ∧
    (∀ φ < Head.nFeat .hd, ∀ i < Head.nT, (ofMat h M).vHead.hd φ i = at' M (Name.hd φ i).place) ∧
    (∀ φ < h.nr, ∀ i < Head.nT, (ofMat h M).vHead.hr φ i = at' M (Name.hr φ i).place) ∧
    ∀ φ < Head.nFeat .x, ∀ i < Head.nT, (ofMat h M).vHead.x φ i = at' M (ownX φ i).place

/-- .. and, for `h.OK`, for the matrices of a trace. -/
def lay_read_toMat : Prop :=
  ∀ h : Hd, h.OK →
    ∀ T : Trace,
      (∀ g < nGr, ∀ c : FFSeg.Cell, c.Valid DF → T.vFF g c = at' (toMat h T) (ownFF g c).place) ∧
      (∀ g < nGr, ∀ c : AttSeg.Raw, c.Valid DA → T.vAtt g c = at' (toMat h T) (ownAtt g c).place) ∧
      (∀ φ < h.nf, ∀ i < Head.nT, T.vHead.hf φ i = at' (toMat h T) (Name.hf φ i).place) ∧
      (∀ φ < Head.nFeat .hd, ∀ i < Head.nT, T.vHead.hd φ i = at' (toMat h T) (Name.hd φ i).place) ∧
      (∀ φ < h.nr, ∀ i < Head.nT, T.vHead.hr φ i = at' (toMat h T) (Name.hr φ i).place) ∧
      ∀ φ < Head.nFeat .x, ∀ i < Head.nT, T.vHead.x φ i = at' (toMat h T) (ownX φ i).place

/-- States: for `h.OK`, from a trace to matrices and back: the three readings are the same, for
g < `nGr` at valid cells (for the head: at features and positions in range). -/
def lay_same_readings : Prop :=
  ∀ h : Hd, h.OK →
    ∀ T : Trace,
      (∀ g < nGr, ∀ c : FFSeg.Cell, c.Valid DF → (ofMat h (toMat h T)).vFF g c = T.vFF g c) ∧
      (∀ g < nGr, ∀ c : AttSeg.Raw, c.Valid DA → (ofMat h (toMat h T)).vAtt g c = T.vAtt g c) ∧
      (∀ φ < h.nf, ∀ i < Head.nT, (ofMat h (toMat h T)).vHead.hf φ i = T.vHead.hf φ i) ∧
      (∀ φ < Head.nFeat .hd, ∀ i < Head.nT, (ofMat h (toMat h T)).vHead.hd φ i = T.vHead.hd φ i) ∧
      (∀ φ < h.nr, ∀ i < Head.nT, (ofMat h (toMat h T)).vHead.hr φ i = T.vHead.hr φ i) ∧
      ∀ φ < Head.nFeat .x, ∀ i < Head.nT, (ofMat h (toMat h T)).vHead.x φ i = T.vHead.x φ i

/-- States, on bounds: for `h.OK`, all own cells are below B ⇔ all entries of the matrices are
(B > 0). -/
def lay_below : Prop :=
  ∀ h : Hd, h.OK →
    ∀ (B : ℤ) (T : Trace), 0 < B → (BelowN h B T ↔ ∀ p : Place, InShape p → |at' (toMat h T) p| < B)

/-- States: for `h.OK`, a segment reads its own cells and cells of earlier segments, inside their
shapes. -/
def lay_reads : Prop := ∀ h : Hd, h.OK → ∀ s < nSeg, ∀ p ∈ reads h s, p.1 ≤ s ∧ InShape p

/-- States: for `h.OK`, a cell of an earlier segment is read in a row that is kept after every
segment in between. -/
def lay_keeps : Prop :=
  ∀ h : Hd, h.OK → ∀ s < nSeg, ∀ p ∈ reads h s, ∀ k, p.1 ≤ k → k < s → (p.1, p.2.1) ∈ kept k

/-- States: only rows of matrices are kept. -/
def lay_keptIn : Prop := ∀ k, ∀ q ∈ kept k, q.1 ≤ k ∧ q.1 < nSeg ∧ q.2 < 2 ^ rowsLog q.1

/-- States: what is kept after segment k + 1 is a row of that segment or was kept after segment
k. -/
def lay_keptStep : Prop := ∀ k, ∀ q ∈ kept (k + 1), q.1 = k + 1 ∨ q ∈ kept k

/-- States: the names of an attention segment's cells do not depend on the table of scales: the
sizes at a table differ from the reference sizes in the number of live rows of the exponential
alone, which no name reads. Likewise `lamOf`, `head` and `ch`, from which the owner's name is
built, which names of identities are valid, and the numbers `used`. -/
def lay_valid_refK : Prop :=
  ∀ u0 : ℕ,
    (∀ c : AttSeg.Raw, c.Valid (AttSeg.Dim.refK u0) ↔ c.Valid DA) ∧
    (∀ j : AttSeg.Idn, j.Valid (AttSeg.Dim.refK u0) ↔ j.Valid DA) ∧
    (∀ b, (AttSeg.Dim.refK u0).lamOf b = DA.lamOf b) ∧
    (∀ g b, (AttSeg.Dim.refK u0).head g b = DA.head g b) ∧
    (AttSeg.Dim.refK u0).ch = DA.ch ∧
    ∀ c, (AttSeg.Dim.refK u0).used c = DA.used c

/-- States: no row is kept in vain: every kept row holds a cell that a later segment reads. -/
def lay_kept_used : Prop :=
  ∀ h : Hd, ∀ k, ∀ q ∈ kept k, ∃ s, k < s ∧ s < nSeg ∧ ∃ p ∈ reads h s, (p.1, p.2.1) = q

end Cm.Spec
