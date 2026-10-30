-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/All/Addr.lean: lender and borrower read one entry: the row and the column of a borrowed
cell in the borrower's matrix are those of the lender's cell in the lender's matrix.

A cell that two segments read is owned by one of them, the lender, and borrowed by the other.
The protocol reads one packed matrix, sent by the lender. The readings of
Inst/Model/All/Trace.lean (`bor`, `vFF`, `vHead`) pair names of cells; here: the address maps of
the three kinds agree on these pairs, at the reference parameters, for all names, valid or not.
Only row and column can be equated: the three kinds have separate types for the names of their
matrices (qa of a feed-forward and of an attention segment; xout, xin, and x of the head), and xin
and xout are two names of one type.
Notation:
  the three kinds (of segments): feed-forward, attention, the head (Inst/Model/All/Trace.lean).
  `DF`, `DA`: `FFSeg.Dim.ref`, `AttSeg.Dim.ref`, the sizes at "the reference parameters"
    (Inst/Model/FF/Index.lean, Inst/Model/Att/Index.lean).
  `KA`: `AttSeg.Cols.ref`, an `AttSeg.Cols`: "a column of ah holds 2^fh features"
    (Inst/Model/Att/Trace.lean).
  `FFSeg.addr D c`, `AttSeg.addr D K c`: of type `Mx × ℕ × ℕ`, "the matrix, the row and the column
    of a cell" (Inst/Model/FF/Index.lean): `.1` is the matrix, `.2` the pair of row and column.
  `⟨X, k, inst, j, i⟩`: an `FFSeg.Cell`: "the array, the number k of the cell in a value, the
    instance, the channel j and the position i" (Inst/Model/FF/Index.lean).
  `.qry k b g i n`, `.key k lam g j n` (`.out`, `.val` alike): an `AttSeg.Raw`, "The names of the
    cells (without the multiplicity bits)."; "k is the number of the cell in a value of several
    cells" (Inst/Model/Att/Trace.lean).
  g, b, i, j, n, lam: natural numbers (Inst/Model/Att/Index.lean): "key/value heads g"; "pairs b =
    na λ + a of a layer λ of the segment and the number a of a query head among those of its
    key/value head"; "positions i, j"; "channels n"; lam: a layer λ of the segment.
  `lamOf b`: "λ(b)"; `head g b`: "the query head h = na g + a(b) that reads key/value head g"; `ch`:
    the number of "channels n"; `nG`: of "key/value heads g"; `nl`: of "layers in a segment".
  φ: a natural number, a feature of x of the head: "feature 5,120 l + j is cell l of channel j" (the
    comment at the top of Inst/Model/All/Trace.lean).
Terms: lean/GLOSSARY.md.
-/
import Inst.Model.All.NoWrap

set_option autoImplicit false

namespace Inst.Model.All

abbrev KA : AttSeg.Cols := AttSeg.Cols.ref

theorem addr_qry (k b g i n : ℕ) :
    (FFSeg.addr DF ⟨.q, k, DA.lamOf b, DA.ch * DA.head g b + n, i⟩).2 =
      (AttSeg.addr DA KA (.qry k b g i n)).2 := by
  have e : FFSeg.feat DF .q k (DA.lamOf b) (DA.ch * DA.head g b + n) =
      DA.nH * DA.ch * (DA.nl * k + DA.lamOf b) + DA.ch * DA.head g b + n := by
    show 0 + (k * 4 + DA.lamOf b) * 5120 + (DA.ch * DA.head g b + n) =
      40 * 128 * (4 * k + DA.lamOf b) + DA.ch * DA.head g b + n
    ring
  show FFSeg.featAt DF .qa _ i = AttSeg.featAt DA 6 _ i
  rw [e]
  rfl

theorem addr_out (k b g i n : ℕ) :
    (FFSeg.addr DF ⟨.o, k, DA.lamOf b, DA.ch * DA.head g b + n, i⟩).2 =
      (AttSeg.addr DA KA (.out k b g i n)).2 := by
  have e : FFSeg.feat DF .o k (DA.lamOf b) (DA.ch * DA.head g b + n) =
      2 * DA.nl * DA.nH * DA.ch + 4 * DA.nl * DA.nG * DA.ch +
        DA.nH * DA.ch * (DA.nl * k + DA.lamOf b) + DA.ch * DA.head g b + n := by
    show 57344 + (k * 4 + DA.lamOf b) * 5120 + (DA.ch * DA.head g b + n) =
      2 * 4 * 40 * 128 + 4 * 4 * 8 * 128 + 40 * 128 * (4 * k + DA.lamOf b) + DA.ch * DA.head g b + n
    ring
  show FFSeg.featAt DF .qa _ i = AttSeg.featAt DA 6 _ i
  rw [e]
  rfl

theorem addr_key (k lam g j n : ℕ) :
    (FFSeg.addr DF ⟨.kx, k, lam, DA.ch * g + n, j⟩).2 =
      (AttSeg.addr DA KA (.key k lam g j n)).2 := by
  have e : FFSeg.feat DF .kx k lam (DA.ch * g + n) =
      2 * DA.nl * DA.nH * DA.ch + DA.nG * DA.ch * (DA.nl * k + lam) + DA.ch * g + n := by
    show 40960 + (k * 4 + lam) * 1024 + (DA.ch * g + n) =
      2 * 4 * 40 * 128 + 8 * 128 * (4 * k + lam) + DA.ch * g + n
    ring
  show FFSeg.featAt DF .qa _ j = AttSeg.featAt DA 6 _ j
  rw [e]
  rfl

theorem addr_val (k lam g j n : ℕ) :
    (FFSeg.addr DF ⟨.v, k, lam, DA.ch * g + n, j⟩).2 =
      (AttSeg.addr DA KA (.val k lam g j n)).2 := by
  have e : FFSeg.feat DF .v k lam (DA.ch * g + n) =
      2 * DA.nl * DA.nH * DA.ch + 2 * DA.nl * DA.nG * DA.ch +
        DA.nG * DA.ch * (DA.nl * k + lam) + DA.ch * g + n := by
    show 49152 + (k * 4 + lam) * 1024 + (DA.ch * g + n) =
      2 * 4 * 40 * 128 + 2 * 4 * 8 * 128 + 8 * 128 * (4 * k + lam) + DA.ch * g + n
    ring
  show FFSeg.featAt DF .qa _ j = AttSeg.featAt DA 6 _ j
  rw [e]
  rfl

/-- x of the head and x8 of the last feed-forward segment -/
theorem addr_head (φ i : ℕ) :
    (FFSeg.addr DF ⟨.x8, φ / 5120, 0, φ % 5120, i⟩).2 = (Head.rowOf .x φ i, Head.colOf .x φ) := by
  have e : FFSeg.feat DF .x8 (φ / 5120) 0 (φ % 5120) = φ := by
    show 0 + (φ / 5120 * 1 + 0) * 5120 + φ % 5120 = φ
    omega
  show FFSeg.featAt DF .xout _ i = _
  rw [e]
  rfl

/-- x0 in xin and x8 in xout are in the same row and column -/
theorem addr_x0 (k inst j i : ℕ) :
    (FFSeg.addr DF ⟨.x0, k, inst, j, i⟩).2 = (FFSeg.addr DF ⟨.x8, k, inst, j, i⟩).2 := rfl

end Inst.Model.All
