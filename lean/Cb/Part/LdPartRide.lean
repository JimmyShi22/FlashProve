-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartRide.lean: this file defines the pair of relations (exact, for the honest prover;
relaxed, for knowledge soundness) that holds what is still to be proved of the later segments while
the sub-protocols of segment k run.

Book-keeping for a protocol that treats a request in segments. Definitions only. A partition
`P : LdPartD Cf` (Cb/Part/LdPartDef.lean) cuts a model's conditions into P.n segments, each with a
matrix of integer cells. The two worlds are the two relations of a record `IOR.Rels`
(Ior/Chain.lean). Cells are sent packed: `K.P` integer cells y_l in one field element, the sum of
`K.rdx`^l · y_l (K : `LdPartPk`; `pack`, Cb/Ld/LdRngAlg.lean).

Why: in this protocol's technical report (lean/CREDITS.md; by inspection) the relation at every
stage of segment k holds, beside the claims of the blocks that run, the conditions of all later
segments, copied by every
block. Cells are read off the messages that pack them as soon as those have been sent; before that
the witness holds them. Relaxed: the relaxed bound in the place of the honest one everywhere, and no
predicate on multiplicities.
The records of a request leave "what else is claimed" free.
For a model its relaxed part
cannot be "True": going
backwards through body k one learns segment k's conditions and must still hold those of
k + 1, .., n - 1, or the model's one step has nothing to give the relaxed relation from.


Why one width `Cw`: all bodies then have Cw columns, all matrices that a body holds are on the same
columns, and its packed rows, own and kept, cover its rectangle: a body's relation speaks of every
entry of that rectangle.

Main names:
  `LdPartGh`, `LdPartW`: one ghost and one further witness, the same types in all segments.
  `LdPartPk`, `LdPartOut`: the public parameters of packing, with one public width `Cw`; how the
    cells that have been sent are read at a stage with the open messages S. Told in their
    docstrings.
  `P.ride K k O x rc bitX`: the riding relation of segment k, on tuples ((message of the index,
    messages), (further witness, ghost)). x, rc read instance and record off the state; `bitX j` is
    a parameter: "the bits of layer j are the honest ones".
    `rel` (exact): the index's message holds an index; `O.pkX`; the ghost is below B in all shapes;
      every later layer is the packing of the ghost's matrix; every later layer's bits are the
      honest ones; all later segments' conditions at (instance, the matrix read off the index's
      message, the ghost's cells).
    `relR` (relaxed): `O.pkR`; every later layer is a packing of cells below 2 D; all later
      segments' conditions at (instance, that matrix, the relaxed world's cells).
    `on`: the statement decodes to an index of the index set; the request has the form.
    `core`: the ghost.

Limits: declared (by the same reading). One width, all matrices on the same columns: the report
lays the matrices of a segment along a diagonal. No error of soundness moves; two numbers do: its
bound on the window event has the widest single matrix of the segment where a bound that counts a
body's columns has Cw; its ternary matrix has the sum of the matrices' columns where this layout has
Cw. The report holds the later cells in the witness as cells; here their packings stand in the
further witness and the integers in the ghost: the same content under unique packing. Its relation
has the predicate on multiplicities for the next segment only; here the honest bits of all later
segments stand in the exact witness: more data, all determined by the cells.
This file says nothing on segment k's own conditions (they stand beside this relation at the
segment's entry: keys in tables, identities vanish, its bits valid) and the blocks' claims. It does
not say that O's letters are tied to each other and from stage to stage (Cb/Part/LdPartCells.lean;
the closing's places). No statement, no protocol.
Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartDef
import Cb.Ld.LdRngAlg
import Cb.Ld.LdWfIdx
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk

/-- The ghost: the integer cells of all segments, by (segment, row, column). It is the core of every
joint. -/
abbrev LdPartGh : Type := ℕ → ℕ → ℕ → ℤ

/-- The further witness: the data of the segments that have not been sent. `pk`: (segment, packed
row, column) ↦ packed entry. `bit`: (segment, number of a name) ↦ a bit of that segment's front
lookup's multiplicities (data that are sent with the cells, before the shift is drawn). -/
structure LdPartW (E : Type) where
  pk  : ℕ → ℕ → ℕ → E
  bit : ℕ → ℕ → E

/-- The public parameters of packing: `P` rows of cells in one, the radix `rdx` (written ϱ in the
formulas of the heads of Cb/Part), and one public width `Cw`: every layer is a full rectangle
(packed rows of the segment) × Cw columns, whatever the segment's own number of columns; beyond
these the ghost is read as 0. -/
structure LdPartPk where
  P : ℕ
  rdx : ℤ
  Cw : ℕ

/-- How the cells that have been sent are read at a stage with the open messages S. The fields are
letters. `A m`: the matrices (segment, row, column) read off the messages (for the value see
`LdPartNm.A`, Cb/Part/LdPartCells.lean). `pkX m g`: the messages' packed entries are the packing of
the ghost's rows that they hold, below the honest bound B. `pkR m`: they are a packing of cells
below the relaxed bound 2 D. -/
structure LdPartOut (E : Type) [Field E] (S : Sig E) where
  A   : S.Msg → ℕ → ℕ → ℕ → E
  pkX : S.Msg → LdPartGh → Prop
  pkR : S.Msg → Prop

namespace LdPartD
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
  (P : LdPartD Cf) (K : LdPartPk)

/-- the number of packed rows of segment j -/
def rp (j : ℕ) : ℕ := (2 ^ (P.seg j).rowsLog + K.P - 1) / K.P

/-- Segment j's matrix of the ghost, by (packed row, lane) and column below Cw; 0 below the last row
and beyond the last column. -/
def layX (g : LdPartGh) (j : ℕ) : Fin (P.rp K j) × Fin K.P → Fin K.Cw → ℤ :=
  fun r c =>
    if r.1.val * K.P + r.2.val < 2 ^ (P.seg j).rowsLog ∧ c.val < (P.seg j).cols then
      g j (r.1.val * K.P + r.2.val) c.val
    else 0

/-- Layer j of the further witness: its packed entries on (packed rows of segment j) × Cw columns.
-/
def layW (w : LdPartW E) (j : ℕ) : Fin (P.rp K j) → Fin K.Cw → E := fun i c => w.pk j i.val c.val

/-- The cells unpacked from layer j (`cells`, Cb/Ld/LdRngAlg.lean, at the relaxed bound 2 D), in E;
0 outside the shape; the zero matrix where the layer is no packing. -/
def cellsW (w : LdPartW E) (j : ℕ) : ℕ → ℕ → E := fun r c =>
  if h : (r / K.P < P.rp K j ∧ r % K.P < K.P) ∧ c < K.Cw then
    (if r < 2 ^ (P.seg j).rowsLog ∧ c < (P.seg j).cols then
        ((cells K.P (2 * P.D) K.rdx (P.layW K w j)
          (⟨r / K.P, h.1.1⟩, ⟨r % K.P, h.1.2⟩) ⟨c, h.2⟩ : ℤ) : E)
      else 0)
  else 0

variable {S : Sig E}

/-- The relaxed world's cells while segment k runs: segments ≤ k off the messages, segments > k off
the further witness. -/
def world (k : ℕ) (O : LdPartOut E S) (m : S.Msg) (w : LdPartW E) : ℕ → ℕ → ℕ → E :=
  fun s => if s ≤ k then O.A m s else P.cellsW K w s

/-- the matrix that is read off a message of the encoded index -/
def matU (U : Cf.conf.Msg) : ℕ → ℕ → F := P.matB fun n => (show Cf.Msg from U) (n.1, .inl n.2)

/-- The riding relation of segment k; the head tells its four fields. -/
def ride {St : Type} (k : ℕ) (O : LdPartOut E S) (x : St → Cf.Xm)
    (rc : St → Cf.conf.Rec) (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop) :
    IOR.Rels LdPartGh St Cf.conf.E0 ((Cf.conf.Msg × S.Msg) × (LdPartW E × LdPartGh)) where
  rel  := fun st _ t => (∃ i η, t.1.1 = Cf.conf.hold i η) ∧ O.pkX t.1.2 t.2.2 ∧ P.Below P.B t.2.2 ∧
    (∀ j, k < j → j < P.n → PackBy P.B K.rdx (P.layX K t.2.2 j) (P.layW K t.2.1 j)) ∧
    (∀ j, k < j → j < P.n → bitX j (x st) (P.matU t.1.1) t.2.2 (t.2.1.bit j)) ∧
    ∀ j, k < j → j < P.n → (P.seg j).Holds P.fmt (x st) (P.matU t.1.1) (castM (E := E) t.2.2)
  relR := fun a t =>
    O.pkR t.1.2 ∧
    (∀ j, k < j → j < P.n → Packed K.P (2 * P.D) K.rdx (P.layW K t.2.1 j)) ∧
    ∀ j, k < j → j < P.n → (P.seg j).Holds P.fmt (x a.1) (P.matU t.1.1) (P.world K k O t.1.2 t.2.1)
  on   := fun a => (Cf.conf.D a.2 (rc a.1)).isSome ∧ P.form (x a.1)
  core := fun t => t.2.2

end LdPartD

end Cb
