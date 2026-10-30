-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsCellQ.lean: TWO READINGS OF THE COMMITTED SYMBOLS ARE ONE: the caller's of the
lookup on a link's calls (`symU`, Johnson/Road/K4/K4PinsSym.lean: a read at one place of one table,
by `laidPlace`), of which K4's value's matrices are made, and the field cell of `dataQ`
(Johnson/Desc/Sound/FormsQ.lean: the batch's `dataOf` over the one accessor `tabQ`: a sum over the
layout's blocks and over all entries of a table), which the table's items on forms read. Lean
structures of conditions and theorems, by unfolding. No draw, no count.

  `BlocksOne bs R P`: A STATEMENT ON A LIST OF BLOCKS AND A TABLE's TWO NUMBERS OF BITS: at every
    table tab and every element (i, c) that `laidPlace` finds at (row, place): the sum over the
    blocks of `cellOfBlock` is the one entry tab (row + place · 2 ^ R). PROVED IN
    Johnson/Road/K4/K4PinsBlocks.lean, of blocks that pass the programs' own test and share no
    element.
  `CellOne A own a T r c`: THE CONDITIONS AT ONE CELL (r, c) OF ARRAY NUMBER T OF THE LINK's LIST.
    ON THE PLAN: the list names the array; the layout has it; `laidPlace` finds its place;
    `seatCalls` finds a seat, which lies in a main table of the caller's list. ON THE VERIFIER's
    STATE's PART a: its layout is the plan's; the frame finds the array's message as message number
    o; the book seats o, among own, AT THE SEAT OF THAT MEMBER; the row lies below the statement's
    number of rows of o;
    `BlocksOne` at the array's blocks and the statement's bits of o. "There is" on both sides.
  **`cell_dataQ`**: under `CellOne`: the caller's `valAt` at that cell, over the tuple out of t, is
    `(dataQ own a t.1).cell` at the array's link and name, at (r, c).
  `matsOfB`: matrices made of a `Bound`'s cells as `PinPlan.raw` makes them of the caller's symbols.
  **`raw_dataQ`**: under `CellOne` at every symbol of tl's sizes:
    `A.raw tl t = matsOfB A tl (dataQ own a t.1)`.

OBJECT: none of its own. USER: none yet; meant: whoever ties the table's item formsT m 3 "own" to
the road's sentence on the forms. LETTERS, filled by nobody: every field of `PinPlan`, tl, own, a.

Limits. K04_law IS NOT PROVED BY THIS. `CellOne` IS A PREMISE; IT HAS RUN NOWHERE. ITS SECOND HALF
SPEAKS OF THE VERIFIER's STATE (layout, frame, book, statement): it is for the table's promise to
give: that road is not typed here. `BlocksOne` IS A FIELD OF IT: its payer: K4PinsBlocks.lean's
`blocksOne_of`. `CellOne` IS A STRUCTURE WITH DATA (it lives in Type, not in Prop): whoever pays it
BUILDS the array's link and name, the layout's entry, the place, the member and the message's
number. It speaks of every symbol: no test by blocks is written. FIELD VALUES: no integer behind a
symbol is named.
-/
import Johnson.Road.K4.K4PinsSym
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls valAt laidPlace cellJ szOf)
open VerifiableInference.Desc.Sound (dataQ tabQ)
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.K9L (Bound dataOf cellOfBlock)
open Cb.Pv.Tail (cellValS)

/-- **A statement on a list of blocks**: the batch's sum is the one entry at the place that
`laidPlace` finds. -/
def BlocksOne (bs : List OnBytes.Params.LaidBlock) (R P : ℕ) : Prop :=
  ∀ (tab : ℕ → Cb.Gl.E) (i c : ℕ) (rp : ℕ × ℕ), laidPlace bs i c = some rp →
    (bs.map fun b => cellOfBlock b R P tab i c).sum = tab (rp.1 + rp.2 * 2 ^ R)

variable {Cells : Type} (A : PinPlan Cells)

/-- **The conditions at one cell**: on the plan, and on the verifier's state's part. -/
structure CellOne (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part) (T r c : ℕ) where
  bn : ℕ × String
  named : (A.D.arrayOf.getD A.link #[])[T]? = some bn
  ar : OnBytes.Params.ReqArray
  laid : OnBytes.reqArray A.D.layout bn.1 bn.2 = some ar
  rp : ℕ × ℕ
  place : laidPlace ar.blocks r c = some rp
  /-- the number of the member of the caller's list -/
  k : ℕ
  seat : seatCalls A.D A.link (.cell T r c) = some ⟨k, false, rp.1, rp.2⟩
  member : k < (sigListCalls A.D A.rad A.link).length
  rowIn : rp.1 < ((sigListCalls A.D A.rad A.link).get ⟨k, member⟩).1.mainRows
  placeIn : rp.2 < (pMain A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨k, member⟩).1).ell
  /-- the verifier's state's side -/
  layout : a.L.check.rows.layout = A.D.layout
  o : ℕ
  oracle : a.L.check.frame.whereIs bn.1 ar.message = some o
  seated : seatAt own a.d.book o = some (A.seatT ⟨k, member⟩)
  rowBelow : rp.1 < 2 ^ a.d.st.rowBits o .main
  blocks : BlocksOne ar.blocks (a.d.st.rowBits o .main) (a.d.st.placeBits o .main)

/-- **The two readings of a cell are one**, under `CellOne`. -/
theorem cell_dataQ (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part) (T r c : ℕ)
    (H : CellOne A own a T r c) (t : PinM Cells) :
    (valAt A.D.codes (sigListCalls A.D A.rad A.link) (seatCalls A.D A.link) (A.tuple t)
      (.cell T r c)).getD 0 = (dataQ own a t.1).cell H.bn.1 H.bn.2 r c := by
  have L1 : (valAt A.D.codes (sigListCalls A.D A.rad A.link) (seatCalls A.D A.link) (A.tuple t)
      (.cell T r c)).getD 0 = t.1 (A.seatT ⟨H.k, H.member⟩) false H.rp.1 H.rp.2 := by
    unfold valAt
    rw [H.seat]
    show (VerifiableInference.Desc.First.Look.readAt A.D.codes _
      (tupleOf A.D.codes _ A.seatT t) ⟨H.k, false, H.rp.1, H.rp.2⟩).getD 0 = _
    rw [readAt_tuple A.D.codes _ A.seatT t ⟨H.k, false, H.rp.1, H.rp.2⟩ H.member rfl H.rowIn
      H.placeIn, Option.getD_some]
  have R1 : (dataQ own a t.1).cell H.bn.1 H.bn.2 r c =
      t.1 (A.seatT ⟨H.k, H.member⟩) false H.rp.1 H.rp.2 := by
    show (match OnBytes.reqArray a.L.check.rows.layout H.bn.1 H.bn.2 with
      | none => (0 : Cb.Gl.E)
      | some ar =>
        match a.L.check.frame.whereIs H.bn.1 ar.message with
        | none => (0 : Cb.Gl.E)
        | some o =>
          (ar.blocks.map fun b =>
            cellOfBlock b (a.d.st.rowBits o .main) (a.d.st.placeBits o .main)
              (tabQ own a.d.st a.d.book t.1 o .main) r c).sum) = _
    rw [H.layout, H.laid]
    show (match a.L.check.frame.whereIs H.bn.1 H.ar.message with
        | none => (0 : Cb.Gl.E)
        | some o =>
          (H.ar.blocks.map fun b =>
            cellOfBlock b (a.d.st.rowBits o .main) (a.d.st.placeBits o .main)
              (tabQ own a.d.st a.d.book t.1 o .main) r c).sum) = _
    rw [H.oracle]
    show (H.ar.blocks.map fun b =>
      cellOfBlock b (a.d.st.rowBits H.o .main) (a.d.st.placeBits H.o .main)
        (tabQ own a.d.st a.d.book t.1 H.o .main) r c).sum = _
    rw [H.blocks _ r c H.rp H.place]
    unfold tabQ
    rw [H.seated]
    show t.1 (A.seatT ⟨H.k, H.member⟩) false
      ((H.rp.1 + H.rp.2 * 2 ^ a.d.st.rowBits H.o .main) % 2 ^ a.d.st.rowBits H.o .main)
      ((H.rp.1 + H.rp.2 * 2 ^ a.d.st.rowBits H.o .main) / 2 ^ a.d.st.rowBits H.o .main) = _
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt H.rowBelow,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt H.rowBelow, Nat.zero_add]
  rw [L1, R1]

/-- Matrices made of a `Bound`'s cells, as `PinPlan.raw` makes them of the caller's symbols. -/
def matsOfB (tl : HTailF2) (B : Bound Cb.Gl.E) (a r c : ℕ) : Cb.Gl.E :=
  ((cellJ (szOf tl) a r c).map (cellValS fun μ i c' =>
    B.cell (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).1
      (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).2 i.val
      c'.val)).getD 0

/-- **The value's raw matrices are made of `dataQ`'s cells**, under `CellOne` at every symbol of
tl's sizes. -/
theorem raw_dataQ (tl : HTailF2) (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part)
    (H : ∀ (μ : Fin (szOf tl).NM) (i : Fin (Alg.symRows ((szOf tl).m μ)))
      (c' : Fin ((szOf tl).k μ)), CellOne A own a (tl.gtTree.getD μ.val 0) i.val c'.val)
    (t : PinM Cells) : A.raw tl t = matsOfB A tl (dataQ own a t.1) := by
  funext x r c
  have e : (fun (μ : Fin (szOf tl).NM) (i : Fin (Alg.symRows ((szOf tl).m μ)))
      (c' : Fin ((szOf tl).k μ)) => symU A tl t μ.val i.val c'.val) =
      fun μ i c' => (dataQ own a t.1).cell
        (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).1
        (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).2 i.val c'.val :=
    funext fun μ => funext fun i => funext fun c' => by
      rw [(H μ i c').named, Option.getD_some]
      exact cell_dataQ A own a _ _ _ (H μ i c') t
  show ((cellJ (szOf tl) x r c).map (cellValS fun (μ : Fin (szOf tl).NM)
    (i : Fin (Alg.symRows ((szOf tl).m μ))) (c' : Fin ((szOf tl).k μ)) =>
      symU A tl t μ.val i.val c'.val)).getD 0 = _
  rw [e]
  rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cell_dataQ
#print axioms OnBytes.Road.K4.raw_dataQ
