-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/CellQ.lean: SHORT NAMES FOR WHAT A SEGMENT'S MESSAGES HOLD, OFF THE TABLE'S WITNESS: for
a kind's law that speaks of a matrix's cells and need not open hid. Two definitions, three lemmas by
unfolding. No protocol's soundness is said.

A message holds SYMBOLS; a matrix's cells are the integers whose packing the symbols are.
  `ownQ … w k`: segment k's own list of matrices, in integers: the model's owner's `ownOf` at the
    symbols that segment k reads off the witness (`symAt` at `readAt`: the one accessor, at the seat
    of the segment's own copy).
  `cellQ … k w μ r c`: its entry (matrix μ, row r, column c), cast into the field.
  `ownQ_at`: it is that owner's `ownAt` at the messages as segment k reads them.
  `hidAtSeat_hid`: hid off the witness is that owner's `hidOf` at `ownQ`.
  `base_at`: the field base of `hidAtSeat` is the library's `Base` at these symbols.

Limits. WHERE THE COMMITTED SYMBOLS ARE NO PACKING OF SMALL INTEGERS `ownQ` IS 0 IN THAT COLUMN:
that they are one is what `Base` says (the item "constr k small"). `hidOf` takes THE OWNER's array
where a segment only reads: (hid w)'s lists are `ownQ`'s only where reader's and owner's readings
agree. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (readAt SeatsNamed GroupsSeated MsgT Mem)

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
  (s : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- **Segment by segment, the matrices in integers, off the witness.** -/
def ownQ (w : Wit Cells Tok MsgT) : ℕ → Mats ℤ :=
  ownOf s fun k => symAt (s k) (seat k) (readAt cs arr ms N k w)

/-- **A cell, in the field.** -/
def cellQ (k : ℕ) (w : Wit Cells Tok MsgT) (μ r c : ℕ) : VerifiableInference.OnPublicFiles.Flat.GE :=
  ((ownQ cs arr ms N s seat w k μ r c : ℤ) : VerifiableInference.OnPublicFiles.Flat.GE)

theorem ownQ_at (w : Wit Cells Tok MsgT) (k : ℕ) :
    ownQ cs arr ms N s seat w k = ownAt s seat (readAt cs arr ms N k w) k := rfl

theorem hidAtSeat_hid (X : Model.Verify.Public) {P : Type} {rows cols : ℕ}
    (tokV : Tok → Fin ppref.V) (req : P × TS → TReq)
    (dec : P × TS → Strs → Option (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE))
    (hN : SeatsNamed arr N s seat) (hG : GroupsSeated ms N) (w : Wit Cells Tok MsgT) :
    (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).hid w =
      hidOf X (tokV w.tok) (ownQ cs arr ms N s seat w) := rfl

theorem base_at (X : Model.Verify.Public) {P : Type} {rows cols : ℕ}
    (tokV : Tok → Fin ppref.V) (req : P × TS → TReq)
    (dec : P × TS → Strs → Option (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE))
    (hN : SeatsNamed arr N s seat) (hG : GroupsSeated ms N) (k : ℕ) (w : Wit Cells Tok MsgT) :
    (hidAtSeat X cs arr ms N s seat tokV req dec hN hG).base k w =
      Cb.Pv.Tail.Base (symAt (s k) (seat k) (readAt cs arr ms N k w)) := rfl

end

#print axioms ownQ_at
#print axioms hidAtSeat_hid
#print axioms base_at

end P5J
