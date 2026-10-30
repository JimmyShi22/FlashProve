-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/AtS.lean: kind K13 at the state that the proof file's first chain carries
(Johnson/Desc/First/State.lean: S): the lens; and the blocks that stand in one place of the chain's
table of places, joined. Definitions with code; no theorem.

What the kind reads of S: rowsOwed, by S.noneWaits: S has two forms for "no count waits", none and
some 0, and the lens hands on none for both; what the walk over the links has left (out: the reply
as heard, the message of index masks, the pile); the statement, the book of trees and the number of
roots; and the record of the chain's end (here = mem: msg, ids, lin).
What it writes: rowsOwed; the statement; msg, ids, lin. The book and the roots are handed to the
effects on the statement and are not turned by them; they are not written back. The pile stays where
it lies: behind the batching the one row is read off lin's claim.
enter: S.enterMem, out of the finish; elsewhere nothing: the front refuses.
  atM3 p     the front, the batching and the quiet part as ONE block, under the batching's place.
  atM4 p b   W's commitment (another kind's block b) with the own group and (Eval) behind it, as ONE
             block, under b's place.
  fits p     the test on the plan that ties the kind's numbers to each other: the first chain; W's
             place is the next behind the batching's.

What is not claimed. That what the lens writes is read back as it was written, or that it turns
nothing else of S: no theorem stands in this file. set leaves a record that is not at the chain's
end as it is, without a refusal of its own: the blocks refuse there, since get? returns nothing. The
joined blocks ask nothing beyond what their parts ask: atM4 asks nothing of the block b that it is
handed; that b is W's commitment is the caller's. That a yes of a joined block means anything is the
matter of the kind's laws. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.State
import Johnson.Desc.K13.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open OnBytes
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **The lens.** -/
def atS : Lens S where
  enter := fun s =>
    match s.here with
    | .fin _ => some s.enterMem
    | _ => none
  get? := fun s =>
    match s.here with
    | .mem o =>
      some { owed := if s.noneWaits then none else s.rowsOwed, heard := s.out.reply,
             indexMasks := s.out.indexMasks,
             pile := s.out.pending, msg := o.msg, ids := o.ids, lin := o.lin,
             d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } }
    | _ => none
  set := fun s p =>
    match s.here with
    | .mem _ =>
      { s with st := p.d.st, rowsOwed := p.owed, here := .mem ⟨p.msg, p.ids, p.lin⟩ }
    | _ => s

/-- The kind's numbers speak of one chain's end: the first chain; W's commitment stands in the place
behind the batching's, with the own group behind it in that same place. -/
def fits (p : Where) : Bool := p.chain == 1 && p.pieceRows == p.piece + 1

/-- The front, the batching and the quiet part as one block, under the batching's place. -/
def atM3 (p : Where) : Block S Cl :=
  let b : Block S Cl :=
    ((frontB atS p).andThen "the front and the batching" (claimCombinationBlock atS p)).andThen
      "K13: the members' batching" (quietB atS p)
  { b with planOk := b.planOk && fits p }

/-- W's commitment, another kind's block, with the own group and (Eval) behind it: one block, under
that block's place. -/
def atM4 (p : Where) (commitW : Block S Cl) : Block S Cl :=
  commitW.andThen "W's commitment, the own group and (Eval)" (rowsB atS p)

end VerifiableInference.Desc.K13
