-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/OwedLaid.lean (kind K9; for the table of conditions on the statement): FIVE
TESTS WITH CODE ON THE FIRST CHAIN's CARRIED RECORD, for the two borders INSIDE K9's three pieces
(behind the batching; behind the block that Link.blocksInOrder lays after it): what K9's law takes there as
public facts, so that the number "the plan's claims and the ties' and reads' indices are at most the
round's rows" is paid by the one equation's own yes and not promised in front of the batching.
  K9.owedIs rows s   the rows that are still owed a count are the batching round's: made by the draw
                     (owed := some p.rows), asked by the one equation's piece.
  K9.laidIs s        the indices that the smallness test's equations are said to take (laidOf tl)
                     are topOf tl funs (OnBytes/Tie/Pv/Tail/EndSpread.lean): made by
                     "K8.equations".
  K9.laidOk s        THE WEAK FORM, on which the law of a link leans: whatever number is said to
                     be laid is topOf tl funs. Foretold: yes at every border (idle before
                     "K8.equations").
  K9.rowsFit rows s  the sentence itself: planClaimsF + topOf tl funs ≤ rows.
  K9.groupIs g s     the group on which the segment's own check lays its rows (L.check.group) is g:
                     the plan's number of the segment's group (the table's N.groupAt m).
  K9.owedLaidWhy     the first three under names, with what each reads, and the check's group: for a
                     run that says which fails.
EACH IS "YES" WHERE WHAT IT READS IS NOT THERE (no segment open; no list of tables yet): as the
law's premise has it (Johnson/Desc/First/Batch/Law/RowsRide.lean: hon2; rowsAt): "for all parts,
records and lists that the state has". The law writes top8 (blank u tl) funs: top8's text is topOf's
to the letter, and topOf (blank u t) funs = topOf t funs by rfl (topOf_blank): HELD BY READING, NOT
BY LEAN: the law can import no root outside the library. The lemma: TailClaims/EquationsBlank.lean.
rows: the batching round's entry's rows at the segment: ProofFile.k9Where (ProofFile.k9Stretches Z) l gives it
(Johnson/Desc/ProofFile/Lot/K9.lean).
FORETOLD, of an honest walk: in front of the batching: owedIs no (nothing is owed) · laidIs no
(nothing is laid; but yes where the list of tables is not there yet) · rowsFit yes wherever the
plan's number is laid; behind the batching and behind the next block: all three yes; behind the one
equation: owedIs no (the count is paid).
DEFINITIONS WITH CODE. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.AtS
import OnBytes.Tie.Pv.Tail.EndSpread

set_option autoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (topOf)
open VerifiableInference.Desc.First (S)

/-- The rows owed are the batching round's. -/
def owedIs (rows : Nat) (s : S) : Bool :=
  (atS.get? s).all fun x => x.owed == some rows

/-- What is said to be laid is what the record and the tables foretell. -/
def laidIs (s : S) : Bool :=
  match atS.get? s, s.tl?, s.funs? with
  | some x, some tl, some funs => x.laid == some (topOf tl funs)
  | _, _, _ => true

/-- Whatever number is said to be laid is what the record and the tables foretell. -/
def laidOk (s : S) : Bool :=
  match s.tl?, s.funs? with
  | some tl, some funs => (laidOf tl).all (· == topOf tl funs)
  | _, _ => true

/-- The plan's claims and the ties' and reads' indices are at most the round's rows. -/
def rowsFit (rows : Nat) (s : S) : Bool :=
  match s.tl?, s.funs?, s.fork? with
  | some tl, some funs, some F => decide (F.planClaimsF + topOf tl funs ≤ rows)
  | _, _, _ => true

/-- The segment's own check lays its rows on group g. -/
def groupIs (g : Nat) (s : S) : Bool :=
  (atS.get? s).all fun x => x.L.check.group == g

/-- The three under names; then what they read. -/
def owedLaidWhy (rows : Nat) (s : S) : List (String × String) :=
  [("K9.owedIs", toString (owedIs rows s)), ("K9.laidIs", toString (laidIs s)),
   ("K9.laidOk", toString (laidOk s)), ("K9.rowsFit", toString (rowsFit rows s)),
   ("a part is there", toString (atS.get? s).isSome),
   ("the tables are there", toString s.funs?.isSome),
   ("owed", toString ((atS.get? s).map (·.owed))),
   ("laid", toString ((atS.get? s).map (·.laid))),
   ("the plan's claims", toString (s.fork?.map (·.planClaimsF))),
   ("topOf", toString (s.tl?.bind fun tl => s.funs?.map fun funs => topOf tl funs)),
   ("rows", toString rows),
   ("the check's group", toString ((atS.get? s).map (·.L.check.group)))]

end VerifiableInference.Desc.K9
