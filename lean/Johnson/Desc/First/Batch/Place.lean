-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Place.lean: kinds K9 and K10 at the state that the proof file's first chain
carries
(Johnson/Desc/First/State.lean: S): what closes a segment, as blocks. Definitions with code; no
theorem.

  recOf, putRec   the lens for K10's part of the state: the rows owed; the frame inside the LIVE
                  state of the calls; the statement.
  closing P       K10's block (Johnson/Desc/First/Close/Kind.lean) at S.
  shut p          a block without a round: behind the closing the segment's book-keeping is marked:
                  no segment is under way; the door has been walked; the segment is done
                  (K9.closed, Johnson/Desc/First/Batch/Text.lean). It refuses where no segment is
                  open.
  closeOf p P     THE THREE IN A ROW, as the list that a segment's record takes as `close`:
                  the one equation; the closing; shut.
  joint p P       the same three as ONE block, under K10's place: for a table of places that has one
                  place where these three stand.
  fits p P        the test on the plan that ties the two kinds' numbers: one chain, one segment,
                  the equation's block just in front of the closing's.
All are general in the type of claims: none has a claim.


-/
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Close.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par Rec)

variable {Cl : Type}

/-- K10's part of the state. The rows owed by owedOf: "some 0" is handed on as "none". -/
def recOf (s : S) : Rec := ⟨owedOf s, s.live.frame, s.st⟩

/-- It is written back: the frame into the live state of the calls, and that one alone. -/
def putRec (s : S) (r : Rec) : S :=
  { s.putLive { s.live with frame := r.frame } with st := r.st, rowsOwed := r.owed }

/-- K10's block at S. -/
def closing (P : Par) : Block S Cl := (First.Close.kind P).lift recOf putRec

/-- Behind the closing: the segment's book-keeping is marked. piece: the block's number. IT ASKS
NOTHING: it is not to stand alone: in joint and closeOf it stands behind the closing by
construction. -/
def shut (p : Where) (piece : Nat) : Block S Cl :=
  { name := "K9: the segment is shut"
    place := ⟨p.chain, some p.link, piece, .K9⟩
    planOk := true
    rounds := []
    oracles := []
    before := []
    claims := []
    after := []
    decide := fun s _ _ => do
      let L ← there "K9.in-a-segment" s.link?
      pure (s.putLink (closed L L.check.frame)) }

/-- The two kinds' numbers speak of one place: K10's kind stands on chain 1. -/
def fits (p : Where) (P : Par) : Bool :=
  p.chain == 1 && p.link == P.link && p.pieceEq + 1 == P.piece

/-- What closes a segment, block by block. The first holds the test that ties the numbers. -/
def closeOf (p : Where) (P : Par) : List (Block S Cl) :=
  [{ oneEquation atS p with planOk := fits p P }, closing P, shut p (P.piece + 1)]

/-- The same as one block, under K10's place. -/
def joint (p : Where) (P : Par) : Block S Cl :=
  let b : Block S Cl :=
    ((oneEquation atS p).andThen "the one equation and the closing" (closing P)).andThen
      s!"the one equation and the closing of segment {p.link}" (shut p (P.piece + 1))
  { b with place := (closing (Cl := Cl) P).place, planOk := b.planOk && fits p P }

end VerifiableInference.Desc.K9
