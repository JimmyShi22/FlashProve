-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/Order.lean: THE SMALLNESS TEST: WHAT MUST HOLD IN FRONT OF THE DRAW OF THE
MATRIX, IN THIS LIBRARY's OWN WORDS: the closing of the list of tables, two tests on public numbers,
and the guard of order. For the step without a round that stands behind the sending of the reads.
DEFINITIONS, WITH CODE. NO THEOREM HERE. NO SOUNDNESS IS CLAIMED.

WHY THIS FILE. Johnson/Top/H0/L3/Frame.lean's closeStep, drawFront and orderGuard call two of the
verifier on bytes' own TESTS by name (HTailF2.closeFuns, which refuses a closed list, and
HTailF2.arrayFixed, which calls ReqFrame.whereIs). Here each is written out. What is still read of
that verifier is the fields of its plain records. That each text agrees with the older one at every
argument is proved beside, in Johnson/Desc/First/K8/OrderAgrees.lean, which no running text imports.

THE GUARD OF ORDER. When the matrix is drawn the prover must have no choice left in anything that
the matrix is applied to. So of every array that it multiplies (each matrix's array of symbols,
whichever link committed to it, and the vectors of reads):
  (1) the link's table of arrays names it: the link at which it was born, and its name;
  (2) the layout of that link lays an array of that name, in a message of that link;
  (3) that message is sent in front of this place: born at this link: at an earlier moment than the
      present one; born at an earlier link: its life reaches this link, so that it was sent anew at
      this link's start; born at a later link: never;
  (4) the statement has that message, as it is named in the present link, and its sample is
      answered.
And of the link: its number is the walk's; it is one of the walk's links; one array a matrix.

-/
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Order
open OnBytes OnBytes.Model

/-- Where an array lies: the link at which it was born, its message's number there, and that
message's moment and life. -/
structure Lies where
  born : Nat
  message : Nat
  moment : Nat
  life : Nat

/-- (1) (2): a reading of the link's table of arrays, the layout and the shape. -/
def liesAt (L : LinkCtx) (array : Nat) : Option Lies := do
  let named ← L.arrayOf[array]?
  let laid ← (L.check.rows.layout.link.getD named.1 []).find? fun A => A.name == named.2
  let m ← (← L.check.frame.shape.link[named.1]?).messages[laid.message]?
  pure ⟨named.1, laid.message, m.moment, m.life⟩

/-- (3). -/
def sentInFront (L : LinkCtx) (w : Lies) : Bool :=
  if w.born == L.link then decide (w.moment < L.moments)
  else decide (w.born < L.link) && decide (L.link ≤ w.born + w.life)

/-- Under which number the statement has the message now. A link must be under way. A message born
at the link under way: that link's own list has it, at the message's number. A message born earlier:
the group of the link under way lists what it keeps, by (link, number); what took the rows of the
i-th of these at the last switch is the i-th of the messages kept. Nothing else is had. -/
def namedNow (f : ReqFrame) (w : Lies) : Option Nat :=
  match f.next with
  | .laterOrClose =>
    if w.born == f.link then f.own[w.message]?
    else
      match (f.groups.getD f.link {}).born.idxOf? (w.born, w.message) with
      | none => none
      | some i => f.keptBefore[i]?
  | _ => none

/-- (4). -/
def answered (L : LinkCtx) (S : Statement) (w : Lies) : Bool :=
  match namedNow L.check.frame w with
  | none => false
  | some o =>
    match S.oracles[o]? with
    | none => false
    | some x => x.sampled

/-- (1) to (4), of one array. -/
def fixed (L : LinkCtx) (S : Statement) (array : Nat) : Bool :=
  match liesAt L array with
  | none => false
  | some w => sentInFront L w && answered L S w

/-- **The guard of order.** -/
def orderOk (tl : HTailF2) (L : LinkCtx) (S : Statement) : Bool :=
  L.check.link == L.link && decide (L.link < L.check.links) && tl.gtTree.size == tl.NM &&
    tl.gtTree.all (fixed L S) &&
    (List.range 4).all fun n =>
      match tl.ix.U.getD n none with
      | none => true
      | some u => fixed L S u

/-- **The list of tables is closed**: it must still be open. -/
def close (tl : HTailF2) (funs : Array HFun) : Except String HTailF2 :=
  if tl.funClosed then .error "the smallness test: the list of tables was closed already"
  else .ok { tl with funClosed := true, funs := funs }

/-- **In front of the draw**: the list is closed; one shape a matrix; the guard of order. -/
def front (tl : HTailF2) (L : LinkCtx) (S : Statement) : Except String Unit :=
  if !tl.funClosed then .error "the smallness test: the list of tables is open"
  else if tl.shp.size != tl.NM then .error "the smallness test: not one shape a matrix"
  else if !orderOk tl L S then
    .error "the smallness test: an array that the matrix multiplies is not fixed in front of \
      the draw"
  else .ok ()

end VerifiableInference.Desc.First.K8.Order
