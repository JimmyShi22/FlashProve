-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HeadPart.lean: THE SHAPE OF WHAT THE OUTPUT HEAD's LINK HOLDS BESIDE ITS
CONTEXT, ITS LEDGER AND THE SMALLNESS TEST's RECORD: what is left of these fields of First.HeadOwn
(Johnson/Desc/First/State.lean): no field element, and not all else: a field is meant to be seen
here only if a guard on the structure reads it. Definitions, and two small equations on readers
(headSh_xEnd, headSh_t).

What it is for. Johnson/Desc/First/Shape/Chain.lean lays the shapes of the state's records together.
The head's merge, the code switch in the head's front and the quiet step behind the head's digits
read and write these fields.

THE FIELDS' TYPES.
  `WsClaimSh`  of WsClaim (OnBytes/Model/Weights.lean): ui : Nat; of each factor the sizes of its
               three arrays HV, pt, AV: f : List (Nat × Nat × Nat).
  `HeadSh`     of HeadOwn: fr : FrameSh (Calls.lean), kept ids : Array Nat, slot : Option Nat, each
               under its own name; claim : Option WsClaimSh; wo : Option MergeSh (Own.lean);
               Fm : LedSh (Parts.lean): the ledger as it stood in front of the merge;
               squaresP : Option PscSh (Parts.lean); x : Option HeadHeardSh (HeadHeard.lean): the
               shape of what the head's own rounds heard; of t : Option Head.Tables its field tab,
               whole: for each table its name, its first entry and its length.
               shut : Option ShutSh: WHILE THE LINK IS ENTERED AND NOT YET OPENED: tl, F, L, the
               lookup's record in x, lookHeard and the tables' records: the library's readers S.tl?,
               S.fork?, S.link?, S.look?, S.lookHeard? and S.funs? answer nothing there, though the
               step that opens the link lays these very fields bare.
NOT SEEN HERE, since the chain's shape sees them by components of their own: opened, lookHeard, of
x its field g1 (look), and, once the link is opened, L, F and tl.
The makers lay no default: an Option stays an Option.
  `wsClaimSh`, `headSh`, `headOf`: the last reads the record off a place of the chain, whether or
  not the link is opened. `HeadSh.xEnd`, `HeadSh.t`: two readers (the slot at which the stream's
  token sumcheck ends; that the tables are laid).

Limits. Of t the tables' records (funs) and the vector's length are not seen here (once the link is
opened the chain's shape sees the records' shapes by its component tables). A number can still be
made of a value: which numbers of these records are public given the three public files, or counts,
is not shown in this file. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Calls
import Johnson.Desc.First.Shape.Own
import Johnson.Desc.First.Shape.HeadHeard
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First

/-- A claim on the weights: which unit it names; its factors' sizes. -/
structure WsClaimSh where
  ui : Nat
  f : List (Nat × Nat × Nat)

def wsClaimSh (c : WsClaim) : WsClaimSh :=
  { ui := c.ui, f := c.f.map fun x => (x.HV.size, x.pt.size, x.AV.size) }

/-- What lies in the head's link while it is entered and not yet opened, and is laid bare by the
step that opens it: the library's readers answer nothing of these six until then. -/
structure ShutSh where
  tl : TailSh
  led : LedSh
  link : LinkSh
  look : Option HeardAll
  lookHeard : Option HeardAll
  tables : Option (List FunSh)

/-- The head's link's own fields. -/
structure HeadSh where
  fr : FrameSh
  kept : Array Nat
  ids : Array Nat
  /-- the shape of what the head's own rounds heard -/
  x : Option HeadHeardSh
  /-- where the head's tables are laid: for each table its name, its first entry and its length -/
  tab : Option (List (String × Nat × Nat))
  claim : Option WsClaimSh
  wo : Option MergeSh
  Fm : LedSh
  slot : Option Nat
  squaresP : Option PscSh
  /-- while the link is entered and not yet opened: what lies there; once it is opened the chain's
  shape sees these six by components of their own -/
  shut : Option ShutSh

def headSh (a : HeadOwn) : HeadSh :=
  { fr := frameSh a.fr, kept := a.kept, ids := a.ids, x := a.x.map headHeardSh
    tab := a.t.map (·.tab)
    claim := a.claim.map wsClaimSh, wo := a.wo.map mergeSh, Fm := ledSh a.Fm, slot := a.slot
    squaresP := a.squaresP.map pscSh
    shut := if a.opened then none else
      some ⟨tailSh a.tl, ledSh a.F, linkSh a.L, a.x.map fun x => heardAll x.g1,
        a.lookHeard.map heardAll, a.t.map fun t => t.funs.toList.map funSh⟩ }

/-- Where the head's own rounds are heard: the slot at which the stream's token sumcheck ends. -/
def HeadSh.xEnd (h : HeadSh) : Option Nat := h.x.map (·.tH.sEnd)

/-- The head's tables are laid. -/
def HeadSh.t (h : HeadSh) : Bool := h.tab.isSome

theorem headSh_xEnd (a : HeadOwn) : (headSh a).xEnd = a.x.map (·.tH.sEnd) := by
  unfold HeadSh.xEnd headSh
  cases a.x <;> rfl

theorem headSh_t (a : HeadOwn) : (headSh a).t = a.t.isSome := by
  unfold HeadSh.t headSh
  cases a.t <;> rfl

/-- The head's link's own fields, where the chain stands in that link. -/
def headOf : Here → Option HeadSh
  | .head a => some (headSh a)
  | _ => none

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.headSh_xEnd
#print axioms VerifiableInference.Desc.First.Shape.headSh_t
