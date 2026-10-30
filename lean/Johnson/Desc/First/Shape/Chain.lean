-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Chain.lean: THE SHAPE OF THE STATE THAT THE FIRST CHAIN CARRIES: what is
kept of it: no field element, and not all else: a component is meant to be here only if a guard on
the structure reads it or an update needs it. A definition with named readers and setters; the laws
of the state's own setters seen through it; and the shapes that single sub-protocols have of their
own, as readers of it. Nothing is evaluated.

What it is for. A verifier's step says yes where its guards on the structure pass and its tests on
values pass. The shape is for the first half: member by member, one Bool and one update on a
shape without a field element. This file lays the shapes of the state's records together for the
whole state (First.S, Johnson/Desc/First/State.lean).

ONE PRODUCT, A COMPONENT A RECORD OF THE STATE, EACH FIELD SEEN ONCE. A step must update every
component that sees a field which it writes: so no field is seen by two components. A sub-protocol's
own shape is a reader of this one (section 3).
  `marked`     a named test on values has failed (S.failed is there); the name is left out
  `here`       where the chain stands, as a number (hereNo): between links 0, a layers' link 1, an
               attention link 2, the output head's link 3 once it is opened and 4 before, the
               finish 5, the memory 6
  `tl`         the shape of the smallness test's record, whole (TailSh, Tail.lean), where a link is
               open (S.tl?); `tlNarrow`: Parts.lean's small shape, read off it
  `led`        the shape of the ledger (LedSh, Parts.lean), where a link is open (S.fork?)
  `tables`     the shapes of the sub-proof's list of tables (FunSh, Tail.lean), where it is laid
               (S.funs?); `funs`: that it is laid, read off it
  `rowsOwed`   the number of batched rows that the round closed last counts, while it is not yet
               compared (S.rowsOwed)
  `core`       the one shape of statement, book of trees and number of roots, which all chains share
               (Ground.Sh.CoreSh, Johnson/Desc/Ground/Shape/Core.lean), with the ground's routines
               on it (Ground.lean beside it). Read off it: `st` (the statement's shape as the
               sub-protocol on the table's rows has it, K13.Honest.StSh,
               Johnson/Desc/K13/Honest/ShapeDefs.lean),
               `ledgers` (each oracle message's ledger), `roots`
  `reply`, `indexMasks`, `pile`   of S.out: a reply was heard; the number of the index masks'
               message; the shapes of the rows on the pile (K13.Honest.RowSh, the same file)
  `atEnd`      at the memory alone: the messages that the record announces, the numbers handed on,
               and what is laid for the last chain (K13.Honest.LaidSh)
  `check`      the shape of the walk's state of the calls over the links (CheckSh, Calls.lean)
  `link`       the shape of the open link's context, with its own copy of that state (LinkSh,
               Calls.lean), where a link is open (S.link?)
               `live`: the live copy of that state (S.live), read off link and check
  `look`       the shape of what the lookup on the calls returned, where the link's steps read it
               (HeardAll, Tail.lean; S.look?)
  `lookHeard`  the same as the hearing itself laid it, which no later step writes (S.lookHeard?)
  `own`        the shape of what a layers' link's own rounds leave (OwnSh, Own.lean; S.own?)
  `head`       the shape of the output head's link's own fields (HeadSh, HeadPart.lean), opened or
               not; while it is entered and not yet opened: its tl, ledger and context too
  `att`        the shape of an attention link's own parts (AttOwnSh, AttOwn.lean): what its own
               rounds heard; that the planes and the scores are laid
  `fin`        the shape of the finish's own fields (FinSh, FinPart.lean)
EACH COMPONENT IS REACHED BY A NAMED READER, made by mk and turned by a named setter: a law names no
position in the product, so a component can be added behind the others without turning a law's
statement. Each further component asks a law of every step that writes it.

THE TYPES. marked, here, led, rowsOwed, reply and indexMasks are plain products of numbers, Bools,
strings, lists and options. The other thirteen hold Lean structures: CoreSh with StSh, OrcSh, GrpSh,
BookSh, TreeSh and SrcSh (Ground/Shape/Core.lean); CheckSh and LinkSh (their fields' types are
listed in Calls.lean's head, with SingleSh in Single.lean's); TailSh, HeardAll and FunSh
(Tail.lean's head); OwnSh (Own.lean's head); HeadSh (HeadPart.lean's head); AttOwnSh (AttOwn.lean's
head); FinSh (FinPart.lean's head); RowSh, LaidSh and ClaimSh (K13/Honest/ShapeDefs.lean);
OnBytes.Ledger, OracleShape,
Codes, Part, Slot, RowKind (Iop/Ground.lean and what it imports). That these hold no field element
is a reading of their fields' types, not a theorem.

  1  `hereNo`, `viewSt`, `viewSt_stSh`, `ChainSh` with its readers and setters, `endSh`, `chainSh`;
     `chainSh_st`, `chainSh_ledgers`, `chainSh_roots`: these three readers at a state.
  2  `chainSh_putTl`, `chainSh_putFork`, `chainSh_putLink`: S.putTl, S.putFork and S.putLink turn
     one component each, and only where it is there. `chainSh_ground`, `chainSh_check`: a new
     statement, book and number of roots; a new state of the walk's calls. `chainSh_k8set`: laying
     back the smallness test's part (k8PartP.set, Johnson/Desc/First/TailClaims/K8Claims.lean)
     turns tl and led. `part_sh`: where that part is read, its shapes are the state's components.
     `part_of_sh`: where the three components are there, the part is read. `chainSh_withReq`: the
     shape does not see the request's words. `chainSh_rowsOwed`, `chainSh_mark`, `chainSh_live`.
  3  `viewM3`, `shOf_view`; `viewM4`, `sh4_view`: the two shapes of the sub-protocol on the table's
     rows (K13.Honest.shOf, K13.Honest.sh4) are readers of the chain's shape.

Limits. core holds of a group's open rows their kinds and of a message's sample rows their number:
no summand of a row: a guard that reads a row's terms cannot be written on it. pile holds of each
row on the pile two marks on its weight vectors (K13.Honest.RowSh: it has none; each has so many
variables), not how many they are. Elsewhere in the library which terms a row has can hang on
values (Tensor.lean's tensorBelow drops terms), and so could these marks; that no step of the first
chain makes a row's terms so is a reading, not a theorem. A number can still be made of a value:
which numbers of these records are public given the three public files, or counts, is not shown in
this file. The request, and of an attention link's own parts d, x and t, have no component: a guard
that reads one of them cannot be written on this shape. Nothing on soundness, completeness or
hiding.

-/
import Johnson.Desc.First.Shape.Tail
import Johnson.Desc.First.Shape.Calls
import Johnson.Desc.Ground.Shape.Core
import Johnson.Desc.First.Shape.HeadPart
import Johnson.Desc.First.Shape.AttOwn
import Johnson.Desc.First.Shape.FinPart
import Johnson.Desc.First.TailClaims.K8Claims
import Johnson.Desc.K13.Honest.Shape
import Johnson.Desc.K13.Honest.ShapeM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (K8Part k8PartP)

/-! ## 1 The shape -/

/-- Where the chain stands, as a number. -/
def hereNo : Here → Nat
  | .between => 0
  | .lay _ => 1
  | .att _ => 2
  | .head a => if a.opened then 3 else 4
  | .fin _ => 5
  | .mem _ => 6

/-- At the memory: what the record announces; the numbers handed on; what is laid for the last
chain. -/
abbrev EndSh : Type := Array OracleNotice × Array Nat × Option K13.Honest.LaidSh

/-- The statement's shape K13.Honest.StSh, read off the one shape of a statement: of a message its
shape, its mark, its groups and its pad's places; of a group all but its rows' kinds, of which the
number stays. -/
def viewSt (h : Ground.Sh.StSh) : K13.Honest.StSh :=
  ⟨h.codes, (h.oracles.map fun x => ⟨x.shape, x.sampled, x.groups, x.pad⟩).toArray,
    (h.groups.map fun G =>
      ⟨G.code, G.maskCode, G.members.toArray, G.kept.toArray, G.kinds.length, G.inRun⟩).toArray⟩

theorem viewSt_stSh (St : Statement) : viewSt (Ground.Sh.stSh St) = K13.Honest.stSh St := by
  simp only [viewSt, Ground.Sh.stSh, K13.Honest.stSh, List.map_map]
  congr 1
  · rw [← Array.toList_map, Array.toArray_toList]
    rfl
  · rw [← Array.toList_map, Array.toArray_toList]
    apply congrArg (fun f => Array.map f St.groups)
    funext G
    simp [Ground.Sh.grpSh, K13.Honest.grpSh]

/-- The shape of the first chain's state. -/
abbrev ChainSh : Type :=
  Bool × Nat × Option TailSh × Option LedSh × Option (List FunSh) × Option Nat × Ground.Sh.CoreSh ×
    Bool × Nat × List K13.Honest.RowSh × Option EndSh × CheckSh × Option LinkSh × Option HeardAll ×
    Option HeardAll × Option OwnSh × Option HeadSh × Option AttOwnSh × Option FinSh

namespace ChainSh
def mk (marked : Bool) (here : Nat) (tl : Option TailSh) (led : Option LedSh)
    (tables : Option (List FunSh)) (rowsOwed : Option Nat) (core : Ground.Sh.CoreSh) (reply : Bool)
    (indexMasks : Nat) (pile : List K13.Honest.RowSh) (atEnd : Option EndSh) (check : CheckSh)
    (link : Option LinkSh) (look : Option HeardAll) (lookHeard : Option HeardAll)
    (own : Option OwnSh) (head : Option HeadSh) (att : Option AttOwnSh) (fin : Option FinSh) :
    ChainSh :=
  (marked, here, tl, led, tables, rowsOwed, core, reply, indexMasks, pile, atEnd, check, link,
    look, lookHeard, own, head, att, fin)
def marked (a : ChainSh) : Bool := a.1
def here (a : ChainSh) : Nat := a.2.1
def tl (a : ChainSh) : Option TailSh := a.2.2.1
/-- The small shape of the smallness test's record (Parts.lean), read off the whole one. -/
def tlNarrow (a : ChainSh) : Option TlSh := a.tl.map TailSh.narrow
def led (a : ChainSh) : Option LedSh := a.2.2.2.1
def tables (a : ChainSh) : Option (List FunSh) := a.2.2.2.2.1
/-- The list of tables is laid. -/
def funs (a : ChainSh) : Bool := a.tables.isSome
def rowsOwed (a : ChainSh) : Option Nat := a.2.2.2.2.2.1
def core (a : ChainSh) : Ground.Sh.CoreSh := a.2.2.2.2.2.2.1
/-- The statement's shape K13.Honest.StSh, read off the core. -/
def st (a : ChainSh) : K13.Honest.StSh := viewSt a.core.st
/-- Each oracle message's ledger, read off the core. -/
def ledgers (a : ChainSh) : Array (Option OnBytes.Ledger) :=
  (a.core.st.oracles.map (·.ledger)).toArray
/-- The number of roots received so far, read off the core. -/
def roots (a : ChainSh) : Nat := a.core.roots
def reply (a : ChainSh) : Bool := a.2.2.2.2.2.2.2.1
def indexMasks (a : ChainSh) : Nat := a.2.2.2.2.2.2.2.2.1
def pile (a : ChainSh) : List K13.Honest.RowSh := a.2.2.2.2.2.2.2.2.2.1
def atEnd (a : ChainSh) : Option EndSh := a.2.2.2.2.2.2.2.2.2.2.1
def check (a : ChainSh) : CheckSh := a.2.2.2.2.2.2.2.2.2.2.2.1
def link (a : ChainSh) : Option LinkSh := a.2.2.2.2.2.2.2.2.2.2.2.2.1
/-- The live copy of the state of the calls: the open link's own, else the walk's (S.live). -/
def live (a : ChainSh) : CheckSh :=
  match a.link with
  | some L => L.check
  | none => a.check
def look (a : ChainSh) : Option HeardAll := a.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def lookHeard (a : ChainSh) : Option HeardAll := a.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def own (a : ChainSh) : Option OwnSh := a.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def head (a : ChainSh) : Option HeadSh := a.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def att (a : ChainSh) : Option AttOwnSh := a.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def fin (a : ChainSh) : Option FinSh := a.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
/-- Lays a shape of the smallness test's record where one is there. -/
def setTl (a : ChainSh) (t : TailSh) : ChainSh :=
  mk a.marked a.here (a.tl.map fun _ => t) a.led a.tables a.rowsOwed a.core a.reply a.indexMasks
    a.pile a.atEnd a.check a.link a.look a.lookHeard a.own a.head a.att a.fin
/-- Lays a shape of the ledger where one is there. -/
def setLed (a : ChainSh) (L : LedSh) : ChainSh :=
  mk a.marked a.here a.tl (a.led.map fun _ => L) a.tables a.rowsOwed a.core a.reply a.indexMasks
    a.pile a.atEnd a.check a.link a.look a.lookHeard a.own a.head a.att a.fin
/-- Lays a shape of the link's context where one is there. -/
def setLink (a : ChainSh) (L : LinkSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check (a.link.map fun _ => L) a.look a.lookHeard a.own a.head a.att a.fin
/-- Lays what stands at the memory where something is there. -/
def setEnd (a : ChainSh) (e : EndSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile
    (a.atEnd.map fun _ => e) a.check a.link a.look a.lookHeard a.own a.head a.att a.fin
/-- Lays a shape of the head's link's own fields where one is there. -/
def setHead (a : ChainSh) (h : HeadSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link a.look a.lookHeard a.own (a.head.map fun _ => h) a.att a.fin
/-- Lays a shape of an attention link's own parts where one is there. -/
def setAtt (a : ChainSh) (x : AttOwnSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link a.look a.lookHeard a.own a.head (a.att.map fun _ => x)
    a.fin
def setMarked (a : ChainSh) : ChainSh :=
  mk true a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def setHere (a : ChainSh) (n : Nat) : ChainSh :=
  mk a.marked n a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def setRowsOwed (a : ChainSh) (r : Option Nat) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables r a.core a.reply a.indexMasks a.pile a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def setCore (a : ChainSh) (c : Ground.Sh.CoreSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed c a.reply a.indexMasks a.pile a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def setReply (a : ChainSh) (r : Bool) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core r a.indexMasks a.pile a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def setIndexMasks (a : ChainSh) (n : Nat) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply n a.pile a.atEnd a.check a.link
    a.look a.lookHeard a.own a.head a.att a.fin
def setPile (a : ChainSh) (p : List K13.Honest.RowSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks p a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def setCheck (a : ChainSh) (c : CheckSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd c
    a.link a.look a.lookHeard a.own a.head a.att a.fin
/-- Lays the component anew, whether or not one was there: for a step that enters or leaves a link,
or hears a lookup. So the ten that follow. -/
def layTl (a : ChainSh) (t : Option TailSh) : ChainSh :=
  mk a.marked a.here t a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def layLed (a : ChainSh) (L : Option LedSh) : ChainSh :=
  mk a.marked a.here a.tl L a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def layTables (a : ChainSh) (t : Option (List FunSh)) : ChainSh :=
  mk a.marked a.here a.tl a.led t a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def layLink (a : ChainSh) (L : Option LinkSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check L a.look a.lookHeard a.own a.head a.att a.fin
def layEnd (a : ChainSh) (e : Option EndSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile e a.check
    a.link a.look a.lookHeard a.own a.head a.att a.fin
def layLook (a : ChainSh) (g : Option HeardAll) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link g a.lookHeard a.own a.head a.att a.fin
def layLookHeard (a : ChainSh) (g : Option HeardAll) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link a.look g a.own a.head a.att a.fin
def layOwn (a : ChainSh) (o : Option OwnSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link a.look a.lookHeard o a.head a.att a.fin
def layHead (a : ChainSh) (h : Option HeadSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link a.look a.lookHeard a.own h a.att a.fin
def layAtt (a : ChainSh) (x : Option AttOwnSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link a.look a.lookHeard a.own a.head x a.fin
/-- Lays a shape of the finish's own fields where one is there. -/
def setFin (a : ChainSh) (x : FinSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link a.look a.lookHeard a.own a.head a.att (a.fin.map fun _ => x)
def layFin (a : ChainSh) (x : Option FinSh) : ChainSh :=
  mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile a.atEnd
    a.check a.link a.look a.lookHeard a.own a.head a.att x
end ChainSh

/-- What stands at the memory. -/
def endSh : Here → Option EndSh
  | .mem o => some (o.msg, o.ids, o.lin.map K13.Honest.laidSh)
  | _ => none

/-- **The state's shape.** -/
def chainSh (s : S) : ChainSh :=
  ChainSh.mk s.failed.isSome (hereNo s.here) (s.tl?.map tailSh) (s.fork?.map ledSh)
    (s.funs?.map fun a => a.toList.map funSh) s.rowsOwed
    (Ground.Sh.coreSh ⟨s.st, s.book, s.roots⟩) s.out.reply.isSome s.out.indexMasks
    (s.out.pending.map K13.Honest.rowSh) (endSh s.here) (checkSh s.check) (s.link?.map linkSh)
    (s.look?.map heardAll) (s.lookHeard?.map heardAll) (s.own?.map ownSh) (headOf s.here)
    (attOf s.here) (finOf s.here)

/-- The three readers of the statement, at a state. -/
theorem chainSh_st (s : S) : (chainSh s).st = K13.Honest.stSh s.st := viewSt_stSh s.st

theorem chainSh_ledgers (s : S) : (chainSh s).ledgers = s.st.oracles.map (·.ledger) := by
  show ((s.st.oracles.toList.map Ground.Sh.orcSh).map (·.ledger)).toArray = _
  rw [List.map_map, ← Array.toList_map, Array.toArray_toList]
  rfl

theorem chainSh_roots (s : S) : (chainSh s).roots = s.roots := rfl

/-! ## 2 The state's own setters, seen through it -/

theorem chainSh_putTl (s : S) (tl : HTailF2) :
    chainSh (s.putTl tl) = (chainSh s).setTl (tailSh tl) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [chainSh, ChainSh.mk, ChainSh.marked, ChainSh.here, ChainSh.tl, ChainSh.led,
      ChainSh.tables, ChainSh.rowsOwed, ChainSh.core, ChainSh.reply, ChainSh.indexMasks,
      ChainSh.pile, ChainSh.atEnd, ChainSh.check, ChainSh.link, ChainSh.look, ChainSh.lookHeard,
      ChainSh.own, ChainSh.head, ChainSh.att, ChainSh.fin, endSh, hereNo, headOf, headSh, attOf,
      finOf, attOwnSh,
      S.tl?, S.fork?, S.funs?, S.link?, S.look?, S.lookHeard?, S.own?, ChainSh.setTl, S.putTl]

theorem chainSh_putFork (s : S) (F : Fork) :
    chainSh (s.putFork F) = (chainSh s).setLed (ledSh F) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [chainSh, ChainSh.mk, ChainSh.marked, ChainSh.here, ChainSh.tl, ChainSh.led,
      ChainSh.tables, ChainSh.rowsOwed, ChainSh.core, ChainSh.reply, ChainSh.indexMasks,
      ChainSh.pile, ChainSh.atEnd, ChainSh.check, ChainSh.link, ChainSh.look, ChainSh.lookHeard,
      ChainSh.own, ChainSh.head, ChainSh.att, ChainSh.fin, endSh, hereNo, headOf, headSh, attOf,
      finOf, attOwnSh,
      S.tl?, S.fork?, S.funs?, S.link?, S.look?, S.lookHeard?, S.own?, ChainSh.setLed, S.putFork]

theorem chainSh_putLink (s : S) (L : LinkCtx) :
    chainSh (s.putLink L) = (chainSh s).setLink (linkSh L) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [chainSh, ChainSh.mk, ChainSh.marked, ChainSh.here, ChainSh.tl, ChainSh.led,
      ChainSh.tables, ChainSh.rowsOwed, ChainSh.core, ChainSh.reply, ChainSh.indexMasks,
      ChainSh.pile, ChainSh.atEnd, ChainSh.check, ChainSh.link, ChainSh.look, ChainSh.lookHeard,
      ChainSh.own, ChainSh.head, ChainSh.att, ChainSh.fin, endSh, hereNo, headOf, headSh, attOf,
      finOf, attOwnSh,
      S.tl?, S.fork?, S.funs?, S.link?, S.look?, S.lookHeard?, S.own?, ChainSh.setLink, S.putLink]

/-- A new statement, book and number of roots turn one component. -/
theorem chainSh_ground (s : S) (st : Statement) (book : TreeBook) (roots : Nat) :
    chainSh { s with st := st, book := book, roots := roots } =
      (chainSh s).setCore (Ground.Sh.coreSh ⟨st, book, roots⟩) := rfl

/-- A new state of the walk's calls turns one component. -/
theorem chainSh_check (s : S) (c : ChainCheck) :
    chainSh { s with check := c } = (chainSh s).setCheck (checkSh c) := rfl

/-- The live copy, read off the shape. -/
theorem chainSh_live (s : S) : (chainSh s).live = checkSh s.live := by
  unfold ChainSh.live S.live
  show (match s.link?.map linkSh with
    | some L => L.check
    | none => checkSh s.check) = _
  cases s.link? <;> rfl

/-- **Laying back the smallness test's part turns two components.** -/
theorem chainSh_k8set (s : S) (q : K8Part) :
    chainSh (k8PartP.set s q) = ((chainSh s).setTl (tailSh q.tl)).setLed (ledSh q.F) := by
  have e : k8PartP.set s q = (s.putTl q.tl).putFork q.F := rfl
  rw [e, chainSh_putFork, chainSh_putTl]

/-- **Where the part is read, its shapes are the state's components.** -/
theorem part_sh {s : S} {q : K8Part} (h : k8PartP.get? s = some q) :
    (chainSh s).tl = some (tailSh q.tl) ∧ (chainSh s).led = some (ledSh q.F) ∧
      (chainSh s).tables = some (q.funs.toList.map funSh) ∧ (chainSh s).funs = true := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [chainSh, ChainSh.mk, ChainSh.tl, ChainSh.led, ChainSh.tables, ChainSh.funs, k8PartP,
      tlForkP, Part.pair, tlP, forkP, S.tl?, S.fork?, S.funs?] <;>
    (obtain ⟨f, hf, rfl⟩ := h; simp_all)

/-- Where the three components are there, the part is read. -/
theorem part_of_sh {s : S}
    (h : ((chainSh s).tl.isSome && (chainSh s).led.isSome && (chainSh s).funs) = true) :
    ∃ q, k8PartP.get? s = some q := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp_all [chainSh, ChainSh.mk, ChainSh.tl, ChainSh.led, ChainSh.tables, ChainSh.funs, k8PartP,
      tlForkP, Part.pair, tlP, forkP, S.tl?, S.fork?, S.funs?, Option.isSome_iff_exists]

/-- The shape does not see the request's words. -/
theorem chainSh_withReq (s : S) (req : Array UInt32) : chainSh (s.withReq req) = chainSh s := rfl

theorem chainSh_rowsOwed (s : S) (r : Option Nat) :
    chainSh { s with rowsOwed := r } = (chainSh s).setRowsOwed r := rfl

theorem chainSh_mark (s : S) (name : String) : chainSh (s.mark name) = (chainSh s).setMarked := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases failed <;> rfl

/-! ## 3 Single sub-protocols' own shapes, as readers -/

/-- The shape at the batching of the table's rows, read off the chain's. -/
def viewM3 (a : ChainSh) : K13.Honest.Sh :=
  ⟨a.here == 5, a.reply, (match a.rowsOwed with | none => true | some r => r == 0), a.indexMasks,
    a.pile, a.st.codes, Array.zipWith (fun m l => ⟨m.shape, l⟩) a.st.msgs a.ledgers⟩

theorem shOf_view (s : S) : K13.Honest.shOf s = viewM3 (chainSh s) := by
  unfold viewM3
  rw [chainSh_st, chainSh_ledgers]
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp [K13.Honest.shOf, chainSh, ChainSh.mk, ChainSh.here, ChainSh.reply,
      ChainSh.rowsOwed, ChainSh.indexMasks, ChainSh.pile, hereNo,
      K13.Honest.atFinC, S.noneWaits, K13.Honest.stSh, *] <;>
    (cases rowsOwed <;> exact ⟨rfl, fun _ _ => rfl⟩)

/-- The shape at the rows' sub-protocol and at the chain's end, read off the chain's. -/
def viewM4 (a : ChainSh) : K13.Honest.Sh4 :=
  match a.atEnd with
  | some e => ⟨true, e.2.1, e.2.2, a.rowsOwed, a.st⟩
  | none => ⟨false, #[], none, a.rowsOwed, a.st⟩

theorem sh4_view (s : S) : K13.Honest.sh4 s = viewM4 (chainSh s) := by
  unfold viewM4
  rw [chainSh_st]
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.viewSt_stSh
#print axioms VerifiableInference.Desc.First.Shape.chainSh_st
#print axioms VerifiableInference.Desc.First.Shape.chainSh_ledgers
#print axioms VerifiableInference.Desc.First.Shape.chainSh_roots
#print axioms VerifiableInference.Desc.First.Shape.chainSh_putTl
#print axioms VerifiableInference.Desc.First.Shape.chainSh_putFork
#print axioms VerifiableInference.Desc.First.Shape.chainSh_putLink
#print axioms VerifiableInference.Desc.First.Shape.chainSh_ground
#print axioms VerifiableInference.Desc.First.Shape.chainSh_check
#print axioms VerifiableInference.Desc.First.Shape.chainSh_live
#print axioms VerifiableInference.Desc.First.Shape.chainSh_k8set
#print axioms VerifiableInference.Desc.First.Shape.part_sh
#print axioms VerifiableInference.Desc.First.Shape.part_of_sh
#print axioms VerifiableInference.Desc.First.Shape.chainSh_withReq
#print axioms VerifiableInference.Desc.First.Shape.chainSh_rowsOwed
#print axioms VerifiableInference.Desc.First.Shape.chainSh_mark
#print axioms VerifiableInference.Desc.First.Shape.shOf_view
#print axioms VerifiableInference.Desc.First.Shape.sh4_view
