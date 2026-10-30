-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/Laws.lean: what it means that a flat function (OnBytes/K/Kc/Flat.lean) is the program's
routine, and the five statements that say so for the head's receiving routines.

A run of the program's routine on a view starts from a state F of the sub-proof and a context C and,
if it succeeds, returns a value a and leaves a state G and a context D. The context holds the view's
rounds that are not yet closed (`Chan.pending`, OnBytes/Iop/GroundLaws.lean) and the plan's entries
of these rounds. 'tape C' reads them as plain data: of each round its leading items that are
elements of the extension field, the elements that it drew, and three words of its entry.

'Left C D': what a receiving routine leaves of the context. D is the context of a run on a view; the
statement, the book of trees, the record of a failed test, the opened columns not yet read, the
number of roots received, the first tree's number and the number of answers to a sample are C's; and
D's rounds and entries are C's after some ELEMENTS OF THE FIELD were taken and some rounds closed,
each round under the plan's next entry and with as many draws as that entry says; the entry of the
round closed last and the mark that its rows were asked go along (`Eats`, on the view's rounds
THEMSELVES, not on their reading as plain data).

'Sim X f': whenever the routine X, run on a view (not dry) from F and C, succeeds with a, G and D,
the flat function f at F and 'tape C' returns a, G and 'tape D'; and 'Left C D'. All five states
are letters of the statement, tied at both ends: nothing stands under "there is".

The five statements, each a definition of its own name, so that a theorem can take one as a
hypothesis and a proof can discharge it: `LawPoint`, `LawSquares`, `LawProducts`, `LawStream`,
`LawLogits`.

Not claimed. One direction alone: from the program's success to the flat function's value. The
converse is not stated: the program's channel also tests numbers of the plan's entries that a flat
function does not see (positions, matrix entries, the kind that belongs to a name), and it refuses
to close a round whose next item is no element of the field, where a flat function sees nothing left
to take. `Left` does not speak of the kept intermediate values or of whether such values are kept;
of the round being received and the rounds not yet begun it speaks through `Chan.pending` alone.
Nothing on the dry run. Nothing on soundness. The program does not import this file.
-/
import OnBytes.K.Kc.Flat
import OnBytes.Iop.GroundLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM)

/-! ## The context's rounds as plain data -/

/-- The leading items of a message that are elements of the extension field. -/
def leading : List Fmt.ItemValue → List E
  | .e x :: l => E.ofTriple x :: leading l
  | _ => []

/-- A view's round, with its entry in the plan if there is one, as plain data. -/
def flatOf (r : Fmt.RoundView) (e : Option Fmt.Entry) : FlatRound where
  name := e.map (·.name)
  nz := (e.map (·.drawNZ)).getD 0
  rows := (e.map (·.rows)).getD 0
  sent := leading r.vals
  drawn := r.drawn.elems.map E.ofTriple

/-- Rounds with their entries, one for each in their order. -/
def paired : List Fmt.RoundView → List Fmt.Entry → Tape
  | [], _ => []
  | r :: rs, [] => flatOf r none :: paired rs []
  | r :: rs, e :: es => flatOf r (some e) :: paired rs es

/-- The rounds that a context has not yet closed, as plain data. -/
def tape (C : Ctx) : Tape := paired C.ch.pending C.ch.entries

/-! ## What a receiving routine leaves -/

/-- Four parts of a channel, before and behind: the rounds not yet closed, the plan's entries of
these rounds, the entry of the round closed last, and the mark that its rows were asked. From the
first four to the last four by three kinds of step: an ELEMENT OF THE FIELD is taken off the first
round; the first round, of which all is taken, is closed under the plan's next entry, which becomes
the entry closed last, its rows not asked; the rows of the entry closed last are asked. -/
inductive Eats : List Fmt.RoundView → List Fmt.Entry → Option Fmt.Entry → Bool →
    List Fmt.RoundView → List Fmt.Entry → Option Fmt.Entry → Bool → Prop
  | refl (l : List Fmt.RoundView) (es : List Fmt.Entry) (la : Option Fmt.Entry) (a : Bool) :
      Eats l es la a l es la a
  | item {r : Fmt.RoundView} {x : UInt64 × UInt64 × UInt64} {vs : List Fmt.ItemValue} {rest l' : List Fmt.RoundView}
      {es es' : List Fmt.Entry} {la la' : Option Fmt.Entry} {a a' : Bool}
      (h : r.vals = .e x :: vs) (t : Eats ({ r with vals := vs } :: rest) es la a l' es' la' a') :
      Eats (r :: rest) es la a l' es' la' a'
  | close {r : Fmt.RoundView} {e : Fmt.Entry} {rest l' : List Fmt.RoundView} {es es' : List Fmt.Entry}
      {la la' : Option Fmt.Entry} {a a' : Bool} (h : r.vals = [])
      (h1 : r.drawn.elems.length = e.drawE) (h2 : r.drawn.poss.length = e.poss)
      (h3 : r.drawn.trits.length = e.trits) (t : Eats rest es (some e) false l' es' la' a') :
      Eats (r :: rest) (e :: es) la a l' es' la' a'
  | asked {l l' : List Fmt.RoundView} {es es' : List Fmt.Entry} {la la' : Option Fmt.Entry} {a a' : Bool}
      (t : Eats l es la true l' es' la' a') : Eats l es la a l' es' la' a'

theorem Eats.trans {l1 l2 l3 : List Fmt.RoundView} {e1 e2 e3 : List Fmt.Entry}
    {m1 m2 m3 : Option Fmt.Entry} {a1 a2 a3 : Bool} (x : Eats l1 e1 m1 a1 l2 e2 m2 a2)
    (y : Eats l2 e2 m2 a2 l3 e3 m3 a3) : Eats l1 e1 m1 a1 l3 e3 m3 a3 := by
  induction x with
  | refl => exact y
  | item h _ ih => exact .item h (ih y)
  | close h h1 h2 h3 _ ih => exact .close h h1 h2 h3 (ih y)
  | asked _ ih => exact .asked (ih y)

/-- What a receiving routine, run on a view from C, leaves in D. -/
structure Left (C D : Ctx) : Prop where
  dry : D.ch.dry = false
  st : D.st = C.st
  book : D.book = C.book
  failed : D.failed = C.failed
  opened : D.ch.opened = C.ch.opened
  roots : D.ch.roots = C.ch.roots
  firstTree : D.ch.firstTree = C.ch.firstTree
  samples : D.ch.samples = C.ch.samples
  eats : Eats C.ch.pending C.ch.entries C.ch.last C.ch.askedRows
    D.ch.pending D.ch.entries D.ch.last D.ch.askedRows

theorem Left.refl {C : Ctx} (hd : C.ch.dry = false) : Left C C :=
  ⟨hd, rfl, rfl, rfl, rfl, rfl, rfl, rfl, .refl _ _ _ _⟩

theorem Left.trans {A B C : Ctx} (x : Left A B) (y : Left B C) : Left A C :=
  ⟨y.dry, y.st.trans x.st, y.book.trans x.book, y.failed.trans x.failed,
    y.opened.trans x.opened, y.roots.trans x.roots, y.firstTree.trans x.firstTree,
    y.samples.trans x.samples, x.eats.trans y.eats⟩

/-- A call that only keeps an intermediate value. -/
theorem Left.of_same {C D : Ctx} (hd : C.ch.dry = false) (s : Blk.SameButNotes C D) : Left C D := by
  have e := s.ch
  exact ⟨by rw [e]; exact hd, s.st, s.book, s.failed, by rw [e], by rw [e], by rw [e], by rw [e],
    by rw [e]; exact .refl _ _ _ _⟩

/-! ## The two notions -/

/-- The flat function g is the block x, in a run on a view. -/
def SimB {α : Type} (x : Blk α) (g : Tape → Option (α × Tape)) : Prop :=
  ∀ (C D : Ctx) (a : α), C.ch.dry = false → x.Yields C a D →
    g (tape C) = some (a, tape D) ∧ Left C D

/-- The flat function f is the routine X, in a run on a view. -/
def Sim {α : Type} (X : SubM α) (f : Fl α) : Prop :=
  ∀ (F G : Fork) (C D : Ctx) (a : α), C.ch.dry = false → (X F).Yields C (a, G) D →
    f F (tape C) = some (a, G, tape D) ∧ Left C D

/-- The norm's point. -/
def LawPoint : Prop := ∀ lt : Nat, Sim (SubM.point .zero lt) (flatPoint lt)

/-- The sums of limb products with their product layer. -/
def LawSquares : Prop :=
  ∀ (h : Model.Head.Shape) (PV : Array E),
    Sim (Model.Head.hearSquares h PV) (flatSquares h.XL h.lPd h.lt PV)

/-- The row products with their token sumcheck. -/
def LawProducts : Prop :=
  ∀ (h : Model.Head.Shape) (PV : Array E),
    Sim (Model.Head.hearProducts h PV) (flatProducts h.XL h.lt PV)

/-- The stream times the reciprocal. -/
def LawStream : Prop :=
  ∀ (h : Model.Head.Shape) (zt : Array E), Sim (Model.Head.hearStream h zt) (flatStream h.lt zt)

/-- The activations times the head's weights. -/
def LawLogits : Prop :=
  ∀ (h : Model.Head.Shape) (lam : Nat) (zt : Array E),
    Sim (Model.Head.hearLogits h lam zt) (flatLogits h.lt lam zt)

end OnBytes.K.Kc
