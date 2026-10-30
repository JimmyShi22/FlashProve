-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Stored/HeadSeat.lean.
WHAT IT IS. What the output head's own rounds have heard (Desc/Kinds/: HeardAll) as the record of
the same in the carried state (Model.Head.Heard, fifteen fields), and back; and the reader of the
three further reads (planeEntry). THE SEAT OF THE HEAD's OWN ROUNDS (Stored/HeadSeatAt.lean) CALLS
THESE: a description that seats that block runs this text.
WHAT IT DOES NOT SHOW. Definitions alone.
Why the record has this form. The blocks behind the head's own rounds read it: it is the record of
the program `verify-on-bytes`, and the carried state keeps its type.
What is made anew here, because the kind's text does not keep it, or keeps it in the form of the
part «the masked sumcheck»: that part's record as the program's (pscOf) and back (keptOf); the
powers of the two batching elements; each sumcheck's form (the program makes it at the hearing, the
text with the claims); the mark that the form is made; the channels' challenges in the order of
their bits; the numbers of two calls.

-/
import Johnson.Desc.Kinds.HeadCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open OnBytes OnBytes.Model
open Norm (lt ls lPd T)
open Part.MaskedSum (Var)

/-- A hidden scalar's number. -/
def slotOf (h : Hid) : Nat := (h.var.slots.getD 0 (0, zeroE)).1

/-- 1, x, x^2, ..: n powers. -/
def powersOf (x : E) (n : Nat) : Array E := (Array.range n).map fun i => powE x i

/-- How a variable is summed, as the program keeps it. -/
def weightOf : Var → OnBytes.Psc.Weight
  | .plain d => .plain d
  | .point z d => .equality z d

/-- And back: the program's plain sum leaves out the linear coefficient, its sum at a point the
constant one; the point is the sum of X. -/
def varOf (w : OnBytes.Psc.Weight) : Var :=
  if w.fixed == 1 then .plain w.d else .point (w.moment.getD 1 zeroE) w.d

/-- What the part's hearing hands back, as the program's record of a sumcheck. Three of its ten
fields are set by hand: ended, started; rowMade as it is handed in. -/
def pscOf (k : Option Part.MaskedSum.Heard) (rowMade : Bool) : Psc :=
  match k with
  | none => {}
  | some h =>
    { start := h.start, target := h.target, eps := h.eps, claim := h.claim, first := h.first,
      vars := (h.vars.map weightOf).toArray, r := h.r.toArray, ended := true, rowMade,
      started := true }

/-- And back. sEnd: the first end value's number. -/
def keptOf (p : Psc) (sEnd : Nat) : Part.MaskedSum.Heard :=
  { start := p.start, target := p.target, eps := p.eps, claim := p.claim, first := p.first,
    vars := p.vars.toList.map varOf, r := p.r.toList, sEnd := sEnd }

/-- A token sumcheck as the program keeps it. r: its challenges on the positions. S0: the summand on
the end values as shown. -/
def tscOf (s : Sum) (r : Point) (S0 : E) : Tsc :=
  { sCl := slotOf s.claimed, sEnd := slotOf (s.end_ 0), r, p := pscOf s.psc true,
    rowU := s.left S0 }

/-- The program's record. g1: the lookup's, handed through. qN, qH: the numbers of the lookup's
calls with the segments "NF" and "HD0": `verify-on-bytes` reads them off the layout (callNo); HERE
BOTH ARE LAID AS 0. NO TEST OF THIS FILE HOLDS THE LAYOUT AGAINST THAT; the step that makes the
tables of reads takes its points at these two numbers. -/
def heardOf [Sizes] [Request] [Token] (g1 : Forest.Heard) (H : HeardAll) :
    Model.Head.Heard :=
  let n := H.1; let f := H.2.1; let h := H.2.2
  let two (s : Sum) : E := mulE (s.end_ 0).shown (s.end_ 1).shown
  { win := (Array.range T).map fun t => if checked t then win t else 0
    g1, Zl := g1.zx.extract (g1.zx.size - (ls + lt)) g1.zx.size, PV := n.pV
    sW := slotOf (n.W.getD 0 {}), gp := powersOf n.gam 9
    wpl := { r := n.squares.r, sL := slotOf (n.squares.end_ 0), sR := slotOf (n.squares.end_ 1),
             tau := n.squares.down, row := n.squares.left (two n.squares) }
    sPv := slotOf (n.P.getD 0 {}), omV := powersOf n.om 7
    tV := tscOf n.products n.products.r
      (OnBytes.Desc.First.P6.summand (fun i => powE n.om i) fun j => (n.products.end_ j).shown)
    tN := tscOf f.normed f.normed.r (two f.normed)
    tH := tscOf h.logits (h.logits.r.extract 0 lt) (two h.logits)
    rs := (h.logits.r.extract lt (lt + lPd)).reverse
    qN := 0, qH := 0 }

/-- A hidden scalar by its number: what is shown of it stands in the ledger; nothing if none is. -/
def hidAt (F : Fork) (j : Nat) : Option Hid :=
  (F.shown j).map fun x => { var := Aff.slot j, shown := x }

/-- n hidden scalars from number j on. -/
def hidsAt (F : Fork) (j n : Nat) : Option (Array Hid) :=
  ((List.range n).mapM fun i => hidAt F (j + i)).map (·.toArray)

/-- A token sumcheck of the program's, as the text keeps one. r: all its challenges, in the order of
the rounds; ends: the number of its end values. -/
def sumOf (F : Fork) (t : Tsc) (r : Point) (ends : Nat) : Option Sum := do
  pure { r, claimed := ← hidAt F t.sCl, ends := ← hidsAt F t.sEnd ends,
         psc := some (keptOf t.p t.sEnd) }

/-- THE WAY BACK: what the text heard, out of the program's record, the ledger, and the one thing
that the program's record does not keep: the state of the squares' level's sumcheck. Nothing where a
scalar is not in the ledger or a batching element is not in the record. -/
def allOf (F : Fork) (x : Model.Head.Heard) (squares : Option Part.MaskedSum.Heard) :
    Option HeardAll := do
  pure ({ pV := x.PV, W := ← hidsAt F x.sW 9, gam := ← x.gp[1]?, rhoI := #[]
          squares := { r := x.wpl.r, ends := #[← hidAt F x.wpl.sL, ← hidAt F x.wpl.sR],
                       down := x.wpl.tau, psc := squares }
          P := ← hidsAt F x.sPv 7, om := ← x.omV[1]?
          products := ← sumOf F x.tV x.tV.r 4 },
        { normed := ← sumOf F x.tN x.tN.r 2 },
        { logits := ← sumOf F x.tH (x.tH.r ++ x.rs.reverse) 2 })

/-- The three further reads, of the program's table of its tables (name; first entry; length): by
the program's names; an entry at or beyond a table's length is refused, as the program's own reader
refuses it. iU3: the number of the reads' array; cols: its number of columns. -/
def planeEntry (tab : List (String × Nat × Nat)) (iU3 cols : Nat) (x : PlaneRead) (i : Nat) :
    Option Form :=
  (tab.find? fun e => e.1 == (match x with
    | .bits0 => "bH-bits-0" | .bits1 => "bH-bits-1" | .pin => "bH-pin")).bind fun e =>
    if i < e.2.2 then some (Aff.ent iU3 ((e.2.1 + i) / cols) ((e.2.1 + i) % cols)) else none

end VerifiableInference.Desc.Kinds.Head
