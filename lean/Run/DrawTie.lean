-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawTie.lean: the readers of the draws compute, through `out`, the same as the functions on
machine words that run. The readers are the trees `tree f d` (Run/DrawPage.lean). For `Lawful`
draws a bound on these readers' bias is proved (Run/DrawPageProofs.lean).

This file is about how a verifier message is made from a row of 64-bit words.
Definitions and statements (each a `Prop` in `Run.Spec`); the proofs are in Run/DrawTieProofs.lean.
Two texts say how a verifier message is drawn. Fmt/Rules6.lean has functions that compute, on a row
of machine words and a place in it (`Dr`: `pure`, `bind`, `word`); their values are as they are
handed on: machine words, natural numbers, lists of integers, bytes. Run/DrawPage.lean has trees
(`Tr`), with values in finite types; for these a bound on how many rows give one value is stated,
for `Lawful` draws (proved in Run/DrawPageProofs.lean). This file ties them.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `t.runAt row c`: a tree on a row of words (a function from places to words), from the place c:
    the value, and the place after the words used.
  `out f d v`: the value as it is handed on: a triple of numbers below p ↦ the triple of words; a
    number below 2^k ↦ the number; n pairs of bits ↦ the list of the n entries; four words ↦ their
    32 bytes, each word lowest byte first.
  `outAll f ds v`: the same for a list of draws.
  `rowFn d u`: a row of K words as a function from places; beyond the end its value is d.
  `Spec.drawTie_read`: for each field f, draw d, row, place c: `d.read f row c` = (`out f d` (value
    of `tree f d` from c), its place).
  `Spec.drawTie_all`: `readAll f ds row c` = (`outAll f ds` (value of `all f ds` from c), its
    place).
  `Spec.drawTie_ev`: a tree that asks for at most K words has on a row of K words (`Tr.ev`) the
    value that `runAt` gives on `rowFn`, from the place 0.
  `Spec.drawTie_bs`: `outAll f ds ((bsOf f ds).φ u)` = the value of `readAll f ds` on the row of
    the words of the blocks u, from the place 0.
  `Spec.drawTie_inj`: `out f d` is one to one, for every draw but the matrix entries (two pairs of
    bits give the entry 0): so nothing is lost between the two texts but what the format itself
    drops.

The rules (docs/format/FORMAT.md, section 6, as Fmt/Rules6.lean renders it; written against an
edition of the page that is not the one that ships): R6.1 (the next words of the row: hence the
place beside the value), R6.2 (the order is the
list's), R6.4, R6.5, R6.6, R6.7 (`trit`), R6.8 with R1.5 (four words, each lowest byte first).

Notation:
  `f`: the field, one of the format's two (`Fmt.Fld`, Fmt/Rules1.lean);
  `p`: the number below which the field's elements lie (`Fmt.Fld.p`);
  `all f ds`: a round's draws, one after the other (Run/DrawPage.lean);
  `bsOf f ds`: the block sampler of a round (Run/DrawPage.lean).

Limits: this file does not say what a draw of positions hands on. That is two things: the draws in
the order drawn, and their set in increasing order. Both are functions of the list of the values
".pos". Neither `Fmt.readAll` nor `all` makes them: neither applies `Fmt.listOf`. Fmt/Rules6.lean
defines `Fmt.listOf` and `Fmt.drawPoss`.
This file does not say that the words of a block of 256 bits are the words that `Fmt.rowOfBlocks`
reads off 32 bytes. That depends on how 32 bytes become 256 bits, which belongs to the encoding of
the queries. (For the block's words see Run/DrawBS.lean: bit 64 j + t of the block is bit t of word
j.)
This file says nothing on which draws a round has.

Terms: lean/GLOSSARY.md.
-/
import Run.DrawPage

set_option autoImplicit false

namespace Run
open Iop

/-- A tree on a row of words, from a place. -/
def Tr.runAt {W C : Type} : Tr W C → (ℕ → W) → ℕ → C × ℕ
  | .ret a, _, c => (a, c)
  | .ask k, row, c => Tr.runAt (k (row c)) row (c + 1)

/-- a number below p as a machine word -/
def toU {f : _root_.Fmt.Fld} (x : FV f) : UInt64 := UInt64.ofNat x.val

def toU3 {f : _root_.Fmt.Fld} (e : EV f) : _root_.Fmt.Ext := (toU e.1, toU e.2.1, toU e.2.2)

/-- an entry of the matrix from its pair of bits -/
def trit (b : Bool × Bool) : Int := if b.1 then (if b.2 then -1 else 1) else 0

/-- The value as it is handed on. -/
def out (f : _root_.Fmt.Fld) : (d : _root_.Fmt.Draw) → DVal f d → _root_.Fmt.Val
  | .elem, e => .ext (toU3 e)
  | .elemNZ, e => .ext (toU3 e.1)
  | .pos _, x => .pos x.val
  | .trits _, b => .trits (List.ofFn fun j => trit (b j))
  | .sealed, ws => .sealed (_root_.Fmt.cat ((List.ofFn ws).map _root_.Fmt.u64))

def outAll (f : _root_.Fmt.Fld) : (ds : List _root_.Fmt.Draw) → Vals f ds → List _root_.Fmt.Val
  | [], _ => []
  | d :: ds, v => out f d v.1 :: outAll f ds v.2

/-- a row of K words as a function from places -/
def rowFn {W : Type} (d : W) {K : ℕ} (u : Fin K → W) : ℕ → W := fun i =>
  if h : i < K then u ⟨i, h⟩ else d

namespace Spec

/-- Every draw. -/
def drawTie_read : Prop :=
  ∀ (f : _root_.Fmt.Fld) (d : _root_.Fmt.Draw) (row : _root_.Fmt.Row) (c : ℕ),
    d.read f row c = (out f d ((tree f d).runAt row c).1, ((tree f d).runAt row c).2)

/-- A round's draws. -/
def drawTie_all : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List _root_.Fmt.Draw) (row : _root_.Fmt.Row) (c : ℕ),
    _root_.Fmt.readAll f ds row c =
      (outAll f ds ((all f ds).runAt row c).1, ((all f ds).runAt row c).2)

def drawTie_ev : Prop :=
  ∀ (W C : Type) (d : W) (t : Tr W C) (K : ℕ) (u : Fin K → W),
    t.Most K → t.ev d K u = (t.runAt (rowFn d u) 0).1

/-- The value of a round's block sampler, taken through `outAll`, is the value of the list of draws
that runs. -/
def drawTie_bs : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List _root_.Fmt.Draw) (u : Fin (bsOf f ds).b → Dig 256),
    outAll f ds ((bsOf f ds).φ u) =
      (_root_.Fmt.readAll f ds (rowFn 0 (rowOf e64 (bsOf f ds).b u)) 0).1

def drawTie_inj : Prop :=
  ∀ (f : _root_.Fmt.Fld) (d : _root_.Fmt.Draw), (∀ n, d ≠ .trits n) → Function.Injective (out f d)

end Spec
end Run
