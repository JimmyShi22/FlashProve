-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabG.lean:
the tables of the factors of the long sums in the keys of the layers' calls; the rows that read
them; and the reader of a group's keys and bits that makes the tables once. Definitions with code.

Terms. Honest/K3/GLOSSARY.md. In this file: a table is an array, or an array of arrays to some
depth, made by `Memo.tab` (Honest/K3/Memo.lean) of one of the library's formulas; a row is a value
of `Row`, the rows that the sums read a value of `Inner` (Honest/K3/Tab/SisterG.lean).

What is defined.
  `tenTab`: of a tensor's name: instance, token, entry. `sumNames`, `tensTab`: the five names that
    stand in a long sum; each with its table. `suTab`: the gated products: layer, token, feature.
  `unitAt`, `dimAt`: the unit of a kind at a layer, as `wt` finds it; the number of indices of one
    of its groups.
  `segN`: the entries of a segment. `w0Tab`: the weights of kind 0: layer, head, coordinate,
    channel. `w2Tab`: of the units with two groups: kind, layer, second index, first index. `w3Tab`:
    of the other units with three groups: kind, layer, second, third, first index.
  `colTab`: which entry of which segment stands in a column: call, column.
  `innerTab`: the rows off five such arrays: a row is the innermost array, with the library's
    formula behind it.
  `layersTab`: the reader: the text of the field `layers` of `ownSources` (Honest/K3/WitOwner.lean)
    with the key's products and the search for a column's segment exchanged: the six arrays are
    bound in front of the structure; a key is `affG` at the seated reading plus the lift of `gamGBy`
    in the base field off the rows, under `kvOfBy` at `colTab`.

How it is meant. Each array is bound by a let in front of the structure that one application
returns. An application of a field of `innerTab` is whole: it picks the innermost array and returns
the row that holds it.

Imported. Honest/K3/Memo.lean, Honest/K3/Tab/SisterG.lean, Honest/K3/Tab/RingG.lean.

Users. Honest/K3/Tab/TabGLaw.lean and Honest/K3/Tab/TabAll.lean import this file.

Limits. The sizes are read off the layout's own entries (a tensor's cnt and J, the number of tokens,
a group's number of indices). No statement rests on a size: beyond an array's end the formula itself
is read, so a size that is too small costs time and nothing else. Nothing says how long anything
takes, nor how much room the arrays take. The equations are in Honest/K3/Tab/TabGLaw.lean.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Memo
import Johnson.Desc.ProofFile.Honest.K3.Tab.SisterG
import Johnson.Desc.ProofFile.Honest.K3.Tab.RingG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabG
open OnBytes.Model OnBytes.Ends.G
open ProofFile.Honest.K3.Memo (tab)

section Tables

variable {R : Type} [CommRing R] (P : Layer.Pub) (g : ℕ) (cell : NameG → R)

/-- A tensor's table: instance, token, entry. Empty for a name that the layout has not. -/
def tenTab (n : String) : Array (Array (Array R)) :=
  match P.y.T_ n with
  | some X => tab X.cnt fun inst => tab P.y.T fun i => tab X.J fun x => ten P cell n inst x i
  | none => #[]

/-- The names of the tensors that stand in a long sum. -/
def sumNames : List String := ["a", "m", "o", "xr", "sel"]

/-- These names, each with its table. -/
def tensTab : List (String × Array (Array (Array R))) := sumNames.map fun n => (n, tenTab P cell n)

/-- The gated products: layer, token, feature. -/
def suTab : Array (Array (Array R)) :=
  match P.y.T_ "s" with
  | some X => tab X.cnt fun lam => tab P.y.T fun i => tab X.J fun k => gated P cell lam k i
  | none => #[]

/-- The unit of kind X at layer l of the model, as `wt` finds it. -/
def unitAt (X l : ℕ) : Option WsUnit := (P.wsLay.unitOf X l).bind fun ui => P.wsLay.U[ui]?

/-- The number of indices of a unit's group number j. -/
def dimAt (u : WsUnit) (j : ℕ) : ℕ := (u.g.getD j default).R

/-- The largest number of entries of a segment of the given name in the calls. -/
def segN (sn : String) : ℕ :=
  P.y.calls.foldl
    (fun m c => c.segs.foldl (fun m s => if s.name == sn then max m s.pos.size else m) m) 0

/-- The weights of kind 0: layer of the group, head, coordinate, channel. Of the heads that the
unit's first group counts, those alone that an entry of the segment QK reaches. -/
def w0Tab : Array (Array (Array (Array R))) :=
  let heads := (segN P "QK" + P.y.h.dh - 1) / P.y.h.dh
  tab P.y.Lam fun lam =>
    match unitAt P 0 (lOf P g lam) with
    | some u =>
      tab (min (dimAt u 0) heads) fun hd => tab (dimAt u 1) fun cd => tab (dimAt u 2) fun k =>
        wt P cell 0 (lOf P g lam) [hd, cd, k]
    | none => #[]

/-- The weights of the units with two groups: kind, layer of the group, second index, first. -/
def w2Tab : Array (Array (Array (Array R))) :=
  tab 12 fun X => tab P.y.Lam fun lam =>
    match unitAt P X (lOf P g lam) with
    | some u =>
      if u.g.length == 2 then
        tab (dimAt u 1) fun x => tab (dimAt u 0) fun k => wt P cell X (lOf P g lam) [k, x]
      else #[]
    | none => #[]

/-- The weights of the units with three groups but kind 0's: kind, layer of the group, second
index, third, first. -/
def w3Tab : Array (Array (Array (Array (Array R)))) :=
  tab 12 fun X => tab P.y.Lam fun lam =>
    match unitAt P X (lOf P g lam) with
    | some u =>
      if u.g.length == 3 && X != 0 then
        tab (dimAt u 1) fun e => tab (dimAt u 2) fun x => tab (dimAt u 0) fun k =>
          wt P cell X (lOf P g lam) [k, e, x]
      else #[]
    | none => #[]

/-- Which entry of which segment stands in a column: call, column. -/
def colTab : Array (Array (Option (Seg × ℕ))) :=
  tab P.y.calls.size fun q => tab (2 ^ (P.y.calls.getD q default).lJ) fun j => colG P.y q j

/-- **The rows off five arrays.** Beyond an array's end the library's formula is read. -/
def innerTab (tens : List (String × Array (Array (Array R)))) (su : Array (Array (Array R)))
    (w0 w2 : Array (Array (Array (Array R)))) (w3 : Array (Array (Array (Array (Array R))))) :
    Inner R :=
  { tn := fun n inst i =>
      ⟨(((tens.lookup n).getD #[]).getD inst #[]).getD i #[], fun x => ten P cell n inst x i⟩
    su := fun lam i => ⟨(su.getD lam #[]).getD i #[], fun k => gated P cell lam k i⟩
    w0 := fun lam hd cd =>
      ⟨((w0.getD lam #[]).getD hd #[]).getD cd #[], fun k => wt P cell 0 (lOf P g lam) [hd, cd, k]⟩
    w2 := fun X lam x =>
      ⟨((w2.getD X #[]).getD lam #[]).getD x #[], fun k => wt P cell X (lOf P g lam) [k, x]⟩
    w3 := fun X lam e x =>
      ⟨(((w3.getD X #[]).getD lam #[]).getD e #[]).getD x #[], fun k =>
        wt P cell X (lOf P g lam) [k, e, x]⟩ }

end Tables

/-- **The reader of a group's keys and bits that makes the tables once.** -/
def layersTab (X : OnBytes.Model.Verify.Public) (g : ℕ) (C : Cells) (W : Weights) : LookIn :=
  let P := X.layers
  let cE := ownG X C.cell W.entry (linkG X g)
  let cF := ownGF X C.cell W.entry (linkG X g)
  let t1 := tensTab P cF
  let t2 := suTab P cF
  let t3 := w0Tab P g cF
  let t4 := w2Tab P g cF
  let t5 := w3Tab P g cF
  let t6 := colTab P
  let I := innerTab P g cF t1 t2 t3 t4 t5
  ⟨fun theta n =>
      OnBytes.Ends.jointKey P.y.fo
        (kvOfBy P (Memo.read2 t6 (colG P.y)) fun sn lam x i =>
          affG P g cE sn lam x i + algebraMap Cb.Gl.F Cb.Gl.E (gamGBy P g cF I sn lam x i))
        theta n,
   fun u j => bitsG X.y cE (u * 32 + j)⟩

end ProofFile.Honest.K3.TabG
