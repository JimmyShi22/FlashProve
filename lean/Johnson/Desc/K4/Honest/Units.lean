-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Units.lean: sums over one unit of the committed matrix of weights, under the
factors of a claim, with some of the unit's index groups left open. Definitions with code.
No theorem.

NOT SHOWN HERE. No theorem says that `fbFree` is the sum that its docstring states. THREE SMALL
RULES ARE TYPED HERE THAT THE VERIFIER's TEXT DOES NOT HAVE AS FUNCTIONS: from the part of an index
that lies in a column's number and the part that lies in a row's number back to the index
(`grpIndex`); a group's part of a column's number (`colPart`); a factor's weight on an index
(`facAt`). They are the format's (docs/format/11-5-weights-in-the-table.md), the first read
backwards ("The position of a digit").

What is summed. The committed matrix holds the digits of all weights (OnBytes/Model/Weights.lean). A
unit is a run of its rows: one weight matrix of one layer. A weight of the unit is named by one
index from each of the unit's index groups; its digit number q lies in a row and a column that the
indices and q fix. A claim has a factor for each group: it gives each index of the group a weight.
The claim's value is the sum over the unit's weights of the weight times the product of its indices'
weights. `fbFree` is that sum with the groups named in `free` left open: one value for each choice
of their indices, summed over the other groups alone.

How. The weight that the closed groups give a cell is a product of a weight on its column and a
weight on its row. Both are made by the verifier's own functions, group by group
(`WsFac.onColumns` at a corner; `WsFac.onRows`, `WsRowFac.table`, `wsOuter`, `wsDigits`, in the
order of `wsGamma`). An open group counts as 1 there. The number of the entry to which a cell adds
is the sum of a number of its column and a number of its row. The unit's cells are gone through
once.

  `facAt`                     a factor's weight on an index
  `grpIndex`, `colPart`        an index of its two parts; a group's part of a column's number
  `stridesOf`                 the open groups' strides, and the number of entries
  `colWeight`, `rowWeights`, `rowNumbers`, `colNumber`   the two weights; the two numbers
  `fbFree`, `fbTable`         THE SUMS; with no group open: one entry, the claim's value

Limits. The cost is one step for each cell of the unit in a column whose weight is not 0; these are
definitions for small sizes, not a program for the full size. A cell that belongs to no weight (a
column from 2 ^ ncb on; a column whose part for a group of class 'A' is not below the group's
extent) is not read. The entries of the matrix are the program's words; a word that is not below
the field's prime is not looked for. The unit is taken as the verifier's maker lays it
(`WsLay.add`, OnBytes/Model/Weights.lean): of this `fbFree` tests one thing, that the rows' weights
and numbers are as many as the unit's rows; that the groups' fields agree with each other beyond
that, and that no two groups have one name, is not tested.
Nothing on any property.
No property is claimed.
-/
import OnBytes.Model.Merge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (WsLay WsUnit WsGrp WsFac WsClaim eqOne wsOuter wsDigits)

/-- **A factor's weight on an index of its group.** Class 'E': the index is hi 2 ^ z + lo, and the
weight is HV[hi] times the equality weight of lo at the factor's point. Class 'A': AV[v]. -/
def facAt (x : WsFac) (g : WsGrp) (v : Nat) : E :=
  if g.cls == 'E' then mulE (x.HV.getD (v / 2 ^ g.z) zeroE) (eqOne x.pt (v % 2 ^ g.z))
  else x.AV.getD v zeroE

/-- **An index of a group, of its two parts**: col, what the group gives to the column's number;
rho, what it leaves to the row's number. Class 'E', the lowest t bits taken: rho 2 ^ t + col. Class
'E', the highest t of the z low bits taken: with k = z - t, rho is hi 2 ^ k + (the k lowest bits),
and the index is hi 2 ^ z + col 2 ^ k + (the k lowest bits). Class 'A': the part that is there. In
each class the index is the sum of its values at (col, 0) and at (0, rho). -/
def grpIndex (g : WsGrp) (col rho : Nat) : Nat :=
  if g.cls == 'E' then
    if g.high then
      rho / 2 ^ (g.z - g.t) * 2 ^ g.z + col * 2 ^ (g.z - g.t) + rho % 2 ^ (g.z - g.t)
    else rho * 2 ^ g.t + col
  else if g.aTaken then col
  else rho

/-- A group's part of the number of column c. -/
def colPart (g : WsGrp) (c : Nat) : Nat := c / 2 ^ g.cb0 % 2 ^ g.t

/-- The stride of each open group, and the number of entries: the first name is the most
significant, and each group counts with its extent. A name that is no group's counts with the extent
1. -/
def stridesOf (u : WsUnit) (free : List String) : List (String × Nat) × Nat :=
  free.foldr
    (fun n s => ((n, s.2) :: s.1, s.2 * ((u.g.find? fun g => g.name == n).map (·.R)).getD 1))
    ([], 1)

/-- The stride of a group; nothing if it is closed. -/
def strideOf (st : List (String × Nat)) (g : WsGrp) : Option Nat :=
  (st.find? fun x => x.1 == g.name).map (·.2)

/-- **The weight of column c**: the product of the closed groups' factors on their column bits, at
the corner c. It is 0 from column 2 ^ ncb on, and where an open group of class 'A' has a part that
is not below its extent. -/
def colWeight (u : WsUnit) (fs : List (WsFac × WsGrp)) (st : List (String × Nat)) (c : Nat) : E :=
  if 2 ^ u.ncb ≤ c then zeroE
  else
    fs.foldl
      (fun p y =>
        match strideOf st y.2 with
        | none => mulE p (y.1.onColumns y.2 fun b => if c.testBit b then oneE else zeroE)
        | some _ => if y.2.aTaken && y.2.R ≤ colPart y.2 c then zeroE else p)
      oneE

/-- What column c adds to an entry's number. -/
def colNumber (fs : List (WsFac × WsGrp)) (st : List (String × Nat)) (c : Nat) : Nat :=
  fs.foldl
    (fun n y =>
      match strideOf st y.2 with
      | none => n
      | some s => n + s * grpIndex y.2 (colPart y.2 c) 0)
    0

/-- **The weights of the unit's rows**, from its first row on: 256 ^ q for digit number q, times the
closed groups' factors on the rows. In the order of the verifier's `wsGamma`: the digit's number is
the most significant place of a row's number, the first group the least. -/
def rowWeights (u : WsUnit) (fs : List (WsFac × WsGrp)) (st : List (String × Nat)) : Array E :=
  fs.reverse.foldl
    (fun v y =>
      wsOuter v
        (match strideOf st y.2 with
         | none => (y.1.onRows y.2).table y.2
         | some _ => Array.replicate y.2.left oneE))
    (wsDigits u.nlw oneE).toArray

/-- All sums a[i] + b[q], at the index i |b| + q. -/
def outerAdd (a b : Array Nat) : Array Nat :=
  a.foldl (fun out x => b.foldl (fun o y => o.push (x + y)) out)
    (Array.emptyWithCapacity (a.size * b.size))

/-- What each row of the unit adds to an entry's number, in the order of `rowWeights`. -/
def rowNumbers (u : WsUnit) (fs : List (WsFac × WsGrp)) (st : List (String × Nat)) : Array Nat :=
  fs.reverse.foldl
    (fun v y =>
      outerAdd v
        (match strideOf st y.2 with
         | none => Array.replicate y.2.left 0
         | some s => (Array.range y.2.left).map fun rho => s * grpIndex y.2 0 rho))
    (Array.replicate u.nlw 0)

/-- **The unit's weights under a claim's factors, with the groups named in `free` left open.** lay:
the layout of the committed matrix; w: the matrix, by row and column; c: the claim. The entry's
number is made of the open groups' indices in mixed radix, in the order of `free`, the first the
most significant, each with its extent. The entry is the sum, over all indices of the other groups,
of the weight (the sum over its digits q of 256 ^ q times the digit) times the product of the
claim's factors on these indices. The factors of the open groups are not read. Nothing: the layout
has no such unit; the claim has not one factor for each group; a name in `free` is no group of the
unit, or stands there twice; a closed factor has not the sizes that its group asks for (the
verifier's own test, `WsFac.fits`); the rows' weights or numbers are not as many as the unit's rows.
-/
def fbFree (lay : WsLay) (w : Nat → Nat → F) (c : WsClaim) (free : List String) :
    Option (Array E) :=
  match lay.U[c.ui]? with
  | none => none
  | some u =>
    let fs := c.f.zip u.g
    let st := stridesOf u free
    let rw := rowWeights u fs st.1
    let rn := rowNumbers u fs st.1
    if c.f.length != u.g.length || !(free.all fun n => u.g.any fun g => g.name == n) ||
        free.eraseDups.length != free.length || rw.size != u.rows || rn.size != u.rows ||
        !(fs.all fun y => (strideOf st.1 y.2).isSome || y.1.fits y.2) then none
    else
      -- the columns with a weight, gathered by what they add to the entry's number
      let byNumber : Array (Array (Nat × E)) :=
        (List.range (2 ^ u.ncb)).foldl
          (fun b col =>
            let k := colWeight u fs st.1 col
            if isZeroE k then b else b.modify (colNumber fs st.1 col) (·.push (col, k)))
          (Array.replicate st.2 #[])
      let live : List (Array (Nat × E) × Nat) := byNumber.toList.zipIdx.filter fun b => !b.1.isEmpty
      some ((List.range u.rows).foldl
        (fun out y =>
          let k := rw.getD y zeroE
          if isZeroE k then out
          else
            live.foldl
              (fun out b =>
                out.modify (rn.getD y 0 + b.2) fun s =>
                  maddE s k (b.1.foldl (fun t x => maddS t (w (u.off + y) x.1) x.2) zeroE))
              out)
        (Array.replicate st.2 zeroE))

/-- `fbFree`, with the empty array where it yields nothing. -/
def fbTable (lay : WsLay) (w : Nat → Nat → F) (c : WsClaim) (free : List String) : Array E :=
  (fbFree lay w c free).getD #[]

end OnBytes.Desc.First.K4.Honest
