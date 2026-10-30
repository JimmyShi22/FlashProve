-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Loc.lean: the switch between two links of the second toy (a chain of three links), without a
batching element: the claim carried over and the rows at each drawn position. Both are on the next
group's carrying message and on the kept message sent anew.

Definitions that compute, with tests (#guard). No theorem. Core Lean; total. What the second toy is:
the head of Fmt/M2Dec.lean. A row here is a linear claim (`LRow`, Fmt/M2Types.lean). A tail is the r
entries that are encoded together with a message of l entries (`Code`, `symE`, Fmt/M1Codes.lean).

At the end of a link all its open claims are batched into one row and folded (close(m) in the head
of Fmt/M2Dec.lean). This is the link's closing. It leaves one claim, which the switch carries over.
The claim has forms on
  the folded main message,
  the kept member's table (if the group has a kept row),
  the folded old and fresh mask rows.
The next prover's message begins with a carrying message of two main rows over E and no mask row:
  row 0 is the folded main message;
  row 1 is all the rest, piece after piece (`restOff`), and its last place is the carrying message's
    own pad.
The kept row is sent anew (the second sending), with a fresh pad at its last three places. The old
pad's three entries lie in the rest.
Positions are drawn, and the old tree is opened there. The verifier makes rows that wait until the
next closing, where they are batched. So the functions here return rows.

Main names:
  `Off`, `restOff C Z kept`, `restSize`, `locFits`: where the pieces of the rest begin: old mask
    message, fresh mask message, the main row's tail, [the kept row's tail,] the two mask rows'
    tails, [the old pad's three entries]; they and the pad have room in one row.
  `overP`, `overPad`: a form on the old kept table, carried over. Its coefficients go to the same
    places of the second sending, except those at the three pad places: these go to the old pad's
    entries in the rest.
  `carried f C Z kept S`: the claim carried over.
  `drawL f C Z kept S x col`: the rows at one draw: main, [kept row,] old mask, fresh mask. The row
    for the kept row ties the second sending to the old tree: the second sending with the old pad
    put back, encoded with the old tail, has at x the symbol that the old tree shows.
  `oldSample f C Z Q y`: the old sample row of a kept message, carried over, with the old answer as
    target.
  `rowOfG`, `sumDrawsFromLit`, `sumDrawsFrom`: the draws' rows added onto a row that is there
    already (so that a closing can go on summing in the order of its rows).
  `LRow.add`, `sumDrawsLit`: `sumDrawsLit` is the meaning of `sumDraws`: every row is written out,
    then added. It gives the sum of all draws' rows, in the order drawn, repeats counted. The
    coefficients are the argument `first`, then `first` theta, and so on. It also gives the next
    power.
  `sumDraws`: the same values (within `locFits`), made faster in the way of the first toy's `csStep`
    (Fmt/M1Cs.lean):
      no row is written out: three lists (row 0, row 1, the second sending) are added to;
      the generator's entries lie in the base field;
      on row 1 a draw's pieces stand side by side from the place 0 on, and are added as one short
        list.
    Here tests; the theorem is in Fmt/M2LocEq.lean. It says that sumDraws = sumDrawsLit for all
    arguments, if, where there is a kept row, a row has at least three places (within `locFits` a
    row always has them); at shorter rows the two can differ.

The tests use a prover of this library's own at small sizes: rows and tails made up, folded, laid
as above; the old columns are encodings by Fmt/M1Codes.lean's `symE`, which is other code than the
generator's rows used here. Every row holds; each of five alterations (the main message, the second
sending, the old pad, the kept row's tail, a mask's message) makes just the rows fail that read the
altered entry.

Notation:
  g, p, t (`LRow`): forms on the carrying message's own table and on the table of the kept message
    sent anew, and the target;
  `Code`, written ⟨a, l, r⟩: a code: codewords of length 2^a, messages of l entries, a random tail
    of r entries;
  A0, A1, T, TK, T0, T1, OP (`Off`): where the seven pieces begin, in the order told at `restOff`;
  `S` (`KSRow`): what a fold hands on: s, the first toy's `SRow`, and the form kp (s.c, kp, s.d0,
    s.d1: the claim's forms, in the order of this head's first list; s.t: its target);
  `col` (in `drawL`; `KCol`): an opened column, laid on a group's rows (col.kept: the kept row's
    symbol);
  `cp`: the position of the mask code Z that goes with x;
  `yOf`: the three folded symbols of a column;
  `genM`, `genT`: the generator's row at x, on the message and on the tail.
  (`KSRow`, `KCol`: Fmt/M2Types.lean; `SRow`: Fmt/M1Types.lean; `cp`, `genM`, `genT`:
    Fmt/M1Codes.lean; `yOf`: Fmt/M1Cs.lean.)

Limits: what the head of Fmt/M2Send.lean lists as not said is not said here either. The groups of
this toy have one mask row or none (h = 0), so the mask symbols are taken as they stand (`yOf f 0`).
One place where the toy, which is rendered here, is not the letter of a write-up of our own (ONE
PRINT OF IT; its section on kept rows: a part that is that write-up's own, not restated from the
paper that this protocol builds on (lean/CREDITS.md); found in a second reading that held the
programs' description against that print; that finding has not been checked and stands here as a
question): there a kept message's main rows are rows of the group's word, at places among the 2^k,
replaced by zero rows; in the toy they are not among the 2^k rows: so a smaller k, fewer rounds of
the fold. (In an edition that is not the one that ships, and not held against that page, the format
page (docs/format/FORMAT.md, which comes with the programs) has the toy's form as a
rule: a kept message's rows count in the group in which its life ends, and in no other.)
The print has the old sample row of a kept message also as an open row of its own behind the drawing
of the positions. The toy has that row too: it stands right behind the
carried claim. The row is read on the second sending and, at the pad's three places, on the old pad
in the carrying message. Its target is the old answer. In Lean it is `oldSample` below. (It stands
among its own link's batched rows as well.) Where it stands among a closing's rows is the frame's
matter (`frontRows`, Fmt/M2Dec.lean), not this file's. The frame is that file's pass through the
rounds of the chain of links.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Types
import Fmt.M1Cs

namespace Fmt.M2
open Fmt.M1

/-- where the pieces of the rest begin -/
structure Off where
  A0 : Nat
  A1 : Nat
  T  : Nat
  TK : Nat
  T0 : Nat
  T1 : Nat
  OP : Nat
  deriving DecidableEq, Repr

def restOff (C Z : Code) (kept : Bool) : Off :=
  let TK := 2 * Z.l + C.r
  let T0 := TK + (if kept then C.r else 0)
  ⟨0, Z.l, 2 * Z.l, TK, T0, T0 + Z.r, T0 + 2 * Z.r⟩

/-- the entries of the rest -/
def restSize (C Z : Code) (kept : Bool) : Nat := (restOff C Z kept).OP + (if kept then 3 else 0)

/-- the rest and the carrying message's pad have room in one row; a kept row has its three pad
places -/
def locFits (C Z : Code) (kept : Bool) : Bool :=
  decide (restSize C Z kept + 1 ≤ C.l) && decide (3 ≤ C.l)

/-- the carrying message's table from its two rows -/
def twoRows (l : Nat) (r0 r1 : Array E) : Array E :=
  Array.ofFn (n := 2 * l) fun i => if i.val % 2 == 0 then ent r0 (i.val / 2) else ent r1 (i.val / 2)

/-- a row of l entries from pieces at their places -/
def restOf (f : Fld) (l : Nat) (ps : List (Nat × List E)) : Array E :=
  ps.foldl (fun a p => addV f a (layAt l p.1 p.2)) (zerosE l)

/-- a form on the old kept table, carried over: the part on the second sending (`overP`); the part
on the old pad's entries (`overPad`) -/
def overP (l : Nat) (Q : Array E) : Array E :=
  Array.ofFn (n := l) fun i => if i.val + 3 < l then ent Q i.val else Fld.zeroE
def overPad (l : Nat) (Q : Array E) : List E := [ent Q (l - 3), ent Q (l - 2), ent Q (l - 1)]

/-- The claim carried over. -/
def carried (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) : LRow :=
  let o := restOff C Z kept
  ⟨twoRows C.l S.s.c
      (restOf f C.l
        ([(o.A0, fitL Fld.zeroE Z.l S.s.d0.toList), (o.A1, fitL Fld.zeroE Z.l S.s.d1.toList)] ++
          (if kept then [(o.OP, overPad C.l S.kp)] else []))),
    if kept then overP C.l S.kp else #[],
    S.s.t⟩

/-- The rows at one draw. -/
def drawL (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (x : Nat) (col : KCol) : List LRow :=
  let o := restOff C Z kept
  let y := yOf f 0 S.s col.col
  let gmC := (genM C x).map Fld.ofF
  let gtC := (genT C x).map Fld.ofF
  let gmZ := (genM Z (cp Z x)).map Fld.ofF
  let gtZ := (genT Z (cp Z x)).map Fld.ofF
  [⟨twoRows C.l gmC.toArray (restOf f C.l [(o.T, gtC)]), #[], y.1⟩] ++
  (if kept then
      [⟨twoRows C.l #[] (restOf f C.l [(o.TK, gtC), (o.OP, overPad C.l gmC.toArray)]),
        overP C.l gmC.toArray,
        col.kept.getD Fld.zeroE⟩]
    else []) ++
  [⟨twoRows C.l #[] (restOf f C.l [(o.A0, gmZ), (o.T0, gtZ)]), #[], y.2.1⟩,
   ⟨twoRows C.l #[] (restOf f C.l [(o.A1, gmZ), (o.T1, gtZ)]), #[], y.2.2⟩]

/-- a + w r -/
def LRow.add (f : Fld) (a : LRow) (w : E) (r : LRow) : LRow :=
  ⟨axpy f a.g w r.g, axpy f a.p w r.p, f.addE a.t (f.mulE w r.t)⟩

/-- The sum of all draws' rows with the coefficients first, first theta, ..; the next power.
Literally. -/
def sumDrawsLit (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta first : E)
    (xs : List Nat) (col : Nat → Option KCol) : Option (LRow × E) :=
  xs.foldl (fun (acc : Option (LRow × E)) x =>
    match acc, col x with
    | some a, some cl =>
      some ((drawL f C Z kept S x cl).foldl
          (fun (s : LRow × E) r => (s.1.add f s.2 r, f.mulE s.2 theta)) a)
    | _, _ => none) (some (⟨zerosE (2 * C.l), if kept then zerosE C.l else #[], Fld.zeroE⟩, first))

/-- one draw added onto (row 0, row 1, the second sending, the target, the power) -/
def addDrawL (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (x : Nat) (cl : KCol) :
    List E × List E × List E × E × E → List E × List E × List E × E × E
  | (r0, r1, p, t, w0) =>
    let wK := f.mulE w0 theta
    let wO := if kept then f.mulE wK theta else wK
    let wF := f.mulE wO theta
    let y := yOf f 0 S.s cl.col
    let gmC := genM C x
    let gtC := genT C x
    let gmZ := genM Z (cp Z x)
    let gtZ := genT Z (cp Z x)
    (addPre f r0 (gmC.map fun a => f.scaleE a w0),
      addPre f r1
        (gmZ.map (fun a => f.scaleE a wO) ++ gmZ.map (fun a => f.scaleE a wF) ++
          gtC.map (fun a => f.scaleE a w0) ++
          (if kept then gtC.map (fun a => f.scaleE a wK) else []) ++
          gtZ.map (fun a => f.scaleE a wO) ++ gtZ.map (fun a => f.scaleE a wF) ++
          (if kept then (gmC.drop (C.l - 3)).map (fun a => f.scaleE a wK) else [])),
      (if kept then addPre f p ((gmC.take (C.l - 3)).map fun a => f.scaleE a wK) else p),
      f.addE (f.addE
          (f.addE (f.addE t (f.mulE w0 y.1))
            (if kept then f.mulE wK (cl.kept.getD Fld.zeroE) else Fld.zeroE))
          (f.mulE wO y.2.1))
        (f.mulE wF y.2.2),
      f.mulE wF theta)

/-- The sum of all draws' rows with the coefficients first, first theta, ..; the next power. The
values of `sumDrawsLit`, made faster (if, where there is a kept row, a row has at least three
places: `sumDraws_eq`, Fmt/M2LocEq.lean). -/
def sumDraws (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta first : E)
    (xs : List Nat) (col : Nat → Option KCol) : Option (LRow × E) :=
  (xs.foldl (fun (acc : Option (List E × List E × List E × E × E)) x =>
    match acc, col x with
    | some st, some cl => some (addDrawL f C Z kept S theta x cl st)
    | _, _ => none) (some (List.replicate C.l Fld.zeroE, List.replicate C.l Fld.zeroE, if kept then List.replicate C.l Fld.zeroE else [], Fld.zeroE, first))).map fun st =>
      (⟨twoRows C.l st.1.toArray st.2.1.toArray, st.2.2.1.toArray, st.2.2.2.1⟩, st.2.2.2.2)

/-- row b of a carrying message's table -/
def rowOfG (l b : Nat) (g : Array E) : List E := (List.range l).map fun j => ent g (b + 2 * j)

/-- The sum of all draws' rows (as `sumDrawsLit`), added onto a row that is there already.
Literally. -/
def sumDrawsFromLit (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (start : LRow)
    (first : E) (xs : List Nat) (col : Nat → Option KCol) : Option (LRow × E) :=
  xs.foldl (fun (acc : Option (LRow × E)) x =>
    match acc, col x with
    | some a, some cl =>
      some ((drawL f C Z kept S x cl).foldl
          (fun (s : LRow × E) r => (s.1.add f s.2 r, f.mulE s.2 theta)) a)
    | _, _ => none) (some (start, first))

/-- The same, added onto a row that is there already. The values of `sumDrawsFromLit`, made faster
(under the hypotheses of `sumDrawsFrom_eq`, Fmt/M2LocEq.lean). -/
def sumDrawsFrom (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (start : LRow)
    (first : E) (xs : List Nat) (col : Nat → Option KCol) : Option (LRow × E) :=
  (xs.foldl (fun (acc : Option (List E × List E × List E × E × E)) x =>
    match acc, col x with
    | some st, some cl => some (addDrawL f C Z kept S theta x cl st)
    | _, _ => none) (some (rowOfG C.l 0 start.g, rowOfG C.l 1 start.g, start.p.toList, start.t, first))).map fun st =>
      (⟨twoRows C.l st.1.toArray st.2.1.toArray, st.2.2.1.toArray, st.2.2.2.1⟩, st.2.2.2.2)

/-- The old sample row of a kept message, carried over; Q: its form on the old kept table; y: the
old answer. -/
def oldSample (f : Fld) (C Z : Code) (Q : Array E) (y : E) : LRow :=
  ⟨twoRows C.l #[] (restOf f C.l [((restOff C Z true).OP, overPad C.l Q)]), overP C.l Q, y⟩

/-! ## The honest side, and tests -/

namespace LocT

def rnd (n : Nat) : E :=
  (Fld.two.red (n * 2654435761 + 12345),
    Fld.two.red (n * n * 40503 + 7),
    Fld.two.red (n * 97 + n * n * n))
def rv (s n : Nat) : List E := (List.range n).map fun i => rnd (1000 * s + i)
def rvF (s n : Nat) : List E := (rv s n).map fun e => Fld.ofF e.1

def C : Code := ⟨5, 16, 2⟩
def Z : Code := ⟨5, 2, 1⟩
def gam : E := rnd 5

/-- From here to `Pi`: what the old group's prover holds: two main rows with tails; the kept row
over the base field with its tail; the old and the fresh mask row with tails -/
def M (b : Nat) : List E := rv (10 + b) C.l
def Rh (b : Nat) : List E := rv (20 + b) C.r
def Kp : List E := rvF 30 C.l
def Ka : List E := rvF 31 C.r
def W : List E := rv 40 Z.l
def Sg : List E := rv 41 Z.r
def P : List E := rv 42 Z.l
def Pi : List E := rv 43 Z.r

def Ms : List E := foldRows .two [gam] [M 0, M 1] C.l
def Rs : List E := foldRows .two [gam] [Rh 0, Rh 1] C.r

/-- Adds 1 to entry i if `on`. The number alt, below, says which entry is altered by 1 in what the
switch sends: 0: nothing; 1: the main message; 2: the second sending; 3: the old pad; 4: the kept
row's tail; 5: the old mask's message -/
def bump (on : Bool) (l : List E) (i : Nat) : List E :=
  if on then l.set i (Fld.two.addE (l.getD i Fld.zeroE) Fld.oneE) else l

/-- the carrying message's table (`G`), the second sending's (`P'`) -/
def G (kept : Bool) (alt : Nat) : Array E :=
  let rest := bump (alt == 5) W 0 ++ P ++ Rs ++ (if kept then bump (alt == 4) Ka 1 else []) ++
    Sg ++ Pi ++ (if kept then bump (alt == 3) (Kp.drop (C.l - 3)) 2 else [])
  twoRows C.l (bump (alt == 1) Ms 3).toArray ((fitL Fld.zeroE (C.l - 1) rest) ++ [rnd 77]).toArray
def P' (alt : Nat) : Array E := (bump (alt == 2) (Kp.take (C.l - 3)) 0 ++ rvF 50 3).toArray

/-- the old tree's column at x -/
def colAt (kept : Bool) (x : Nat) : KCol :=
  ⟨⟨#[symE C x (M 0) (Rh 0), symE C x (M 1) (Rh 1)],
      #[symE Z (cp Z x) W Sg],
      #[symE Z (cp Z x) P Pi]⟩,
    if kept then some (symE C x Kp Ka) else none⟩

/-- what a fold would hand on: any forms, with the target that makes the claim true -/
def S (kept : Bool) : KSRow :=
  let c := rv 60 C.l; let d0 := rv 61 Z.l; let d1 := rv 62 Z.l; let kp := if kept then rv 63 C.l else []
  ⟨⟨c.toArray, d0.toArray, d1.toArray,
      Fld.two.addE (dot .two c.toArray Ms.toArray)
        (Fld.two.addE (dot .two kp.toArray Kp.toArray)
          (Fld.two.addE (dot .two d0.toArray W.toArray) (dot .two d1.toArray P.toArray))),
      [gam]⟩,
    kp.toArray⟩

def holds (R : LRow) (kept : Bool) (alt : Nat) : Bool :=
  Fld.two.addE (dot .two R.g (G kept alt)) (dot .two R.p (P' alt)) == R.t

/-- the carried claim; then the rows at the draws -/
def run (kept : Bool) (alt : Nat) (xs : List Nat) : Bool × List (List Bool) :=
  (holds (carried .two C Z kept (S kept)) kept alt,
    xs.map fun x => (drawL .two C Z kept (S kept) x (colAt kept x)).map fun R => holds R kept alt)

def same (a b : Option (LRow × E)) : Bool :=
  match a, b with
  | some x, some y => x.1.g == y.1.g && x.1.p == y.1.p && x.1.t == y.1.t && x.2 == y.2
  | none, none => true
  | _, _ => false

end LocT
open LocT

-- the offsets, at the full parameters' codes: with a kept row, without
#guard restOff ⟨15, 4096, 73⟩ ⟨15, 32, 73⟩ true == ⟨0, 32, 64, 137, 210, 283, 356⟩ && restOff ⟨15, 4096, 73⟩ ⟨15, 32, 73⟩ false == ⟨0, 32, 64, 137, 137, 210, 283⟩
#guard locFits ⟨15, 4096, 73⟩ ⟨15, 32, 73⟩ true && locFits ⟨9, 64, 3⟩ ⟨9, 16, 3⟩ true && !locFits ⟨9, 32, 3⟩ ⟨9, 16, 3⟩ true && locFits LocT.C LocT.Z true
-- four rows a draw with a kept row, three without; sizes
#guard (drawL .two LocT.C LocT.Z true (S true) 3 (LocT.colAt true 3)).length == 4 && (drawL .two LocT.C LocT.Z false (S false) 3 (LocT.colAt false 3)).length == 3
#guard (drawL .two LocT.C LocT.Z true (S true) 3 (LocT.colAt true 3)).all fun R => R.g.size == 32
-- an honest prover: the carried claim and every row hold
#guard run true 0 [0, 3, 17, 31, 3] == (true, List.replicate 5 [true, true, true, true])
#guard run false 0 [0, 3, 17, 31, 3] == (true, List.replicate 5 [true, true, true])
-- One entry altered in what the switch sends: just the rows that read it fail. The main message:
-- the carried claim, the main rows
#guard run true 1 [3, 17] == (false, List.replicate 2 [false, true, true, true])
-- the second sending: the carried claim, the kept row's rows
#guard run true 2 [3, 17] == (false, List.replicate 2 [true, false, true, true])
-- the old pad: likewise
#guard run true 3 [3, 17] == (false, List.replicate 2 [true, false, true, true])
-- the kept row's tail: the kept row's row at every draw, and nothing else
#guard run true 4 [3, 17] == (true, List.replicate 2 [true, false, true, true])
-- the old mask's message: the carried claim, the old mask's rows
#guard run true 5 [3, 17] == (false, List.replicate 2 [true, true, false, true])
-- The fast form gives the literal form's values: every coefficient, the target, the next power; a
-- repeated position; no draw; a position without a column
#guard [true, false].all fun k => [[], [3], [0, 3, 17, 31, 3]].all fun xs =>
  same (sumDraws .two LocT.C LocT.Z k (S k) (rnd 8) (rnd 9) xs fun x => some (LocT.colAt k x)) (sumDrawsLit .two LocT.C LocT.Z k (S k) (rnd 8) (rnd 9) xs fun x => some (LocT.colAt k x))
#guard (sumDraws .two LocT.C LocT.Z true (S true) (rnd 8) (rnd 9) [3, 4] fun x => if x == 4 then none else some (LocT.colAt true x)).isNone && (sumDrawsLit .two LocT.C LocT.Z true (S true) (rnd 8) (rnd 9) [3, 4] fun x => if x == 4 then none else some (LocT.colAt true x)).isNone
-- onto a row that is there: the carried claim as the start: fast and literal the same; the sum
-- holds of the honest tables
#guard [true, false].all fun k => [[], [3], [0, 3, 17, 31, 3]].all fun xs =>
  same (sumDrawsFrom .two LocT.C LocT.Z k (S k) (rnd 8) (carried .two LocT.C LocT.Z k (S k)) (rnd 9) xs fun x => some (LocT.colAt k x)) (sumDrawsFromLit .two LocT.C LocT.Z k (S k) (rnd 8) (carried .two LocT.C LocT.Z k (S k)) (rnd 9) xs fun x => some (LocT.colAt k x))
#guard ((sumDrawsFrom .two LocT.C LocT.Z true (S true) (rnd 8) (carried .two LocT.C LocT.Z true (S true)) (rnd 9) [0, 3, 17] fun x => some (LocT.colAt true x)).map fun r => (holds r.1 true 0, holds r.1 true 4)) == some (true, false)
-- from a start of zeros (every entry 0; the lengths are 2 l = 32 and l = 16): sumDraws
#guard same (sumDrawsFrom .two LocT.C LocT.Z true (S true) (rnd 8) ⟨zerosE 32, zerosE 16, Fld.zeroE⟩ (rnd 9) [3, 17] fun x => some (LocT.colAt true x)) (sumDraws .two LocT.C LocT.Z true (S true) (rnd 8) (rnd 9) [3, 17] fun x => some (LocT.colAt true x))
-- The old sample row, carried over: any form on the old kept table with its true value holds of the
-- second sending and the old pad; it fails if the second sending or the old pad is altered, not if
-- the kept row's tail is
#guard (let Q := (rv 70 LocT.C.l).toArray; let R := oldSample .two LocT.C LocT.Z Q (dot .two Q Kp.toArray); [0, 1, 2, 3, 4, 5].map fun alt => holds R true alt) == [true, true, false, false, true, true]
-- it is the carried claim at that form alone
#guard (let Q := (rv 70 LocT.C.l).toArray; let a := oldSample .two LocT.C LocT.Z Q (rnd 3); let b := carried .two LocT.C LocT.Z true ⟨⟨#[], #[], #[], rnd 3, []⟩, Q⟩; a.g == b.g && a.p == b.p && a.t == b.t)
-- the batched row holds of the honest tables; with the kept row's tail altered it fails
#guard ((sumDraws .two LocT.C LocT.Z true (S true) (rnd 8) (rnd 9) [0, 3, 17, 31, 3] fun x => some (LocT.colAt true x)).map fun r => (holds r.1 true 0, holds r.1 true 4)) == some (true, false)

end Fmt.M2
