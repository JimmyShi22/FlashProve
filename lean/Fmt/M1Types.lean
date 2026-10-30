-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Types.lean: the first toy's verifier: the types of its parameters (the sizes), of what its
decision reads of a transcript and of the linear claims that it carries, and the vector arithmetic
that it uses.

The first toy (a product test) is a protocol in which the prover shows that it knows three rows a,
b, c with a_i b_i = c_i for every i. The programs (the C++ implementation that comes with this Lean
code) write proof files for it. This file and its sister files (named at the end of part 1) give the
verifier's decision as total functions that compute, generic in the sizes. This file has the types
and the shared arithmetic: definitions and tests only. Core Lean, no Mathlib.

The words. The decision, as a Lean function, is `decWith` (Fmt/M1Dec.lean, which takes the blocks as
a further argument): a function of the sizes and of the view; it has the parts (D4) and (D5) of the
paragraph "How the decision is divided" below. The drawn elements of E and positions are the
verifier's challenges. A column, a leaf's column, is the rows' symbols at one position (`cutCol`,
`stageCol`).

Sources. Written from the programs' description of the toy (its sections 0 to 6 and its parts 1 to
4). By its own word that description has one writer throughout and no second reading.
This file's sources include no file made by the programs. Proof files made by the
programs are read and judged by the decision that is built on these definitions: those
tests are gathered in Fmt/M1FullProg.lean (the verdict on each file; nineteen values that the
decision computes on its way, compared with the programs' own list). (Exactly: the values of
`targets`; see Limits in the head of Fmt/M1Targets.lean.)

How the decision is divided (section 5 of that description). It tests five things. (D1) form, (D2)
proof of work and (D3) Merkle openings belong to the reader of a proof file and to the compiled
verifier. These files have (D4), the last block's linear check, and (D5), its checks at the drawn
positions, with all that leads to them. Everything before the last block only moves a claim: it
computes a state that is a function of the plain messages, the drawn elements and the opened
columns.

1. What the file contains.
   `E`: An element of the extension field: three words (Fmt/FieldE.lean).
   `Code`: (a, l, r): length 2^a, message length l, r entries of encoding randomness. It is defined
      in Fmt/M1Codes.lean. The codes' points are those of field 2, and so the toy is over field 2.
   `Stage`: A stage of the proximity test: main code C, mask code Z, k and h (2^k main rows, 2^h
      mask rows), and t, the number of positions drawn at the list that opens this stage's tree.
   `Par`: The sizes: the field; K (the rows a, b, c have 2^K entries); the stages, the last one
      last.
   `RV`: What the decision reads of a round. `sent`: the elements of E in the prover's message, in
      the order sent, answers among them, with roots and nonces left out. `els`: the drawn elements,
      in the order drawn. `poss`: the drawn positions, in the order drawn, repeats kept.
   `View`: The rounds, and the opened columns by (the tree's number in the order of sending,
      position). The general untyped view of a transcript is that of Fmt/View.lean; Fmt/M1Dec.lean
      makes this one from it.
   `Rs`: The rounds that have not been consumed so far. The blocks are pure functions of plain
      arguments (elements, lists, rows). Within the first toy's decision, only the function that
      strings all blocks together (Fmt/M1Dec.lean) takes rounds off this list, one after the other,
      so no block knows a round's number. Others that take rounds off such a list: `targets`
      (Fmt/M1Targets.lean) goes by a copy of that function's steps, and the later toys' files use
      `nextN` likewise (Fmt/M2Dec.lean, Fmt/M3Dec.lean and files beside them).
   `GRow`: A row on a group: c on the main table, d on the mask table, both written out, and the
      target t. It stands for the equation <c, main table> + <d, mask table> = t. A table of 2^b
      rows is one vector: the entry (row r, place p) has the index r + 2^b p.
   `Col`: An opened column, laid on rows: 2^k main symbols (0 at rows that nobody sent; symbols of
      the base field embedded), 2^h symbols of the old mask rows, 2^h of the fresh mask rows.
   `SRow`: What a fold hands on: one claim on three virtual rows, <c, M_0> + <d0, M_1> + <d1, M_2> =
      t, with the fold's challenges g (all k of them; the first h fold the mask columns).
   The arithmetic (all total; beyond an array's end the entry is 0): `ent`, `zerosE`, `addV`,
      `scaleV`, `axpy`, `dot`; `powsE x n`; `eqTab z`; `pv s z` (s times `eqTab z`); `bitsE b r`
      (the low b bits of r as elements 0, 1, so that `pv s (bitsE b r ++ z)` is "row r alone, eqTab
      z on the places"); `eqAt z j`; `foldLow g T`; `foldV g v`;
      `sumRows x rows`; `next`, `nextN`, `colAt`; `cutCol mF mE nz` (a leaf's column: mF main
      symbols over the base field, mE main symbols over E, then nz mask symbols over E);
      `stageCol st mF mE` (the same, laid on the stage's rows).
   Products in E go by `mulEF` of Fmt/FieldEFast.lean (each coordinate reduced once). It is proved
      equal to `mulE` at all words, so no value depends on the choice. The theorem is `mulEF_eq`, in
      that file. `eqAt`, and `sumRows` on the targets and the powers of x, multiply by `mulE`
      itself.
   Why the arithmetic is written on lists under the arrays (padL, addL, dotL, powsL, eqStep, fold1A,
      fold1L), with every recursion in tail position or taken from the core library. The evaluator's
      stack does not hold 16,384 nested calls (tested below: that the functions tried in part 2 run
      at the lengths named there, most at 40,000 entries). For Lean's kernel an array is a list, and
      reading it entry by entry by the index costs the square of its length (measured: an operation
      on 128 entries takes seconds by the index and tenths of a second on lists).
   The sister files, all in this folder: M1Codes (points, a codeword's symbol, generator rows);
      M1Send (the sample row, the first sending); M1Psc (the zero-check and the sum-check); M1Fold
      (a fold, the last block); M1Cs (the code switch); M1Dec (all blocks strung together).

2. What is checked when the file compiles (#guard). On long vectors: the operations run at 40,000
entries (those tried: `addV`, `scaleV`, `powsE`, `dot`, `foldLow`, `sumRows`; `fold1` at 40,001;
`eqTab` at 32,768), so in these no recursion nests as deep as a vector is long (`takeE`, on a leaf's
column, does nest as deep as the number of elements that it takes, and is not tried on long lists);
the shorter of two vectors counts as filled with 0, on either side. On small numbers over field 2:
`eqTab`, `pv`, `powsE`, `foldLow`, `sumRows`, `cutCol` and `stageCol` at values written out by hand;
`eqAt` against `eqTab`; a fold is the inner product with `eqTab`, place by place.

3. Theorems. None.

4. What is not claimed.
   It is not claimed here that these functions are what the programs compute. They are a reading
      of the programs' description; the tests named under "Sources" compare verdicts and values on
      the programs' own files.
   No statement on soundness follows from this file.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Codes
import Fmt.FieldEFast

namespace Fmt.M1

abbrev E : Type := Ext3

structure Stage where
  C : Code
  Z : Code
  k : Nat
  h : Nat
  t : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The sizes. -/
structure Par where
  fld    : Fld
  K      : Nat
  stages : List Stage
  /-- bits of work on each draw of positions; bytes of a leaf's salt (the decision reads neither) -/
  work   : Nat := 20
  salt   : Nat := 40

/-- what the decision reads of a round -/
structure RV where
  sent : List E := []
  els  : List E := []
  poss : List Nat := []
  deriving Inhabited

structure View where
  rounds : List RV
  opened : List (Nat × Nat × List UInt64)

abbrev Rs : Type := List RV

/-- A row on a group. -/
structure GRow where
  c : Array E
  d : Array E
  t : E
  deriving Inhabited

/-- An opened column, laid on rows. -/
structure Col where
  main  : Array E
  mask  : Array E
  fresh : Array E
  deriving Inhabited

/-- What a fold hands on. -/
structure SRow where
  c  : Array E
  d0 : Array E
  d1 : Array E
  t  : E
  g  : List E
  deriving Inhabited

/-! ## Vector arithmetic; reading rounds and columns -/

def ent (v : Array E) (i : Nat) : E := v.getD i Fld.zeroE
def zerosE (n : Nat) : Array E := Array.replicate n Fld.zeroE

/-- a list filled up with 0 to n entries -/
def padL (n : Nat) (u : List E) : List E := u ++ List.replicate (n - u.length) Fld.zeroE

/-- entry by entry, on lists; the longer length; beyond the shorter one's end its entry is 0 -/
def addL (f : Fld) (u v : List E) : List E :=
  List.zipWith f.addE (padL v.length u) (padL u.length v)

/-- entry by entry; the longer length -/
def addV (f : Fld) (u v : Array E) : Array E := (addL f u.toList v.toList).toArray
def scaleV (f : Fld) (s : E) (v : Array E) : Array E := (v.toList.map (f.mulEF s)).toArray
/-- u + s v -/
def axpy (f : Fld) (u : Array E) (s : E) (v : Array E) : Array E := addV f u (scaleV f s v)
def dotL (f : Fld) : List E → List E → E → E
  | a :: u, b :: v, acc => dotL f u v (f.addE acc (f.mulEF a b))
  | _, _, acc => acc
def dot (f : Fld) (u v : Array E) : E := dotL f u.toList v.toList Fld.zeroE

/-- acc reversed, then c, c x, .., c x^(n-1); `powsE` starts it at c = 1 and an empty acc: 1, x, ..,
x^(n-1) -/
def powsL (f : Fld) (x : E) : Nat → E → List E → List E
  | 0, _, acc => acc.reverse
  | n + 1, c, acc => powsL f x n (f.mulEF c x) (c :: acc)
def powsE (f : Fld) (x : E) (n : Nat) : Array E := (powsL f x n Fld.oneE []).toArray

/-- one more variable on top: the old table times 1 - z, then the old table times z -/
def eqStep (f : Fld) (T : List E) (z : E) : List E :=
  T.map (f.mulEF (f.subE Fld.oneE z)) ++ T.map (f.mulEF z)

/-- The table of the multilinear equality polynomial at z. At the index j with bits j_0 (lowest),
j_1, ..: the product over t of z_t if j_t = 1, else 1 - z_t. -/
def eqTab (f : Fld) (z : List E) : Array E := (z.foldl (eqStep f) [Fld.oneE]).toArray

/-- one entry of eqTab -/
def eqAt (f : Fld) (z : List E) (j : Nat) : E :=
  ((z.foldl
    (fun (s : E × Nat) x => (f.mulE s.1 (if s.2 % 2 = 1 then x else f.subE Fld.oneE x), s.2 / 2))
    (Fld.oneE, j))).1

def pv (f : Fld) (s : E) (z : List E) : Array E := (z.foldl (eqStep f) [s]).toArray

/-- the low b bits of r, lowest first, as elements 0, 1 -/
def bitsE (b r : Nat) : List E :=
  (List.range b).map fun t => if r.testBit t then Fld.oneE else Fld.zeroE

/-- one variable: new entry i = (1 - g) T[2 i] + g T[2 i + 1] -/
def fold1A (f : Fld) (g : E) : List E → List E → List E
  | a :: b :: T, acc => fold1A f g T (f.addE a (f.mulEF g (f.subE b a)) :: acc)
  | [a], acc => (f.addE a (f.mulEF g (f.subE Fld.zeroE a)) :: acc).reverse
  | [], acc => acc.reverse
def fold1L (f : Fld) (g : E) (T : List E) : List E := fold1A f g T []
def fold1 (f : Fld) (g : E) (T : Array E) : Array E := (fold1L f g T.toList).toArray

/-- A table of 2^|g| rows folded at g: entry p is the sum over the rows b of
eq(g, b) T[b + 2^|g| p]. -/
def foldLow (f : Fld) (g : List E) (T : Array E) : Array E :=
  (g.foldl (fun T x => fold1L f x T) T.toList).toArray

/-- a vector of 2^|g| entries folded to one element -/
def foldV (f : Fld) (g : List E) (v : Array E) : E := ent (foldLow f g v) 0

/-- The sum of the rows with the coefficients 1, x, x^2, .. -/
def sumRows (f : Fld) (x : E) (rows : List GRow) : GRow :=
  (rows.foldl
    (fun (s : GRow × E) R =>
      (⟨axpy f s.1.c s.2 R.c, axpy f s.1.d s.2 R.d, f.addE s.1.t (f.mulE s.2 R.t)⟩, f.mulE s.2 x))
    (⟨#[], #[], Fld.zeroE⟩, Fld.oneE)).1

/-- the next round -/
def next : Rs → Option (RV × Rs)
  | [] => none
  | v :: rs => some (v, rs)

/-- the next round, which sends ns elements, draws ne elements and np positions: refused if the
numbers differ -/
def nextN (ns ne np : Nat) (rs : Rs) : Option (RV × Rs) :=
  match rs with
  | [] => none
  | v :: rs' =>
    if v.sent.length == ns && v.els.length == ne && v.poss.length == np then some (v, rs') else none

/-- the opened column at (tree, position) -/
def colAt (V : View) (tree x : Nat) : Option (List UInt64) :=
  (V.opened.find? fun o => o.1 == tree && o.2.1 == x).map (·.2.2)

/-- n elements of E off a list of words -/
def takeE : Nat → List UInt64 → Option (List E × List UInt64)
  | 0, w => some ([], w)
  | n + 1, a :: b :: c :: w => (takeE n w).map fun x => ((a, b, c) :: x.1, x.2)
  | _ + 1, _ => none

/-- A leaf's column: mF main symbols over the base field, mE main symbols over E, then nz mask
symbols over E; nothing behind them. The result: (the main symbols, the mask symbols). -/
def cutCol (mF mE nz : Nat) (w : List UInt64) : Option (List E × List E) :=
  if w.length == mF + 3 * mE + 3 * nz then
    match takeE mE (w.drop mF) with
    | none => none
    | some (me, w') => (takeE nz w').map fun x => ((w.take mF).map Fld.ofF ++ me, x.1)
  else none

/-- A column of a stage's tree, laid on rows: mF + mE main rows were sent (the others of the 2^k are
0); behind them 2^h old mask symbols, then 2^h fresh ones. -/
def stageCol (st : Stage) (mF mE : Nat) (w : List UInt64) : Option Col :=
  (cutCol mF mE (2 * 2 ^ st.h) w).map fun x =>
    ⟨Array.ofFn (n := 2 ^ st.k) fun i => x.1.getD i.val Fld.zeroE,
      (x.2.take (2 ^ st.h)).toArray,
      (x.2.drop (2 ^ st.h)).toArray⟩

/-! ## Tests: long vectors: no recursion may nest as deep as a vector is long -/

#guard (addV .two (zerosE 40000) (zerosE 3)).size == 40000
#guard (scaleV .two (2, 0, 0) (zerosE 40000)).size == 40000
#guard (fold1 .two (2, 0, 0) (zerosE 40001)).size == 20001
#guard (powsE .two (2, 0, 0) 40000).size == 40000
#guard dot .two (zerosE 40000) (zerosE 40000) == (0, 0, 0)
#guard (eqTab .two (List.replicate 15 (3, 1, 0))).size == 32768
#guard (foldLow .two [(1, 0, 0), (0, 0, 0)] (zerosE 40000)).size == 10000
#guard (sumRows .two (2, 0, 0) [⟨zerosE 40000, zerosE 5, (1, 0, 0)⟩, ⟨zerosE 40000, zerosE 7, (1, 0, 0)⟩]).c.size == 40000
-- the shorter vector counts as filled with 0, on either side
#guard addV .two #[(1, 0, 0)] #[(2, 0, 0), (3, 0, 0)] == #[(3, 0, 0), (3, 0, 0)] && addV .two #[(2, 0, 0), (3, 0, 0)] #[(1, 0, 0)] == #[(3, 0, 0), (3, 0, 0)]
#guard fold1 .two (2, 0, 0) #[(5, 0, 0), (7, 0, 0), (1, 0, 0)] == #[(9, 0, 0), (18446744069414584320, 0, 0)]

/-! ## Tests (field 2; small numbers) -/

#guard eqTab .two [] == #[(1, 0, 0)]
#guard eqTab .two [(0, 0, 0), (1, 0, 0)] == #[(0, 0, 0), (0, 0, 0), (1, 0, 0), (0, 0, 0)]
#guard eqTab .two [(3, 0, 0)] == #[(18446744069414584319, 0, 0), (3, 0, 0)]
#guard pv .two (5, 0, 0) (bitsE 2 2 ++ [(0, 0, 0)]) == #[(0, 0, 0), (0, 0, 0), (5, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)]
#guard powsE .two (2, 0, 0) 4 == #[(1, 0, 0), (2, 0, 0), (4, 0, 0), (8, 0, 0)]
#guard foldLow .two [(0, 0, 0)] #[(7, 0, 0), (9, 0, 0), (1, 0, 0), (2, 0, 0)] == #[(7, 0, 0), (1, 0, 0)]
#guard foldLow .two [(1, 0, 0)] #[(7, 0, 0), (9, 0, 0), (1, 0, 0), (2, 0, 0)] == #[(9, 0, 0), (2, 0, 0)]
-- a fold is the inner product with eq, place by place
#guard foldLow .two [(3, 1, 0), (5, 0, 2)] #[(7, 0, 0), (9, 0, 0), (1, 0, 0), (2, 0, 0)] == #[dot .two (eqTab .two [(3, 1, 0), (5, 0, 2)]) #[(7, 0, 0), (9, 0, 0), (1, 0, 0), (2, 0, 0)]]
#guard (sumRows .two (2, 0, 0) [⟨#[(1, 0, 0)], #[], (1, 0, 0)⟩, ⟨#[(1, 0, 0), (1, 0, 0)], #[(3, 0, 0)], (1, 0, 0)⟩]).c == #[(3, 0, 0), (2, 0, 0)]
#guard (sumRows .two (2, 0, 0) [⟨#[(1, 0, 0)], #[], (1, 0, 0)⟩, ⟨#[(1, 0, 0), (1, 0, 0)], #[(3, 0, 0)], (1, 0, 0)⟩]).t == (3, 0, 0)
#guard cutCol 3 0 2 [1, 2, 3, 4, 5, 6, 7, 8, 9] == some ([(1, 0, 0), (2, 0, 0), (3, 0, 0)], [(4, 5, 6), (7, 8, 9)])
#guard cutCol 3 0 2 [1, 2, 3, 4, 5, 6, 7, 8] == none
#guard (List.range 4).map (eqAt .two [(3, 1, 0), (5, 0, 2)]) == (eqTab .two [(3, 1, 0), (5, 0, 2)]).toList
#guard ((stageCol ⟨⟨3, 2, 1⟩, ⟨3, 2, 1⟩, 2, 0, 1⟩ 3 0 [1, 2, 3, 4, 5, 6, 7, 8, 9]).map fun c => (c.main, c.mask, c.fresh)) == some (#[(1, 0, 0), (2, 0, 0), (3, 0, 0), (0, 0, 0)], #[(4, 5, 6)], #[(7, 8, 9)])

end Fmt.M1
