-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadRunK.lean: the public numbers and the lookup tables of the output head's sub-proof,
the verifier's beside the library's, at the parameter files of two examples that ship with the
prover.

All but one theorem is a run. A line "#guard" is evaluated when this file is compiled, by Lean's
interpreter, and the compilation fails if the value is not true. It is no theorem, and it says
nothing of other numbers.

The two sides. The verifier's side is what publicOf (OnBytes/Model/VerifyPublic.lean) returns on the
bytes of an example's parameter file and scale file: the head's shape (hS), the head's layout (HLy),
and what the head reads of the layers' layout (borderOf). The files' contents are those written out
in Johnson/Road/FormsKeysRunK.lean. The library's side is Inst/Model/Head/Index.lean, the tables of
Inst/Model/Tables.lean and the reference parameters ppref, each definition evaluated as it stands.
The library's head is written at one size: 1,024 positions, width 5,120, 202,048 tokens.

What is compared (checksH; each line has a name):
 1. the sizes: positions, width, vocabulary, ledger bytes; the final normalisation's three numbers
    against ppref.nf, and the library's test NormPar.OK on them; seventeen numbers of the shape
    against numerals written here,
 2. the first features of the five tensors of hf against fNw, fRn, fD1, fD2, fEx at 0; the
    vocabulary needs no filler entry (JV = V); the first entry of HE1 against shift,
 3. rows, columns, features and filled features of hf, hd, hr, of the matrix of the lookup's counts
    and of the borrowed matrix of the stream against n1, n2, nFeat, perCol; the feature of every
    limb of every channel of the stream against fX,
 4. for each of the nine families: it is a segment of the call that the library names; its length
    against len; the column of EVERY entry against pos,
 5. for each of the six calls: its families; the logarithm of its number of keys against size; its
    columns against cols; for EVERY column whether a segment takes it, against "below used"; the
    rows of its table and its padding key against the rows and pad of the families' tables
    (Head.tableOf); its trees' numbers of padding keys against "none but in the last tree, and
    padPos there",
 6. the numbers of trees, and the nine numbers of padding keys in the order of the trees.

The tables (runHT), at both examples. For each family: the number of rows u at which the word of its
call's table, as a number, is not (Head.tableOf s).row u, with the library's definition evaluated.
For the table of exponentials the library's rows are evaluated below 4,096 only: the library's
recurrence is evaluated anew for each row, and a long one overflows the evaluator's stack. All its
65,536 rows are compared with u + 2^16 e(u), e = 2^24, 2, 1, 1, …, the values that the library's
comment names. The theorem isLut_FE of Johnson/Road/HeadTabs.lean has all rows. Also: what the six
calls' records hold (the written table, the logarithm of the rows, the padding row), as the theorems
of that file ask it, and that the layers' layout has the array tauFCw.

What comes out.
 - At the full-size example every line holds but one. The matrix of the lookup's counts has 384
   columns for the verifier, 64 for each of six calls, and n2 .b = 576 in the library, 64 for each
   of nine trees. In the library n2 .b and placeB are used in Index.lean alone.
 - At the small example the library has no head: the lines that compare a size fail, and they are
   listed (smallFails). What holds there: no filler entry; 120 ledger bytes; NormPar.OK; the digit
   forms; each family in its call; the calls' families, tables' rows and padding keys; the columns
   of five families (HD1, HD2, HE0, HE1, CNF), where the library's pos begins as the identity.

Controls. With the first features of two tensors of the layout exchanged, the two lines on them fail
(runCH).

Also here: the two shapes written by hand (shapeHF, shapeHS), compared field by field with what the
verifier reads from the files, so that a theorem can speak of a term.

Theorem: normOK_F (the library's NormPar.OK at 44, 30, 53,687).

What is not claimed. The strides of a tensor's limbs are no part of the layout and are not
compared here. Head.tableOf gives the family HD0 the table of 2^16 consecutive numbers, as the
verifier's call does; the relations of Cm/TargetPHead.lean and Policy/Rel/LedgerHead.lean give it
the multiples of 2^23: padding key and number of rows are the same. In the library call, size,
cols, pos, used, padPos and shift are used in Index.lean alone: these seven describe the calls,
and no theorem on a protocol stands on them; 51 of the 107 lines are set against them. Nothing is
said of other parameter files, of a proof or of soundness. The program does not import this file.

Where the guards stand. The comparison of the tables (runHT) is run by no guard of this library; all
other comparisons are guards here.
-/
import Johnson.Road.FormsKeysRunK
import Johnson.Road.HeadTabs
import Johnson.Road.HeadLines
import Inst.Model.FF.ScalesDef

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Seg CallD Call)
open OnBytes.Model.Verify (publicOf borderOf Public)
open Inst.Model

/-! ## The shapes, by hand -/

/-- The six lines of calls of both examples' parameter files. -/
def linesH : List (List String) :=
  [["R16a", "R16", "NF", "NFH", "HD0"], ["R16b", "R16", "HD1"], ["R8", "R8", "ROW", "HD2"],
   ["FEa", "FE", "HE0"], ["FEb", "FE", "HE1"], ["FC", "FC", "CNF"]]

/-- The head's shape at the full-size example, written by hand from the lines of its parameter
file. -/
def shapeHF : Model.Head.Shape :=
  { lt := 10, la := 16, d := 5120, lPd := 13, V := 202048, MF := 44, KF := 30, epsF := 53687,
    toksrc := 1, wbEmb := 21, wbHead := 13, clipC := 256, theta := 256, cap := 0, logS := 15,
    digSh := 8, tabS := 4, famF := 24, lmhf := 16, NHf := 4, lmhd := 14, lmhr := 13, lmbH := 15,
    iotaH := [1, 1, 1, 0, 0, 0], nmin := 20, NMINH := 27, LIDB := 28, XL := 5,
    polCallsH := linesH }

/-- The head's shape at the small example, written by hand from the lines of its parameter file. -/
def shapeHS : Model.Head.Shape :=
  { lt := 6, la := 8, d := 512, lPd := 9, V := 512, MF := 44, KF := 30, epsF := 1,
    toksrc := 1, wbEmb := 21, wbHead := 13, clipC := 256, theta := 256, cap := 0, logS := 16,
    digSh := 8, tabS := 4, famF := 24, lmhf := 14, NHf := 1, lmhd := 12, lmhr := 12, lmbH := 13,
    iotaH := [0, 0, 0, 0, 0, 0], nmin := 20, NMINH := 0, LIDB := 24, XL := 5,
    polCallsH := linesH }

/-- All fields of a head's shape, for a comparison. -/
def fieldsH (h : Model.Head.Shape) : List ℕ × List ℕ × List (List String) :=
  ([h.lt, h.la, h.d, h.lPd, h.V, h.MF, h.KF, h.epsF, h.toksrc, h.wbEmb, h.wbHead, h.clipC, h.theta,
    h.cap, h.logS, h.digSh, h.tabS, h.famF, h.lmhf, h.NHf, h.lmhd, h.lmhr, h.lmbH, h.nmin, h.NMINH,
    h.LIDB, h.XL], h.iotaH, h.polCallsH)

/-! ## What is evaluated -/

/-- The verifier's segment for a family, looked for in the call that the library names. The library
counts the calls from 1. -/
def segH (L : Model.Head.HL) (s : Head.Fam) : Option Seg :=
  (L.calls[Head.call s - 1]?).bind fun c => c.seg? (nameH s)

/-- The comparisons of sizes, first features and matrices: points 1 to 3 of the head comment. -/
def sizeChecksH (X : Public) : List (String × Bool) :=
  let h := X.hS
  let L := X.HLy
  let b := borderOf X.y
  [("positions", 2 ^ h.lt == Head.nT), ("width", h.d == Head.nD), ("vocabulary", h.V == Head.nV),
   ("ledger bytes", Model.ledNRH h.XL == Head.nB),
   ("norm is ppref's", (h.MF, h.KF, (h.epsF : ℤ)) == (ppref.nf.M, ppref.nf.K, ppref.nf.eps)),
   ("NormPar.OK", decide (npOf h).OK),
   ("seventeen numerals",
     [h.lt, h.la, h.d, h.lPd, h.V, h.XL, h.digSh, h.tabS, h.famF, h.lmhf, h.NHf, h.lmhd, h.lmhr,
       h.lmbH, h.MF, h.KF, h.epsF] ==
     [10, 16, 5120, 13, 202048, 5, 8, 4, 24, 16, 4, 14, 13, 15, 44, 30, 53687]),
   ("digit forms", [h.XL, h.digSh, h.tabS, h.famF] == [5, 8, 4, 24]),
   ("first feature aw", L.oAw == Head.fNw 0 0), ("first feature ra", L.oRa == Head.fRn 0 0),
   ("first feature d1", L.oD1 == Head.fD1 0 0), ("first feature d2", L.oD2 == Head.fD2 0),
   ("first feature ex", L.oE == Head.fEx 0 0),
   ("no filler entry", L.JV == h.V), ("first entry of HE1", L.JVa == Head.shift .HE1),
   ("hf features", L.feat == Head.nFeat .hf),
   ("hf filled", L.filled == Head.perCol .hf * Head.n2 .hf),
   ("hf rows", L.m == Head.n1 .hf), ("hf columns", h.NHf * L.k == Head.n2 .hf),
   ("hd features", 2 * h.d == Head.nFeat .hd),
   ("hd filled", L.fillD == Head.perCol .hd * Head.n2 .hd),
   ("hd rows", L.mD == Head.n1 .hd), ("hd columns", L.kD == Head.n2 .hd),
   ("hr features", Model.ledNRH h.XL == Head.nFeat .hr),
   ("hr filled", L.fillR == Head.perCol .hr * Head.n2 .hr),
   ("hr rows", L.mR == Head.n1 .hr), ("hr columns", L.kR == Head.n2 .hr),
   ("counts rows", 2 ^ h.lmbH == Head.n1 .b), ("counts columns", L.kb == Head.n2 .b),
   ("stream features", b.nl * b.J == Head.nFeat .x),
   ("stream rows", b.mxb == Head.n1 .x), ("stream columns", b.kxb == Head.n2 .x),
   ("stream cells", (Array.range h.XL).all fun l => (Array.range h.d).all fun j =>
      b.cell l j == Head.fX l j)]

/-- The comparisons for one family: point 4. -/
def famChecksH (L : Model.Head.HL) (s : Head.Fam) : List (String × Bool) :=
  match segH L s with
  | none => [(nameH s ++ " in its call", false)]
  | some g =>
    [(nameH s ++ " in its call", true), (nameH s ++ " length", g.n == Head.len s),
     (nameH s ++ " columns", g.pos == (Array.range g.n).map (Head.pos s))]

/-- The comparisons for call c, counted from 1: point 5. -/
def callChecksH (h : Model.Head.Shape) (L : Model.Head.HL) (c : ℕ) : List (String × Bool) :=
  let cd := L.calls.getD (c - 1) default
  let k := L.cl.getD (c - 1) {}
  let fams := famsH.filter fun s => Head.call s == c
  let i := L.fs.iota.getD (c - 1) 0
  let base := L.fs.first.getD (c - 1) 0
  let nm := "call " ++ toString c ++ " "
  [(nm ++ "families", cd.segs.length == fams.length &&
      fams.all fun s => (cd.segs.map (·.name)).contains (nameH s)),
   (nm ++ "keys", cd.lJ + h.lt == Head.size c && k.n == Head.size c),
   (nm ++ "columns", cd.J == Head.cols c && cd.used.size == cd.J),
   (nm ++ "taken columns",
      cd.used.map (· != 0) == (Array.range cd.J).map fun j => decide (j < Head.used c)),
   (nm ++ "rows", fams.all fun s => 2 ^ k.k == (Head.tableOf s).rows),
   (nm ++ "padding key", fams.all fun s => ((k.tauAt k.t0).toNat : ℤ) == (Head.tableOf s).pad),
   (nm ++ "padding places", (List.range (2 ^ i)).map (fun t => L.fs.pub.getD (base + t) 0) ==
      List.replicate (2 ^ i - 1) 0 ++ [Head.padPos c])]

/-- The comparisons on the trees: point 6. The library has a tree of 2^17 columns in words alone, so
that number stands here as a numeral. -/
def treeChecksH (h : Model.Head.Shape) (L : Model.Head.HL) : List (String × Bool) :=
  [("six calls", L.calls.size == 6 && L.cl.size == 6),
   ("columns of a tree", L.fs.dT - h.lt == 17),
   ("trees of a call", L.fs.iota.toList == (List.range 6).map fun q => Head.size (q + 1) - 27),
   ("nine trees", L.fs.NT == 9),
   ("padding places of the nine", L.fs.pub.toList ==
      [0, Head.padPos 1, 0, Head.padPos 2, 0, Head.padPos 3, Head.padPos 4, Head.padPos 5,
        Head.padPos 6])]

/-- All comparisons. -/
def checksH (X : Public) : List (String × Bool) :=
  sizeChecksH X ++ famsH.flatMap (famChecksH X.HLy) ++
    (List.range 6).flatMap (fun q => callChecksH X.hS X.HLy (q + 1)) ++ treeChecksH X.hS X.HLy

/-- The run at an example's files. pol, KL: the parameter file and the scale file; h: a shape
written by hand. Returns whether the shape that the verifier reads is h, the number of comparisons,
the number of columns of the matrix of counts, and the names of the comparisons that fail. Refuses
where the verifier refuses. -/
def runH (pol KL : ByteArray) (h : Model.Head.Shape) :
    Except String (Bool × ℕ × ℕ × List String) := do
  let X ← publicOf pol KL none
  let r := checksH X
  pure (fieldsH X.hS == fieldsH h, r.length, X.HLy.kb, (r.filter (!·.2)).map (·.1))

/-- A control at an example's files: the names of the comparisons of sizes that fail if the first
features of the tensors d1 and d2 are exchanged in the layout. -/
def runCH (pol KL : ByteArray) : Except String (List String) := do
  let X ← publicOf pol KL none
  let L := X.HLy
  pure (((sizeChecksH { X with HLy := { L with oD1 := L.oD2, oD2 := L.oD1 } }).filter
    (!·.2)).map (·.1))

/-- The comparisons that fail at the small example. -/
def smallFails : List String :=
  ["positions", "width", "vocabulary", "norm is ppref's", "seventeen numerals",
   "first feature ra", "first feature d1", "first feature d2", "first feature ex",
   "first entry of HE1", "hf features", "hf filled", "hf rows", "hf columns", "hd features",
   "hd filled", "hd rows", "hd columns", "hr filled", "hr rows", "hr columns", "counts rows",
   "counts columns", "stream features", "stream rows", "stream columns", "stream cells",
   "NF length", "NF columns", "NFH length", "NFH columns", "HD0 length", "HD0 columns",
   "HD1 length", "ROW columns", "HD2 length", "HE0 length", "HE1 length", "CNF length",
   "call 1 keys", "call 1 columns", "call 1 taken columns", "call 1 padding places",
   "call 2 keys", "call 2 columns", "call 2 taken columns", "call 2 padding places",
   "call 3 keys", "call 3 columns", "call 3 taken columns", "call 3 padding places",
   "call 4 keys", "call 4 columns", "call 4 taken columns", "call 4 padding places",
   "call 5 keys", "call 5 columns", "call 5 taken columns", "call 5 padding places",
   "call 6 keys", "call 6 columns", "call 6 taken columns", "call 6 padding places",
   "columns of a tree", "trees of a call", "nine trees", "padding places of the nine"]

/-- The library's conditions on a normalisation hold at the full-size example's three numbers. -/
theorem normOK_F : (npOf shapeHF).OK := by
  unfold NormPar.OK npOf shapeHF
  norm_num

/-! ## The tables -/

/-- The number of rows u below n at which the word of the call, as a number, is not f u. -/
def differHT (k : Call) (n : ℕ) (f : ℕ → ℤ) : ℕ :=
  ((Array.range n).filter fun u => ((k.tauAt u).toNat : ℤ) != f u).size

/-- The values of the exponentials' table that the library's comment names. -/
def stepHT (u : ℕ) : ℤ := u + 2 ^ 16 * (if u = 0 then 2 ^ 24 else if u = 1 then 2 else 1)

/-- For each family: its name, the logarithm of the rows of its call's table, and the number of rows
at which the call's table differs from the family's table in the library; for a family of the table
of exponentials the rows below 4,096 alone. -/
def rowsHT (X : Public) : List (String × ℕ × ℕ) :=
  famsH.map fun s =>
    let k := X.HLy.cl.getD (Head.call s - 1) {}
    let n := if s == .HE0 || s == .HE1 then 4096 else (Head.tableOf s).rows
    (nameH s, k.k, differHT k n (Head.tableOf s).row)

/-- What the records of the six calls hold, as the four theorems isLut_… ask it: for each call
whether it has no written table, the array tauFCw or the table of exponentials at 24, 8, 4; the
logarithm of its rows; its padding row. Before them: whether the layers' layout has the array
tauFCw. -/
def recordsHT (X : Public) : Bool × List (String × ℕ × ℕ) :=
  (X.y.tauFC == tauFCw,
   (List.range 6).map fun q =>
    let k := X.HLy.cl.getD q {}
    (if k.tau.isNone then "none" else if k.tau == some tauFCw then "FC"
      else if k.tau == some (Model.Head.tauFEOf 24 8 4) then "FE" else "other", k.k, k.t0))

/-- The run at an example's files: rowsHT; the numbers of rows, of all 65,536, at which the tables
of the calls 4 and 5 differ from stepHT; recordsHT. Refuses where the verifier refuses. -/
def runHT (pol KL : ByteArray) : Except String
    (List (String × ℕ × ℕ) × (ℕ × ℕ) × Bool × List (String × ℕ × ℕ)) := do
  let X ← publicOf pol KL none
  pure (rowsHT X,
    (differHT (X.HLy.cl.getD 3 {}) 65536 stepHT, differHT (X.HLy.cl.getD 4 {}) 65536 stepHT),
    recordsHT X)

/-- What the run gives at both examples. -/
def foundHT : List (String × ℕ × ℕ) × (ℕ × ℕ) × Bool × List (String × ℕ × ℕ) :=
  ([("NF", 16, 0), ("NFH", 16, 0), ("HD0", 16, 0), ("HD1", 16, 0), ("ROW", 8, 0), ("HD2", 8, 0),
    ("HE0", 16, 0), ("HE1", 16, 0), ("CNF", 16, 0)], (0, 0), true,
   [("none", 16, 0), ("none", 16, 0), ("none", 8, 0), ("FE", 16, 0), ("FE", 16, 0),
    ("FC", 16, 32768)])

/-! ## The run -/

/- the full-size example: 107 comparisons, one fails -/
#guard (match runH (textK linesKF) (wordsK scalesKF) shapeHF with
  | .ok r => r == (true, 107, 384, ["counts columns"])
  | .error _ => false)

/- the small example -/
#guard (match runH (textK linesKS) (wordsK scalesKS) shapeHS with
  | .ok r => r == (true, 107, 1536, smallFails)
  | .error _ => false)

/- a control: two first features exchanged -/
#guard (match runCH (textK linesKF) (wordsK scalesKF) with
  | .ok r => r == ["first feature d1", "first feature d2", "counts columns"]
  | .error _ => false)

#print axioms normOK_F

end OnBytes.Road.Hd
