-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/ToyShapes.lean: the shapes of the toy whose key, entry and proof files the C++ tools
make for other verifiers, read off its two public files.

The toy's first public file is a parameter file. Its second says what the files of a real model say:
how many links a request has, how many rows on the table it leaves (linear claims on the committed
matrix, for the test on the table), how many rows the matrix has, and the links' identifiers:
   links 3
   pending 2
   matrix 100
   identifiers 1 2 3
A link is as in the small run "links" (OnBytes/Plan/ToyRuns.lean); the last link has one plain
scalar. With these shapes the seven chains of the toy's files follow from the two public files.

How the second file is read. The C++ routines read the four words and the first three numbers with
the C library's formatted scan, and this file follows that routine: the four words must be there as
they are; where the form has a blank or a line feed, there may be any white space, or none; a number
may have a sign and leading zeros, one of 2^64 or more counts as 2^64 - 1, and of each number the
low 32 bits are kept. The identifiers are read by a C++ stream, as long as numbers follow;
numbersFrom says how that ends.

There are two toys of this kind. The tool that makes a key and an entry
(blocks/frame/handover_files.cpp) reads the second file as said here. The tool that makes proofs
(blocks/frame/handover_proof.cpp) has links that also make claims on the table, and takes three more
words after the identifiers. In the names of this file "seam" marks the second toy, after the C++
header.

Main definitions: toyRanges, readToyModel, toyShapes, seamShapes, toyConfigure, toyForProofs,
toyForCommitters.
C++ counterpart: toy_shapes() in blocks/frame/tests/toy_shapes.h (toyShapes) and in
blocks/frame/tests/seam_world.h (seamShapes); toy_ranges() in blocks/frame/tests/toy_file.h.

Not claimed here: no theorem is stated.
-/
import OnBytes.Plan.ToyRuns
import OnBytes.Plan.ReqFrame
import OnBytes.Params.Configure

namespace OnBytes.Plan

open OnBytes.Params

/-- What the key's proof of the ranges looks up in a toy's matrix of so many rows, an even number.
Row i and row i + rows / 2 are an entry; every cell is a byte of three bits; the first fifth of the
entries are weights of two digits. -/
def toyRanges (matrixRows : Nat) : Shape where
  kCol := 0
  matrixRows := matrixRows
  lookups := [
    { lookup := { d := 3, mu := 0, live := 0, digitWeight := [1], offset := 4, paddingKey := 3,
                  parts := [], firstBound := [1, 0] }
      entries := [⟨0, 0, matrixRows / 2, matrixRows / 2⟩]
      logRowsApart := 1 },
    { lookup := { d := 5, mu := 0, live := 0, digitWeight := [1, 8], offset := 16,
                  paddingKey := 17, parts := [], firstBound := [] }
      entries := [⟨0, 0, matrixRows / 10, matrixRows / 2⟩] }]

/-- What follows a word at the head of a list; nothing if the list does not begin with the word. -/
def behindWord (word : String) (l : List UInt8) : Option (List UInt8) :=
  let w := word.toUTF8.toList
  if l.take w.length == w then some (l.drop w.length) else none

/-- A word, white space or none, and a number that is kept as a word of 32 bits. Returns the number
and what follows it, white space skipped. -/
def wordAndNumber (word : String) (l : List UInt8) : Option (Nat × List UInt8) := do
  let rest ← behindWord word l
  let x ← scanNumber (rest.dropWhile isSpace)
  pure (x.1 % 2 ^ 32, x.2.dropWhile isSpace)

/-- The numbers at the head of a list, each after white space or none, as long as numbers below
2^64 follow, and what comes after them. The reading ends as that of a C++ stream ends: what it has
taken in before it fails is gone. So a sign without a digit after it is passed over, and so are
the sign and all digits of a number of 2^64 or more, which is not kept. most: a bound on how many
numbers are read. -/
def numbersFrom (most : Nat) (text : List UInt8) : List Nat × List UInt8 :=
  loop most text []
where
  /-- done: the numbers so far, the last one first. -/
  loop : Nat → List UInt8 → List Nat → List Nat × List UInt8
    | 0, l, done => (done.reverse, l)
    | fuel + 1, l, done =>
      let rest := l.dropWhile isSpace
      let minus := rest.head? == some 45
      let body := if minus || rest.head? == some 43 then rest.drop 1 else rest
      let d := digits body 0 0
      if d.2.1 == 0 then (done.reverse, body)
      else if 2 ^ 64 ≤ d.1 then (done.reverse, d.2.2)
      else loop fuel d.2.2 ((if minus then (2 ^ 64 - d.1) % 2 ^ 64 else d.1) :: done)

/-- The toy's second public file: links, pending rows, rows of the matrix, the identifiers, and what
comes after them. -/
def readToyModel (file : ByteArray) : Option (Nat × Nat × Nat × List Nat × List UInt8) := do
  let a ← wordAndNumber "links" file.toList
  let b ← wordAndNumber "pending" a.2
  let c ← wordAndNumber "matrix" b.2
  let rest ← behindWord "identifiers" c.2
  pure (a.1, b.1, c.1, numbersFrom rest.length rest)

/-- The made-up range checks of a toy: its links check no range, and an empty list is refused. -/
def toyChecks (links : Nat) : List RangeCheck :=
  List.replicate links ⟨2 ^ 6, 2 ^ 8, 128, 41, 2 ^ 17, (10, 8)⟩

/-- The links of a toy's request: those of the small run "links", the last with one plain
scalar. -/
def toyRequest (links answers : Nat) : List ReqLink :=
  ((List.range links).zip (toyLinks links answers)).map fun x =>
    { x.2 with plain := if x.1 + 1 == links then 1 else 0 }

/-- The shapes of the toy whose key and entry files are made. l and rest: what the first file's
lines say, and what comes after them, which must be nothing. What comes after the identifiers is not
read. Nothing if the second file is not in its form, or has more than 9 links or an odd number of
rows. The links make no claims on the table. In their place the prover sends, after the links, one
scalar for each pending row, as a stand-in for that row's target. -/
def toyShapes (l : Lines) (rest model : ByteArray) : Option Shapes := do
  if !rest.isEmpty then none
  let (links, pending, matrix, identifiers, _) ← readToyModel model
  if 9 < links || matrix % 2 != 0 then none
  let vars := l.link.logL - 1
  pure
    { sub :=
        { links := toyRequest links l.answers
          openRows := List.replicate links 3
          plan := fun _ _ => productRounds vars
          pendingRows := pending
          afterLinks := planScalars pending
          matrixRows := matrix }
      layout := ⟨List.replicate links []⟩
      identifiers := identifiers
      ranges := toyRanges matrix
      rangeChecks := toyChecks links }

/-- The words of a text: the stretches of bytes between white space. -/
def wordsOf (l : List UInt8) : List (List UInt8) :=
  (l.foldr (fun x (acc : List UInt8 × List (List UInt8)) =>
    if isSpace x then ([], if acc.1.isEmpty then acc.2 else acc.1 :: acc.2)
    else (x :: acc.1, acc.2)) ([], [])) |> fun a => if a.1.isEmpty then a.2 else a.1 :: a.2

/-- The claims on the table that each link of the toy with proofs makes. -/
def seamClaims : Nat := 2

/-- The arrays that the layout names for link number l of the toy with proofs, if the second file
has the word "arrays": b as one block, c as two, its lower and its upper half. The toy's sub-proofs
do not go through arrays: the layout only says, among the chain's parameter bytes, where the vectors
lie. -/
def seamArrays (vars l : Nat) : List ReqArray :=
  let half := vars / 2
  [⟨"b", 0, 2 ^ half, 2 ^ (vars - half),
     [⟨0, 0, if l == 0 then 1 else 0, 0, half, vars - half, 0, vars, true⟩]⟩,
   ⟨"c", 1, 2 ^ half, 2 ^ (vars - half),
     [⟨0, 0, 0, 0, half - 1, vars - half, 0, vars - 1, false⟩,
      ⟨2 ^ (half - 1), 0, 0, 2 ^ (vars - 1), half - 1, vars - half, 0, vars - 1, false⟩]⟩]

/-- The shapes of the toy whose proof files are made. Each link leaves one row on the table, and
makes two claims on the table, which it joins after its own sumcheck. After the identifiers there
may be any of three words, each at most once. "arrays": the links' vectors are named in the layout
(seamArrays). "class": the second link (the only one, if there is one) has one oracle message more
in its first prover's message, in a class of leaves, and so in a tree, of its own. "later": that
link has one oracle message more at a later moment, between its own sumcheck and its claims on the
table. Of the two further oracle messages nothing is claimed: only their samples' rows are in the
link's group. -/
def seamShapes (l : Lines) (rest model : ByteArray) : Option Shapes := do
  if !rest.isEmpty then none
  let (links, pending, matrix, identifiers, behind) ← readToyModel model
  if 9 < links || pending != links || matrix % 2 != 0 then none
  let words := wordsOf behind
  let known := ["arrays", "class", "later"].map (·.toUTF8.toList)
  if !(words.all known.contains) || !Lkp.allPairs (· != ·) words then none
  let has := fun (w : String) => words.contains w.toUTF8.toList
  let vars := l.link.logL - 1
  let special := if 1 < links then 1 else 0
  let further : List ReqMessage :=
    (if has "class" then [⟨{ mainRows := 1 }, 1, 0, 0⟩] else []) ++
    (if has "later" then [⟨{ mainRows := 1 }, 0, 1, 0⟩] else [])
  let request := ((List.range links).zip (toyRequest links l.answers)).map fun x =>
    if x.1 == special then { x.2 with messages := x.2.messages ++ further } else x.2
  pure
    { sub :=
        { links := fillLinks (withAnswers l.answers request)
          openRows := List.replicate links (3 + 1)
          plan := fun link moment => do
            if moment == 0 then productRounds vars
            if moment == (if has "later" && link == special then 1 else 0) then
              planScalars seamClaims
              planBatSigma seamClaims
              planPsc { degree := List.replicate l.blockLog 3, degreeY := 1, values := 1 }
          pendingRows := pending
          matrixRows := matrix }
      layout := ⟨(List.range links).map fun i => if has "arrays" then seamArrays vars i else []⟩
      identifiers := identifiers
      ranges := toyRanges matrix
      rangeChecks := toyChecks links }

/-- All that the chains of a toy's files bind and walk, from its two public files. shapes: toyShapes
or seamShapes. bits: what the caller asks of every round; a round holds with its proof of work
counted. Whatever the reader of the parameter file refuses is refused under the one name
notAdmitted. -/
def toyConfigure (shapes : Lines → ByteArray → ByteArray → Option Shapes)
    (parameters model : ByteArray) (bits : Nat := 128) : Except String Configured := do
  let x ← (readLines parameters).mapError fun _ => notAdmitted
  let s ← orRefuse (shapes x.1 x.2 model)
  configure x.1 s (configurationDigest [parameters, model]) bits

/-- For a toy's proof files: only the tool that makes proofs has them, so its shapes are meant. -/
def toyForProofs (parameters model : ByteArray) (bits : Nat := 128) : Except String Configured :=
  toyConfigure seamShapes parameters model bits

/-- For a toy's key and entry files. The two tools read one pair of public files as different
requests, but the chains of a key and of an entry depend on neither reading: they follow from the
parameter file, the rows of the matrix and the digest of the two files. So whichever reading admits
the files serves: first that of the tool that makes proofs, then the other. Of the result only the
four chains of key and entry are meant to be read. -/
def toyForCommitters (parameters model : ByteArray) (bits : Nat := 128) :
    Except String Configured :=
  match toyConfigure seamShapes parameters model bits with
  | .ok c => .ok c
  | .error _ => toyConfigure toyShapes parameters model bits

end OnBytes.Plan
