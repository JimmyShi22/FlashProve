-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/RequestItem.lean: what two items in the statement of a proof file's first chain must be, as
functions of the public files and the caller's request, and tests that compare. Definitions, and two
theorems without hypotheses. (A chain is the non-interactive form of one protocol.)
In the programs the item "request" (R14.3 of docs/format/FORMAT.md) is not the bytes of the request
file. It is 177 words of 32 bits, which each program forms for itself from the parameter file, the
scale file and the request file (12.3, R15.1 to R15.7): most of them numbers of the parameter file's
lines; five digests that are computed by the format page's second hash function (R15.3), and four
digests that are copied from lines. The item "the request file's words" is, in the programs, the
request file itself, byte for byte.
In the library both are free fields, `ProofStm.request` and `ProofStm.words` (a `ProofStm` is what a
proof's chains are given from outside). The second hash function is an argument k, with values in a
monad m. No text of any hash is in this file.
Defines: `requestItemW`: the item "request" from the three files, or nothing; it computes the five
digests by k, then `requestItemOf`, which calls no hash, decides. `Declared.requestItemW`: that at
the public files of a `Declared` (the library's description of what is public) and the caller's
request (the field `request` of a `UserStm`). `UserStm.requestBytes`: the request file's bytes.
`ProofStm.wordsOk`, `ProofStm.requestOkW`: the tests on the field `words` and on both fields.
States:
(1) `ProofStm.wordsOk_iff` (0 hypotheses): the test `wordsOk` is passed exactly if the field `words`
    is the request file's bytes.
(2) `ProofStm.requestOk_iff` (0 hypotheses; k any plain function, at which the names lose their W):
    the test `requestOk` is passed exactly if `Declared.requestItem` has a value, the field
    `request` is that value, and the field `words` is the request file's bytes.
Under: no hypothesis; none on k.
Does not show:
(1) The order of the parameter file's lines is not tested here, nor any condition on the numbers
    except these: each is below 2^32 (R15.2); the line "prof" is 20 and the line "NE" is not 0
    (12.3); the request has 2^lt + 2 words (R15.6).
(2) The four digests that are copied from lines are not computed here.
(3) Whether the parameter file is admitted at all is decided elsewhere.
(4) lt is not bounded: at a parameter file whose line "lt" is large the test on the request's length
    computes 2^lt.
(5) The tests of 12.2 on the request's words (r < e <= T; tokens below V) are not here.
(6) A name whose number enters the item must be the name of exactly one line. Not every byte of such
    a line enters the item: of a line "name number" the first piece behind the name is read, and
    whatever is behind it is not ("theta 256 999" gives what "theta 256" gives; so with the line
    "version"). The line "table" alone must have exactly six numbers. Empty lines are dropped.
(7) A line whose name gives no word does not enter the item at all.
(8) Which file is which is given by its place in `Declared.files` alone: the function cannot tell a
    layout file from a scale file. With the second and the third file in each other's places nothing
    is refused for it, unless the file that is then third is not made of at least eight whole words:
    the item then holds that file's tree digest.
(9) The forms of a parameter file outside 12.3 (prof other than 20; NE 0; without the 32 lines of
    the four tables' digests) have no item here. The C++ verifier forms a statement for some of them
    and accepts under none (12.3).
(10) Nothing is asked of k: that its values have 32 bytes is not assumed. Whatever k returns, a
    value of the item has 708 bytes (the last test), and the two trees' digests in it have 32 bytes
    each (`olderLevelsW`); the three digests under 73 have 96 bytes together, and singly any
    lengths.
(11) That `Declared`'s other fields are what follows from the same files is not compared here.
(12) The functions without a W are the ones with a W at m := Id, by definition. That at another
    lawful monad `requestItemW` on (fun n w => pure (f n w)) is pure (requestItem f ...) is not
    proved.
Notes in full, with every limit at length and the text's source, stand at the end of this file.

-/
import Fmt.Parsed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-! ## What stands around the second hash function -/

/-- The words of a text (R15.4): its bytes, filled up with zero bytes to a whole word. -/
def textWords (t : ByteArray) : ByteArray := t ++ zeroBytes ((4 - t.size % 4) % 4)

section
variable {m : Type → Type} [Monad m] (k : Nat → ByteArray → m ByteArray)

/-- One level of the tree hash: the digests under num of the pieces of 128 words, one after the
other. The last piece can be shorter. The pieces are hashed in their order. -/
def olderLevelW (num : Nat) (w : ByteArray) : m ByteArray :=
  Nat.fold ((w.size + 511) / 512)
    (fun i _ acc => do
      let a ← acc
      let d ← k num (w.extract (512 * i) (512 * (i + 1)))
      pure (a ++ d))
    (pure ByteArray.empty)

/-- Levels of the tree hash until 32 bytes are left: the first level under num, the later ones
under 11. The first argument bounds the number of levels; the result is none if it runs out. -/
def olderLevelsW : Nat → Nat → ByteArray → m (Option ByteArray)
  | 0, _, _ => pure none
  | j + 1, num, w => do
    let d ← olderLevelW k num w
    if d.size == 32 then pure (some d) else olderLevelsW j 11 d

/-- TK(w) of R15.3: the tree hash of a list of at least eight words. The first level is hashed
under the number 10, the others under 11. So every list is hashed at least once, and the number
tells a piece of the list from a piece of digests. If every value of k has 32 bytes, a level has a
sixteenth of the bytes of the level before, rounded up to a whole digest, so sixteen levels are
enough for every list of fewer than 2^64 bytes. The result is nothing, and k is not called, if w is
not made of whole words or has fewer than eight. -/
def olderTKW (w : ByteArray) : m (Option ByteArray) :=
  if w.size % 4 != 0 || w.size < 32 then pure none else olderLevelsW k 16 10 w

end

/-! ## The parameter file's lines -/

/-- The pieces of l between the bytes c: one more than the number of times that c occurs. Joining
them with single bytes c gives l back. The list is walked from its end, so that the depth of the
calls does not grow with its length. -/
def splitAt (c : UInt8) (l : List UInt8) : List (List UInt8) :=
  l.reverse.foldl
    (fun acc x =>
      if x == c then [] :: acc
      else
        match acc with
        | [] => [[x]]
        | p :: ps => (x :: p) :: ps)
    [[]]

/-- The lines of a parameter file that are not empty, each cut at its blanks. The first piece of a
line is its name. -/
structure ReqLines where
  lines : List (List (List UInt8))

/-- Cuts a parameter file into lines and pieces. -/
def ReqLines.read (file : ByteArray) : ReqLines :=
  ⟨((splitAt 0x0A file.toList).filter fun l => !l.isEmpty).map (splitAt 0x20)⟩

/-- The lines of one name. -/
def ReqLines.named (L : ReqLines) (name : String) : List (List (List UInt8)) :=
  L.lines.filter fun l => l.head? == some name.toUTF8.toList

/-- The pieces after the name in the one line of that name. Returns nothing if no line or more than
one line has the name. -/
def ReqLines.values (L : ReqLines) (name : String) : Option (List (List UInt8)) :=
  match L.named name with
  | [l] => some (l.drop 1)
  | _ => none

/-- The number that decimal digits spell. Nothing for an empty value, one of more than 15
characters, one with a leading zero, or one with a character that is no digit. The bound of 15 is
that of the C++ reader of the file's first 32 lines (read_parameters in blocks/frame/parameters.h).
-/
def lineNumber (w : List UInt8) : Option Nat :=
  if w.isEmpty || decide (15 < w.length) || (w.head? == some 0x30 && decide (1 < w.length)) ||
      w.any (fun c => c < 0x30 || 0x39 < c) then none
  else some (w.foldl (fun x c => 10 * x + (c.toNat - 0x30)) 0)

/-- A decimal numeral below 2^32, without a sign and without a leading zero. -/
def number32 (w : List UInt8) : Option Nat := (lineNumber w).filter fun x => decide (x < 2 ^ 32)

/-- The first number of the one line of that name. -/
def ReqLines.value (L : ReqLines) (name : String) : Option Nat :=
  ((L.values name).bind (·.head?)).bind number32

/-- The numbers of the lines that "names" lists, as words. In "names" single
blanks separate the names. -/
def ReqLines.words (L : ReqLines) (names : String) : Option ByteArray :=
  ((names.splitOn " ").mapM L.value).map fun l => cat (l.map (lowBytes 4))

/-- The eight words of the lines name0 to name7. -/
def ReqLines.eight (L : ReqLines) (name : String) : Option ByteArray :=
  ((List.range 8).mapM fun i => L.value (name ++ toString i)).map fun l =>
    cat (l.map (lowBytes 4))

/-- The text of all lines of one name, each whole, with its name and a line feed. A line was cut
at every blank, so joining its pieces with single blanks gives the line's own bytes back. A last
line that has no line feed in the file gets one here. -/
def ReqLines.text (L : ReqLines) (name : String) : ByteArray :=
  ⟨((L.named name).flatMap fun l => [0x20].intercalate l ++ [0x0A]).toArray⟩

/-- The six lines that are taken in place of the lines "callH" if a file has none (R15.6). -/
def callHIfNone : String :=
  "callH R16a R16 NF NFH HD0\ncallH R16b R16 HD1\ncallH R8 R8 ROW HD2\n" ++
  "callH FEa FE HE0\ncallH FEb FE HE1\ncallH FC FC CNF\n"

/-- The digest of the lines of one name (R15.6): one call of k, under 73. "ifNone" is the text that
is taken if the file has no such line; without one the result is then nothing, and k is not called.
-/
def ReqLines.callsW {m : Type → Type} [Monad m] (k : Nat → ByteArray → m ByteArray) (L : ReqLines)
    (name : String) (ifNone : Option String := none) : m (Option ByteArray) :=
  let t := L.text name
  if !t.isEmpty then do pure (some (← k 73 (textWords t)))
  else
    match ifNone with
    | none => pure none
    | some s => do pure (some (← k 73 (textWords s.toUTF8)))

/-! ## The item -/

/-- The names of the words 2 to 28. -/
def names2 : String :=
  "prof lt L ll d H G dh f fe NE V eps1_lo eps1_hi eps2_lo eps2_hi cs theta0_lo theta0_hi " ++
  "hq hv ho hgD huD hdD hr ut"

/-- The names of the words 37 to 70. -/
def names37 : String :=
  "la nmin D tau lmaf NAf lmad NAd lmar lmb lmq lmx wb_qk wb_v wb_o wb_g wb_u wb_gs wb_us " ++
  "wb_gr wb_ur wb_dn wb_dnr wb_r iota_0 iota_1 iota_2 iota_3 iota_4 iota_5 iota_6 iota_7 " ++
  "seed_lo seed_hi"

/-- The names of the words 103 to 113. -/
def names103 : String := "lB S rx kFM kFD lmS NAs lmh lmo lmbA iotaA_0"

/-- The names of the words 130 to 154. -/
def names130 : String :=
  "MF KF epsF_lo epsF_hi toksrc lmhf NHf lmhd lmhr lmbH wb_emb wb_head iotaH_0 iotaH_1 iotaH_2 " ++
  "iotaH_3 iotaH_4 iotaH_5 C theta cap s sh sT F"

/-- The last five words: B of the line "sec"; then of the line "table b n i m e w": w, b, n, m. -/
def ReqLines.lastWords (L : ReqLines) : Option ByteArray :=
  match L.value "sec", (L.values "table").bind fun v => v.mapM number32 with
  | some sec, some [b, n, _, m, _, w] => some (cat ([sec, w, b, n, m].map (lowBytes 4)))
  | _, _ => none

/-- The value of the item "request" from the parameter file's lines, the number of the request
file's bytes and the five digests that are computed (R15.1, R15.5): of the lines "call", of the
scale file, of the lines "callA", of the lines "callH", of the request file. A digest that is
nothing makes the result nothing. The word of the next token is 0 (R15.7). Returns nothing if a line
is missing or misspelled, or if a file does not have the form that 12.3 covers, or if the result has
not 708 bytes. No hash is called. lt is not bounded here. -/
def requestItemOf (L : ReqLines) (requestSize : Nat)
    (call scale callA callH request : Option ByteArray) : Option ByteArray := do
  let version ← (L.values "version").bind (·.head?)
  let prof ← L.value "prof"
  let ne ← L.value "NE"
  let lt ← L.value "lt"
  if version.length != 4 || prof != 20 || ne == 0 || requestSize != 4 * (2 ^ lt + 2) then none
  let w := cat [
    lowBytes 4 0x4D363100, ⟨version.toArray⟩, ← L.words names2, ← call,
    ← L.words names37,
    ← L.eight "tsilu", ← L.eight "tsig", ← L.eight "trope", ← scale,
    ← L.words names103, ← L.eight "texp", ← callA, ← L.words names130,
    ← callH, ← request, lowBytes 4 0, ← L.lastWords]
  if w.size == 708 then some w else none

section
variable {m : Type → Type} [Monad m] (k : Nat → ByteArray → m ByteArray)

/-- The value of the item "request": 177 words, 708 bytes (R15.1, R15.5). The five digests are
computed first, in the item's order, whatever the lines say; then `requestItemOf` decides. Call it
on an admitted parameter file: lt is not bounded here. -/
def requestItemW (parameterFile scaleFile requestFile : ByteArray) : m (Option ByteArray) := do
  let L := ReqLines.read parameterFile
  let call ← L.callsW k "call"
  let scale ← olderTKW k scaleFile
  let callA ← L.callsW k "callA"
  let callH ← L.callsW k "callH" (some callHIfNone)
  let request ← olderTKW k requestFile
  pure (requestItemOf L requestFile.size call scale callA callH request)

/-! ## At the declared structure -/

/-- The request file's bytes, from its words (12.2; by the head of section 12 a word has four bytes,
the lowest first). -/
def UserStm.requestBytes (u : UserStm) : ByteArray :=
  cat (u.request.map fun x => lowBytes 4 x.toNat)

/-- What a proof's chains are told as the item "the request file's words" is the caller's request
file, byte for byte. No hash is called, and the public files are not read. It asks nothing of the
request's length, of its two positions or of its tokens. -/
def ProofStm.wordsOk (u : UserStm) (x : ProofStm) : Bool := decide (x.words = u.requestBytes)

/-- The test is passed exactly if the field is the request file's bytes. -/
theorem ProofStm.wordsOk_iff (u : UserStm) (x : ProofStm) :
    x.wordsOk u = true ↔ x.words = u.requestBytes := decide_eq_true_iff

/-- The value of the item "request" from the declared structure's public files and the caller's
request. The public files must be three: the parameter file, the layout file, the scale file, in
this order (R4.9). Of any other number of files the result is nothing, and k is not called. The
layout file is not read. -/
def Declared.requestItemW (D : Declared) (u : UserStm) : m (Option ByteArray) :=
  match D.files with
  | [parameterFile, _, scaleFile] => Fmt.requestItemW k parameterFile scaleFile u.requestBytes
  | _ => pure none

/-- What a proof's chains are told as the item "request" is what the public files and the caller's
request give, and what they are told as the item "the request file's words" is the caller's request
file (`ProofStm.wordsOk`). False where the files and the request give nothing. -/
def ProofStm.requestOkW (D : Declared) (u : UserStm) (x : ProofStm) : m Bool := do
  pure (decide ((← D.requestItemW k u) = some x.request) && x.wordsOk u)

end

/-! ## At a hash that is a plain function -/

section
variable (k : Nat → ByteArray → ByteArray)

/-- `olderTKW` at a plain function. -/
def olderTK (w : ByteArray) : Option ByteArray := Id.run (olderTKW (m := Id) k w)

/-- `ReqLines.callsW` at a plain function. -/
def ReqLines.calls (L : ReqLines) (name : String) (ifNone : Option String := none) :
    Option ByteArray := Id.run (L.callsW (m := Id) k name ifNone)

/-- `requestItemW` at a plain function. -/
def requestItem (parameterFile scaleFile requestFile : ByteArray) : Option ByteArray :=
  Id.run (requestItemW (m := Id) k parameterFile scaleFile requestFile)

/-- `Declared.requestItemW` at a plain function. -/
def Declared.requestItem (D : Declared) (u : UserStm) : Option ByteArray :=
  Id.run (D.requestItemW (m := Id) k u)

/-- `ProofStm.requestOkW` at a plain function. -/
def ProofStm.requestOk (D : Declared) (u : UserStm) (x : ProofStm) : Bool :=
  Id.run (x.requestOkW (m := Id) k D u)

/-- The test is passed exactly if the function has a value, the field `request` is that value, and
the field `words` is the request file's bytes. -/
theorem ProofStm.requestOk_iff (D : Declared) (u : UserStm) (x : ProofStm) :
    x.requestOk k D u = true ↔ D.requestItem k u = some x.request ∧ x.words = u.requestBytes := by
  show (decide (D.requestItem k u = some x.request) && x.wordsOk u) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_iff, ProofStm.wordsOk_iff]

end

end Fmt

#print axioms Fmt.ProofStm.wordsOk_iff
#print axioms Fmt.ProofStm.requestOk_iff

/-
Notes in full (other files' comments call these notes "the head of" this file).

Fmt/RequestItem.lean: the value of the item "request" in the statement of a proof file's first
chain, as a function of the public files and the caller's request, with the second hash function as
an argument; and the value of the item "the request file's words". It stands on Decl/Declared.lean
and Fmt/Parsed.lean. Of these it uses the types
`Declared`,
`UserStm`,
`ProofStm` and, through the imports of Fmt/Parsed.lean, `lowBytes`.

The first chain of a proof file binds the item "request" as one string of bytes (R14.3). In the
programs these are not the bytes of the request file. They are 177 words of 32 bits, which each
program forms for itself from three files: the parameter file, the scale file and the request file
(docs/format/FORMAT.md, 12.3, R15.1 to R15.7). Most words are numbers of the parameter file's lines.
Five groups of eight words are digests that are computed, by the format page's second hash function
on lists of 32-bit words (R15.3). Four more groups ("tsilu", "tsig", "trope", "texp") are digests
that are copied from the parameter file's lines.
`ProofStm.request` (Decl/Declared.lean) is a free field. This file has the function that says what
it must be, and a test that compares the two.
Behind it the chain binds the item "the request file's words" (R14.3): in the programs the request
file itself, byte for byte. `ProofStm.words` is a free field too. What it must be needs no hash:
`UserStm.requestBytes`. The test on it stands apart (`ProofStm.wordsOk`) and inside the test on
both.

In this file a list of 32-bit words is kept as its bytes, four to a word, the lowest byte first.

Where the text comes from. It is the port's: OnBytes/Proof/RequestItem.lean (all of it),
OnBytes/Hash/SecondHashFunction.lean (secondHashFunctionTreeLevel, secondHashFunctionTreeLevels, secondHashFunctionTree, textWords: what stands around the hash,
and nothing of the hash) and OnBytes/Params/File.lean (number). It differs from
the port's in five things.
 (a) The second hash function K(num; w) of R15.3 is an argument k, with values in a monad m, as the
     format's own hash is in Fmt/'s functions whose names end in W. No hash's text is in this file.
 (b) So the five digests are computed first, in the item's order (`requestItemW`), and the rest is a
     function without a hash that takes them as arguments (`requestItemOf`): the port's do-block,
     with an argument wherever the port calls the hash.
 (c) The port's word32 is `lowBytes 4` (Fmt/Rules8Own.lean) and is not written again.
 (d) The port's allOf (all values of a list of options, or nothing) on a mapped list is `List.mapM`
     in Option, as Fmt/Parsed.lean writes it, and is not written again.
 (e) Names: ParamLines is `ReqLines`, number is `lineNumber`; with (a) and (b): calls is `callsW`,
     the tree is `olderLevelW`, `olderLevelsW`, `olderTKW`, requestItem is `requestItemOf` and
     `requestItemW`, the bound letter k of secondHashFunctionTreeLevels is j, and the port's ifNone.map is a match.
That the port's function is this one at the port's hash is a theorem of a module under OnBytes/,
where both can be imported (requestItem_eq).

1. What the file contains.
   The tree over the second hash function: `olderLevelW`, `olderLevelsW`, `olderTKW` (TK of R15.3);
   `textWords` (R15.4). The parameter file's lines: `splitAt`, `ReqLines` with read, named, values,
     value, words, eight, text, lastWords, callsW; `lineNumber`, `number32`, `callHIfNone`.
   The item: `names2`, `names37`, `names103`, `names130`, `requestItemOf`, `requestItemW`.
   At the declared structure: `UserStm.requestBytes`, `ProofStm.wordsOk`, `Declared.requestItemW`,
   `ProofStm.requestOkW`. At a hash that is a plain function, without the W: `olderTK`,
   `ReqLines.calls`, `requestItem`,
     `Declared.requestItem`, `ProofStm.requestOk`.

2. What is checked when the file compiles. The two proofs. Tests that need no hash:
   Fmt/TestRequestItem.lean. Tests of these functions at the second hash function itself are not in
   this library (OnBytes/Proof/TestRequestItem.lean tests the port's functions, not these).

3. Theorems. Two: `ProofStm.wordsOk_iff`, `ProofStm.requestOk_iff`.

4. What is not claimed.
   The order of the parameter file's lines is not tested here, nor any condition on the numbers
   except these: each is below 2^32 (R15.2); the line "prof" is 20 and the line "NE" is not 0
   (12.3); the request has 2^lt + 2 words (R15.6). The four digests that are copied from lines are
   not computed here: the C++ verifier computes each of them itself and ends its run if the line
   differs (R15.6). Whether the parameter file is admitted at all is decided elsewhere. lt is not
   bounded: at a parameter file whose line "lt" is large the test on the request's length computes
   2^lt. The tests of 12.2 on the request's words (r < e <= T; tokens below V) are not here. One
   thing is tested so that two readers of one file cannot take different numbers: a name whose
   number enters the item must be the name of exactly one line.
   NOT EVERY BYTE OF SUCH A LINE ENTERS THE ITEM: of a line "name number" the first piece behind the
   name is read, and whatever stands behind it is not ("theta 256 999" gives what "theta 256" gives;
   so with the line "version"). The line "table" alone must have exactly six numbers. Empty lines
   are dropped. The C++ verifier refuses a third piece on a line from prof to F where it scans the
   file (cp_verify.cpp, polScan). A line whose name gives no word does not enter the item at all.
   WHICH FILE IS WHICH is told by its place in `Declared.files` alone: the function cannot tell a
   layout file from a scale file. With the second and the third file in each other's places nothing
   is refused for it, unless the file that then stands third is not made of at least eight whole
   words: the item then holds that file's tree digest.
   The forms of a parameter file outside 12.3 (prof other than 20; NE 0; without the 32 lines of the
   four tables' digests) have no item here. The C++ verifier forms a statement for some of them and
   accepts under none (12.3).
   Nothing is asked of k: that its values have 32 bytes is not assumed. Whatever k returns, a value
   of the item has 708 bytes (the last test), and the two trees' digests in it have 32 bytes each
   (`olderLevelsW`); the three digests under 73 have 96 bytes together, and singly any lengths.
   That `Declared`'s other fields are what follows from the same files is not compared here.
   The functions without a W are the ones with a W at m := Id, by definition.
   That at another lawful monad
   `requestItemW` on (fun n w => pure (f n w)) is pure (requestItem f ...) is not proved.
-/
