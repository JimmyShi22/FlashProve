-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/RequestItem.lean: the value of the statement's item `request` in a model's proof.

The first chain of a proof file binds the request in two items of its statement: `request`, one
string of bytes, and `the request file's words`, the caller's request itself
(`Params.First.statement`, OnBytes/Params/Chains.lean). This file forms the first. For a model's
proof its bytes are not those of the request's file. They are 177 words of 32 bits, which the
verifier forms for itself from three files: the parameter file, the scale file and the request's
file (docs/format/FORMAT.md, 12.3, R15.x). Most words are numbers of the parameter file's lines.
Five groups of eight words are digests that are computed here, by the second hash function on lists
of 32-bit words (R15.3; OnBytes/Hash/SecondHashFunction.lean). Four more groups (`tsilu`, `tsig`, `trope`,
`texp`) are digests of public tables of the model's functions; they are copied from the parameter
file's lines.
C++: verifier/src/cp_verify.cpp, polSkeleton and polScan (the lines' words), runStage (digests).
In this file a list of 32-bit words is kept as its bytes, four to a word, the lowest byte first.

Main definitions: `ParamLines`, `requestItem`.

What is not claimed. The order of the parameter file's lines is not tested here, nor any condition
on the numbers except these: each is below 2^32 (R15.2); the line `prof` is 20 and the line `NE` is
not 0 (12.3); the request's file has 2^lt + 2 words (R15.6). The four digests that are copied
from lines are not computed here: the C++ verifier computes each of them itself and ends its run if
the line differs (R15.6). Whether the file is admitted at all is decided by the code that reads it
for the model. One thing is tested so that two readers of one file cannot take different numbers: a
name whose number enters the item must be the name of exactly one line.
-/
import OnBytes.Params.File
import OnBytes.Hash.SecondHashFunction

namespace OnBytes.Proof

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
structure ParamLines where
  lines : List (List (List UInt8))

/-- Cuts a parameter file into lines and pieces. -/
def ParamLines.read (file : ByteArray) : ParamLines :=
  ⟨((splitAt 0x0A file.toList).filter fun l => !l.isEmpty).map (splitAt 0x20)⟩

/-- The lines of one name. -/
def ParamLines.named (L : ParamLines) (name : String) : List (List (List UInt8)) :=
  L.lines.filter fun l => l.head? == some name.toUTF8.toList

/-- The pieces after the name in the one line of that name. Returns nothing if no line or more than
one line has the name. -/
def ParamLines.values (L : ParamLines) (name : String) : Option (List (List UInt8)) :=
  match L.named name with
  | [l] => some (l.drop 1)
  | _ => none

/-- A decimal numeral below 2^32, without a sign and without a leading zero. -/
def number32 (w : List UInt8) : Option Nat := (Params.number w).filter fun x => decide (x < 2 ^ 32)

/-- The first number of the one line of that name. -/
def ParamLines.value (L : ParamLines) (name : String) : Option Nat :=
  ((L.values name).bind (·.head?)).bind number32

/-- The numbers of the lines that `names` lists, as words. In `names` single blanks separate the
names. -/
def ParamLines.words (L : ParamLines) (names : String) : Option ByteArray :=
  (Params.allOf ((names.splitOn " ").map L.value)).map fun l => Fmt.cat (l.map word32)

/-- The eight words of the lines name0 to name7. -/
def ParamLines.eight (L : ParamLines) (name : String) : Option ByteArray :=
  (Params.allOf ((List.range 8).map fun i => L.value (name ++ toString i))).map fun l =>
    Fmt.cat (l.map word32)

/-- The text of all lines of one name, each whole, with its name and a line feed. A line was cut
at every blank, so joining its pieces with single blanks gives the line's own bytes back. A last
line that has no line feed in the file gets one here. -/
def ParamLines.text (L : ParamLines) (name : String) : ByteArray :=
  ⟨((L.named name).flatMap fun l => [0x20].intercalate l ++ [0x0A]).toArray⟩

/-- The six lines that are taken in place of the lines `callH` if a file has none (R15.6). -/
def callHIfNone : String :=
  "callH R16a R16 NF NFH HD0\ncallH R16b R16 HD1\ncallH R8 R8 ROW HD2\n" ++
  "callH FEa FE HE0\ncallH FEb FE HE1\ncallH FC FC CNF\n"

/-- The digest of the lines of one name (R15.6). `ifNone` is the text that is taken if the file
has no such line; without one the result is then nothing. -/
def ParamLines.calls (L : ParamLines) (name : String) (ifNone : Option String := none) :
    Option ByteArray :=
  let t := L.text name
  if !t.isEmpty then some (secondHashFunction 73 (textWords t))
  else ifNone.map fun s => secondHashFunction 73 (textWords s.toUTF8)

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

/-- The last five words: B of the line `sec`; then of the line `table b n i m e w`: w, b, n, m. -/
def ParamLines.lastWords (L : ParamLines) : Option ByteArray :=
  match L.value "sec", (L.values "table").bind fun v => Params.allOf (v.map number32) with
  | some sec, some [b, n, _, m, _, w] => some (Fmt.cat ([sec, w, b, n, m].map word32))
  | _, _ => none

/-- The value of the item `request`: 177 words, 708 bytes (R15.1, R15.5). The word of the reply is 0
(R15.7). Returns nothing if a line is missing or misspelled, or if a file does not have the form
that 12.3 covers. Call it on an admitted parameter file: lt is not bounded here. -/
def requestItem (parameterFile scaleFile requestFile : ByteArray) : Option ByteArray := do
  let L := ParamLines.read parameterFile
  let version ← (L.values "version").bind (·.head?)
  let prof ← L.value "prof"
  let ne ← L.value "NE"
  let lt ← L.value "lt"
  if version.length != 4 || prof != 20 || ne == 0 || requestFile.size != 4 * (2 ^ lt + 2) then none
  let w := Fmt.cat [
    word32 0x4D363100, ⟨version.toArray⟩, ← L.words names2, ← L.calls "call",
    ← L.words names37,
    ← L.eight "tsilu", ← L.eight "tsig", ← L.eight "trope", ← secondHashFunctionTree scaleFile,
    ← L.words names103, ← L.eight "texp", ← L.calls "callA", ← L.words names130,
    ← L.calls "callH" (some callHIfNone), ← secondHashFunctionTree requestFile, word32 0, ← L.lastWords]
  if w.size == 708 then some w else none

end OnBytes.Proof
