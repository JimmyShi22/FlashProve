-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Config.lean: the configuration files of a model as the verifier reads them, and the
acceptance policies.

A caller of the verifier holds a folder with three public files. policy.txt is the parameter file, a
text of named numbers. KL.bin holds the scales of the model's integer arithmetic as 32-bit words.
layout.txt says where the committed arrays are. This file reads the first two and hashes all three.
In names of files and refusals, policy means the whole parameter file; the acceptance policy is only
its lines C to F. OnBytes/Model/Frame.lean explains sub-proof, lookup call and smallness test.

The parameter file has two parts. Its first lines, from version to table, set the protocol's own
numbers: the security target, the bits of proof of work, the shapes of the codes (below: the frame's
lines). OnBytes/Params/File.lean reads them. The lines after them belong to the model, and the
strict scan of this file reads them (polScan; in C++ polPrescan and polScan,
verifier/src/cp_verify.cpp). The part on the scan says what it tests, what it leaves out, and how
long an admitted file can be.

An acceptance policy is what an accepted proof says about the checked tokens. It is set by seven
lines of the parameter file. The last part of this file sorts the policies into four kinds and
reads the policy that a caller names on the command line.

Main definitions: Config.linesOf, Config.wordLineForm, Config.scanLine, Config.polWord,
valueNames, Hdr, PolScan, polScan, polBeforeLayout, polBehindLayout, polTablesAdmitted,
PolScan.settings, PublicTable, tableHeld, klWhole, klHeld, fileWords, textTH, parDigests, hPar,
hex64, exactMatch, policyKind, aboveClip, policyEmpty, PolicyNamed, policyNamedRead, rotaryServed,
Config.names.

What this file does not claim. No theorem is stated here. The parts on the scan and on the digests
of the four public tables say what the C++ verifier tests and this file does not.
-/
import OnBytes.Params.File
import OnBytes.Hash.SecondHashFunction
import OnBytes.Model.Frame

namespace OnBytes.Model

namespace Config

/-! ## A text as lines -/

/-- Cuts a text into lines. cur: the bytes of the current line, the last one first. acc: the lines
that are complete, the last one first. -/
def linesLoop : List UInt8 → List UInt8 → List (List UInt8) → List (List UInt8)
  | [], cur, acc => (if cur.isEmpty then acc else cur.reverse :: acc).reverse
  | c :: t, cur, acc =>
    if c == 0x0A then linesLoop t [] ((c :: cur).reverse :: acc) else linesLoop t (c :: cur) acc

/-- The lines of a text, each with its line feed if it has one. -/
def linesOf (text : List UInt8) : List (List UInt8) := linesLoop text [] []

/-- True for a decimal digit. -/
def isDigit (c : UInt8) : Bool := 0x30 ≤ c && c ≤ 0x39

/-- True for a space, a tab, a line feed and the three other bytes that C counts as white space. -/
def isSpace (c : UInt8) : Bool := c == 0x20 || (0x09 ≤ c && c ≤ 0x0D)

/-- The number that decimal digits spell. -/
def digitsValue (l : List UInt8) : Nat := l.foldl (fun v c => 10 * v + (c.toNat - 0x30)) 0

/-- The bytes of a text. -/
def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

/-- Bytes below 128 as a text. -/
def textOf (l : List UInt8) : String := l.foldl (fun s b => s.push (Char.ofNat b.toNat)) ""

/-- True if the line begins with the text. -/
def begins (p : String) (line : List UInt8) : Bool := (Params.behind (bytesOf p) line).isSome

/-- True if the line is spelled in the only way that the format admits for a name with a number:
the name in printable bytes other than the space, a single space, the number in decimal, below
2^32 and without leading zeros, and the line feed. So names and numbers determine the bytes. -/
def wordLineForm (line : List UInt8) : Bool :=
  let name := line.takeWhile fun c => 0x20 < c && c < 0x7F
  match line.drop name.length with
  | 0x20 :: rest =>
    let digits := rest.takeWhile isDigit
    !name.isEmpty && !digits.isEmpty && decide (digits.length ≤ 10) &&
    (digits.head? != some 0x30 || digits.length == 1) && decide (digitsValue digits < 2 ^ 32) &&
    rest.drop digits.length == [0x0A]
  | _ => false

/-- True if the line has more than 19 decimal digits in a row. A number of at most 19 digits is
below 2^64. The C standard leaves open what the C library's scan makes of a number that 64 bits
cannot hold, so the C++ scan refuses such a line, which is in no valid spelling, before it scans
it. -/
def digitsBeyondScan (line : List UInt8) : Bool :=
  (line.foldl (fun (s : Nat × Bool) c =>
    let run := if isDigit c then s.1 + 1 else 0
    (run, s.2 || decide (19 < run))) (0, false)).2

/-- The lax reading of a value line that the C++ scan makes first, by the C library's pattern for
a word, a number and nothing more. It passes over white space, takes at most 63 bytes as the name,
and admits a sign before the digits. Returns name and number, or none if the line does not consist
of exactly these two. It only decides under which name a line is refused: wordLineForm is applied
to every line that passes. -/
def scanLine (line : List UInt8) : Option (List UInt8 × Nat) :=
  let a := line.dropWhile isSpace
  let name := (a.takeWhile fun c => !isSpace c).take 63
  let b := (a.drop name.length).dropWhile isSpace
  let signed : Bool × List UInt8 :=
    match b with
    | 0x2D :: r => (true, r)
    | 0x2B :: r => (false, r)
    | _ => (false, b)
  let digits := signed.2.takeWhile isDigit
  let v := digitsValue digits
  if name.isEmpty || digits.isEmpty ||
      !((signed.2.drop digits.length).dropWhile isSpace).isEmpty then none
  else some (name, if signed.1 then (2 ^ 64 - v) % 2 ^ 64 else v)

/-- scanLine, after the test for more than 19 digits in a row, which fails as policy-line-form. -/
def scanned (line : List UInt8) : Except String (Option (List UInt8 × Nat)) :=
  if digitsBeyondScan line then .error "policy-line-form" else .ok (scanLine line)

/-- Refuses a value line that is not in the one spelling. -/
def oneSpelling (line : List UInt8) : Except String Unit :=
  if wordLineForm line then .ok () else .error "policy-line-form"

/-! ## The lines prof, toksrc and lt, which are read before the scan -/

/-- The value of the first line that begins with the name and a space and has a further byte; none
if there is no such line, or if what follows the space in it is not one to ten digits. -/
def findWord (name : String) : List (List UInt8) → Option Nat
  | [] => none
  | line :: rest =>
    let l := line.filter fun c => c != 0x0A
    match Params.behind (bytesOf name ++ [0x20]) l with
    | some v =>
      if v.isEmpty then findWord name rest
      else if decide (10 < v.length) || !v.all isDigit then none
      else some (digitsValue v)
    | none => findWord name rest

/-- A number of the model's lines by its name, read before the scan. whole: a whole parameter file,
of which the lines after the frame's are searched, or only those lines. A text that begins with the
line version and whose frame's lines are refused gives none. polScan asks it only for prof, toksrc
and lt; the C++ routine (polWord, verifier/src/cp_verify.cpp) also answers names that follow from
the frame's lines. -/
def polWord (whole : ByteArray) (name : String) : Option Nat :=
  match Params.readLines whole with
  | .ok x => findWord name (linesOf x.2.toList)
  | .error _ =>
    if begins "version " whole.toList then none else findWord name (linesOf whole.toList)

end Config

open Config

/-! ## The names of the value lines -/

/-- The names of the value lines from prof to F, in their order. The eleven lines of the attention
sub-proofs are there from profile 4 on. -/
def valueNames (prof : Nat) : List String :=
  ["prof", "lt", "L", "ll", "d", "H", "G", "dh", "f", "fe", "NE", "V", "eps1_lo", "eps1_hi",
   "eps2_lo", "eps2_hi", "cs", "theta0_lo", "theta0_hi", "hq", "hv", "ho", "hgD", "huD", "hdD",
   "hr", "ut", "la", "nmin", "D", "tau", "lmaf", "NAf", "lmad", "NAd", "lmar", "lmb", "lmq",
   "lmx", "wb_qk", "wb_v", "wb_o", "wb_g", "wb_u", "wb_gs", "wb_us", "wb_gr", "wb_ur", "wb_dn",
   "wb_dnr", "wb_r", "iota_0", "iota_1", "iota_2", "iota_3", "iota_4", "iota_5", "iota_6",
   "iota_7", "seed_lo", "seed_hi"] ++
  (if 4 ≤ prof then
    ["lB", "S", "rx", "kFM", "kFD", "lmS", "NAs", "lmh", "lmo", "lmbA", "iotaA_0"]
   else []) ++
  ["MF", "KF", "epsF_lo", "epsF_hi", "toksrc", "lmhf", "NHf", "lmhd", "lmhr", "lmbH", "wb_emb",
   "wb_head", "iotaH_0", "iotaH_1", "iotaH_2", "iotaH_3", "iotaH_4", "iotaH_5", "C", "theta",
   "cap", "s", "sh", "sT", "F"]

/-- Names that a line after the line F must not have. Such a line is refused under the
one name policy-line-of-an-earlier-format, as is every line that begins with mb. -/
def goneNames : List String :=
  ["magic", "version", "hb", "lkW", "fb", "fln", "fnm", "lNmax", "fi0", "fe0", "leafd", "zva",
   "leafo", "zvo", "fuk", "fun", "pow", "fhb", "pows", "powc", "lsalt", "oxc", "oxr", "oxv", "oxs",
   "oxu", "orw", "ocq", "oiD", "oiU", "oiS", "Rrep", "t0", "lmW", "lc", "ir", "lwr"]

/-- The prefixes of the names of the 32 lines with the digests of the four public tables. -/
def tableNames : List String := ["tsilu", "tsig", "trope", "texp"]

/-! ## The scan

The scan admits one order and one spelling. The aim is that the values read determine the file's
bytes; no theorem here says so. The scan is written to make the same tests on the file as the C++
verifier's scan, in the same order, and to refuse under the same names (verifier/src/cp_verify.cpp,
polPrescan and polScan; verifier/docs/parameter-file.md); no theorem says that either.

On a line from prof to F the scan tests the form. The range of such a value is tested where the part
of the proof that uses it is set up. Exceptions in this file: prof, toksrc and lt are tested before
the scan (polScan), and tau after it (polBeforeLayout, polBehindLayout).

How long an admitted file can be. Each of the frame's 32 lines has at most 32 numbers of at most 15
digits (OnBytes/Params/File.lean). The 97 value lines and the 39 optional lines (lineAfterF) have a
fixed name and at most ten digits. A call line has at most 1023 bytes, and the three layouts admit
at most 8 lines call, 12 lines callA and 6 lines callH (LayerLayout.lean, AttentionConfig.lean and
HeadLayout.lean in OnBytes/Model/). Together that is under 50,000 bytes. This is a count by reading,
not a theorem; OnBytes/Model/TestConfigBytes.lean adds it up. The scan itself does not bound the
number of call lines.

What is left out. In a whole call the C++ program tests the first line of the parameter file and
hashes the three files before its stages scan the parameter file; that order is left to the caller.
The C++ scan also writes each value into the verifier's own statement, the list of 32-bit words that
cp_verify builds from its public inputs, with two tests of its own (internal-statement-twice: two
sources give a word differently; internal-statement-cover), and the routine after it reads the
statement back (internal-statement-prescan). This file builds no statement and has no counterpart of
these three tests. -/

/-- What the scan has read so far. -/
structure PolState where
  /-- the values of the lines from prof on, read so far -/
  vals : Array Nat := #[]
  /-- the line lidb -/
  lidb : Option Nat := none
  /-- the line nminH -/
  nminH : Option Nat := none
  /-- the line eg -/
  eg : Option Nat := none
  /-- the line smax -/
  smax : Option Nat := none
  /-- the line rcl has been read -/
  rcl : Bool := false
  /-- the line gcl has been read -/
  gcl : Bool := false
  /-- the line xl has been read -/
  xl : Bool := false
  /-- the words of the tables' digests, read so far -/
  tbl : Array Nat := #[]
  /-- the line before this one was one of the tables' lines -/
  tblPrev : Bool := false
  /-- the lines call: name, kind, segments -/
  calls : Array (List String) := #[]
  /-- the lines callA -/
  callsA : Array (List String) := #[]
  /-- the lines callH -/
  callsH : Array (List String) := #[]

/-- True if a call line has been read. -/
def PolState.anyCall (s : PolState) : Bool :=
  !s.calls.isEmpty || !s.callsA.isEmpty || !s.callsH.isEmpty

/-- The three tests on the frame's lines that the model's verifier adds to the frame's own. They are
made when the line F has been read. The C++ verifier keeps the committed table's numbers in 32
bits, takes at most 32 bits of proof of work of every kind, and at most 256 requests in a batch. On
lines that the frame's reader has read, the first test cannot fail (by reading, no theorem): the
reader admits a code of at most 2 ^ 32 positions and asks that a row's coordinates together be below
its length. The C++ verifier makes the test all the same, and so does this
one. -/
def frameWords (f : Params.Lines) : Except String Unit := do
  refuseIf ([f.tableData, f.tableRandom].any fun x => decide (2 ^ 32 ≤ x))
    "parameter-table-shape (policy)"
  refuseIf ([f.workField, f.workSample, f.workCloseness, f.workPositions, f.workSmallness].any
    fun w => [w.request, w.shared, w.once].any fun bits => decide (workMost < bits))
    "policy-work-most"
  refuseIf (decide (8 < ceilLog2 f.slots)) "policy-leafd"

/-- True for a byte that an item of a call line may hold: a letter, a digit, a full stop, an
underscore or a hyphen. The C++ verifier prints items at the end of some refusal names (none of this
file's), so no control byte or space may occur in them. -/
def callByte (c : UInt8) : Bool :=
  (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A) || isDigit c || c == 0x2E || c == 0x5F ||
  c == 0x2D

/-- A call line: at least four items, separated by single spaces, and one line feed at the end. The
items are the word call, callA or callH, the call's name, the kind of its table, and one or more
segments. The lines call come first, then the lines callA, which are admitted from profile 4 on,
then the lines callH. The call's name has at most 8 characters. -/
def callLine (prof : Nat) (s : PolState) (line : List UInt8) : Except String PolState := do
  refuseIf (line.getLast? != some 0x0A) "policy-call-line"
  let items := Params.pieces line.dropLast
  refuseIf (items.any fun t => t.isEmpty || !t.all callByte) "policy-call-line"
  let tok := items.map textOf
  refuseIf ((items[1]?).any fun t => decide (8 < t.length)) "policy-call-line"
  refuseIf (decide (tok.length < 4)) "policy-call-line"
  match tok with
  | "call" :: rest =>
    refuseIf (!s.callsA.isEmpty || !s.callsH.isEmpty) "policy-call-line"
    pure { s with calls := s.calls.push rest }
  | "callA" :: rest =>
    refuseIf (decide (prof < 4) || !s.callsH.isEmpty) "policy-call-line"
    pure { s with callsA := s.callsA.push rest }
  | "callH" :: rest => pure { s with callsH := s.callsH.push rest }
  | _ => .error "policy-call-line"

/-- The number of an optional line that has passed the tests on its place. Fails under the given
name if the line is not a name and a number, and as policy-line-form if it is not in the one
spelling. -/
def optionalValue (line : List UInt8) (name : String) : Except String Nat := do
  match ← scanned line with
  | some x =>
    oneSpelling line
    pure x.2
  | none => .error name

/-- Reads one line after the line F. A line of goneNames, a line that begins with mb and the lines
clt, clns and cms are refused first. The optional lines come at most once each and in this order:
lidb, nminH (only after lidb), eg, smax, rcl, gcl, xl, the 32 lines of the tables without a gap, the
call lines. The range of an optional line is tested here: lidb 23 to 30, nminH 2 to 28, eg 4 to 7,
smax 2047, 1023, 511 or 255, rcl 1, gcl 1, xl 5. So a line that would state its default (lidb 22,
eg 8, smax 4095, xl 4) is refused: with it the same values would have a second spelling. Every other
line is read as a call line, so an unknown name fails as policy-call-line. afterTbl: the line before
was one of the tables' lines. -/
def lineAfterF (prof : Nat) (afterTbl : Bool) (s : PolState) (line : List UInt8) :
    Except String PolState := do
  refuseIf ((goneNames.any fun g => begins (g ++ " ") line) || begins "mb" line)
    "policy-line-of-an-earlier-format"
  refuseIf (begins "clt " line || begins "clns " line || begins "cms " line) "policy-cert-words"
  let tables := s.tbl.size != 0
  if begins "lidb " line then
    refuseIf (s.lidb.isSome || s.nminH.isSome || s.eg.isSome || s.smax.isSome || s.rcl || s.gcl ||
      s.xl || tables || s.anyCall) "policy-lidb"
    let val ← optionalValue line "policy-lidb"
    refuseIf (decide (val ≤ lidbSealed)) "policy-lidb"
    refuseIf (decide (lidbMost < val)) "plan-identity-cap"
    pure { s with lidb := some val }
  else if begins "nminH " line then
    refuseIf (s.lidb.isNone || s.nminH.isSome || s.eg.isSome || s.smax.isSome || s.rcl || s.gcl ||
      s.xl || tables || s.anyCall) "policy-nminH"
    let val ← optionalValue line "policy-nminH"
    refuseIf (decide (val < 2) || decide (nminHMost < val)) "policy-nminH"
    pure { s with nminH := some val }
  else if begins "eg " line then
    refuseIf (s.smax.isSome || s.eg.isSome || s.rcl || s.gcl || s.xl || tables || s.anyCall)
      "policy-gate-table"
    let val ← optionalValue line "policy-gate-table"
    refuseIf (decide (val < 4) || decide (7 < val)) "policy-gate-table"
    pure { s with eg := some val }
  else if begins "smax " line then
    refuseIf (s.smax.isSome || s.rcl || s.gcl || s.xl || tables || s.anyCall) "policy-gate-table"
    let val ← optionalValue line "policy-gate-table"
    refuseIf (!([2047, 1023, 511, 255].contains val)) "policy-gate-table"
    pure { s with smax := some val }
  else if begins "rcl " line then
    refuseIf (s.rcl || s.gcl || s.xl || tables || s.anyCall) "policy-rcl"
    match ← scanned line with
    | some (_, 1) =>
      oneSpelling line
      pure { s with rcl := true }
    | _ => .error "policy-rcl"
  else if begins "gcl " line then
    refuseIf (s.gcl || s.xl || tables || s.anyCall) "policy-gcl"
    match ← scanned line with
    | some (_, 1) =>
      oneSpelling line
      pure { s with gcl := true }
    | _ => .error "policy-gcl"
  else if begins "xl " line then
    refuseIf (s.xl || tables || s.anyCall) "policy-xl"
    let val ← optionalValue line "policy-xl"
    refuseIf (val != 5) "policy-xl"
    pure { s with xl := true }
  else if tableNames.any fun t => begins t line then
    refuseIf (decide (32 ≤ s.tbl.size) || (tables && !afterTbl) || s.anyCall) "policy-tables"
    match ← scanned line with
    | some (name, val) =>
      refuseIf (decide (2 ^ 32 ≤ val)) "policy-tables"
      oneSpelling line
      refuseIf (bytesOf (tableNames.getD (s.tbl.size / 8) "" ++ toString (s.tbl.size % 8)) != name)
        "policy-tables"
      pure { s with tbl := s.tbl.push val, tblPrev := true }
    | none => .error "policy-tables"
  else callLine prof s line

/-- One line of the scan. names: the names of the lines from prof to F. -/
def polStep (frame : Params.Lines) (prof : Nat) (names : Array String) (s : PolState)
    (line : List UInt8) : Except String PolState := do
  refuseIf (decide (1023 < line.length)) "policy-line-long"
  refuseIf (line.contains 0) "policy-zero-byte"
  let afterTbl := s.tblPrev
  let s := { s with tblPrev := false }
  match names[s.vals.size]? with
  | some due =>
    -- The C++ verifier counts the line prof as 2. This is not the line's number in the file.
    let number := "policy-line-" ++ toString (s.vals.size + 2)
    match ← scanned line with
    | some (name, val) =>
      refuseIf (decide (2 ^ 32 ≤ val)) number
      refuseIf (name != bytesOf due) ("policy-name-" ++ due)
      oneSpelling line
      let s := { s with vals := s.vals.push val }
      if s.vals.size == names.size then frameWords frame
      pure s
    | none => .error number
  | none => lineAfterF prof afterTbl s line

/-! ## What the scan gives -/

/-- The numbers of the model's value lines, under the names of the C++ verifier's header record. A
number of 64 bits is made of its two lines. What each line means and which
values it may have: verifier/docs/parameter-file.md. -/
structure Hdr where
  /-- the profile: the line prof minus 16. 4 is the whole model, 3 the model without attention. A
  run below profile 4 does not check attention: the C++ verifier ends it at best with the words that
  it is no verification, whatever number of bits is asked -/
  prof : Nat := 0
  /-- log2 of the number of tokens in a request's window -/
  lt : Nat := 0
  /-- the number of layers -/
  L : Nat := 0
  /-- log2 of the number of layers that one sub-proof covers -/
  ll : Nat := 0
  /-- the width of the residual stream -/
  d : Nat := 0
  /-- the number of query heads -/
  H : Nat := 0
  /-- the number of key and value heads: the line G -/
  Gk : Nat := 0
  /-- the dimension of a head -/
  dh : Nat := 0
  /-- the hidden width of a dense layer's feed-forward network -/
  f : Nat := 0
  /-- the hidden width of one expert -/
  fe : Nat := 0
  /-- the number of routed experts -/
  NE : Nat := 0
  /-- the size of the vocabulary -/
  V : Nat := 0
  /-- the constants of the first and the second norm of a layer: the lines eps1 and eps2 -/
  eps : Array Nat := #[0, 0]
  /-- log2 of the scale of the rotary table's entries -/
  cs : Nat := 0
  /-- the base of the rotary position embedding -/
  theta0 : Nat := 0
  /-- the digit form (how many high bytes of a rounding remainder are committed: 0, 1 or 2) of each
  of the 13 classes of rounding sites, in the order queries, keys, values, attention output; gate,
  up and down of a dense layer; router; gate and up of the shared expert; gate and up of the routed
  experts; down of the expert layers. The file gives seven; each other class has the form of the
  class whose digit tensor it shares. This is not the matrix hf of the line lmhf -/
  hf : Array Nat := Array.replicate 13 0
  /-- 1: the output of the up projection is range-checked to 16 bits -/
  ut : Nat := 0
  /-- a feature is a run of committed values, one for each token of the window. Features are
  evaluated 2^(la - lt) at a time, that is 2^la values at a time -/
  la : Nat := 0
  /-- a lookup call has at least 2^nmin keys -/
  nmin : Nat := 0
  /-- the rows of a unit of the committed weight matrix are rounded up to a multiple of D -/
  D : Nat := 0
  /-- the number of random combinations of the smallness test -/
  tau : Nat := 0
  /-- log2 of the rows of the matrix af: most intermediate values of the layers -/
  lmaf : Nat := 0
  /-- the parts into which the columns of af are cut -/
  NAf : Nat := 0
  /-- log2 of the rows of the matrix ad: the norms' outputs, the routed expert's input -/
  lmad : Nat := 0
  /-- the parts into which the columns of ad are cut -/
  NAd : Nat := 0
  /-- log2 of the rows of the matrix ar: the router's values, the norms' rows of digits -/
  lmar : Nat := 0
  /-- log2 of the rows of the matrix b: the multiplicities of the lookups, bit by bit -/
  lmb : Nat := 0
  /-- log2 of the rows of the matrix qa: queries, keys, values, attention outputs -/
  lmq : Nat := 0
  /-- log2 of the rows of the matrices of the residual stream before and after the layers that one
  sub-proof covers -/
  lmx : Nat := 0
  /-- the declared width of a weight, by kind: the twelve lines wb_qk to wb_r -/
  wb : Array Nat := Array.replicate 12 0
  /-- the lines iota_0 to iota_7: the lookup call of the i-th line call, counted from 0, has
  2^iota_i trees. A file has at most eight lines call; iota_i is meant to be 0 if there is no i-th.
  This file tests neither -/
  iota : Array Nat := Array.replicate 8 0
  /-- a public seed. At profile 4 nothing uses it; below it, it seeds the pseudo-random numbers that
  stand in for the attention's outputs -/
  seed : Nat := 0
  /-- log2 of the side of a tile of a head's score matrix. This line and the ten after it
  belong to the attention sub-proofs and are 0 below profile 4 -/
  lB : Nat := 0
  /-- the largest softmax weight is 2^Sx: the line S -/
  Sx : Nat := 0
  /-- the softmax table holds 2^Sx exp(-u / 2^rx), rounded, for u = 0, 1 and so on -/
  rx : Nat := 0
  /-- a line that no test and no formula reads; it is hashed like every line -/
  kFM : Nat := 0
  /-- log2 of the rows of the lookup table that contains the softmax table -/
  kFD : Nat := 0
  /-- log2 of the rows of a part of the matrix as: the softmax weight of each score -/
  lmS : Nat := 0
  /-- the parts of the matrix as -/
  NAs : Nat := 0
  /-- log2 of the rows of the matrix ah: largest score and sum of weights by head, token -/
  lmh : Nat := 0
  /-- log2 of the rows of the matrix ao: high digits of the division's remainders -/
  lmo : Nat := 0
  /-- log2 of the rows of the matrix bA: the multiplicities of attention's lookups -/
  lmbA : Nat := 0
  /-- 32 plus log2 of the keys of a tree of attention's lookups: the line iotaA_0 -/
  iotaA0 : Nat := 0
  /-- the final norm multiplies by a reciprocal that is scaled by 2^MF -/
  MF : Nat := 0
  /-- the final norm then shifts right by KF bits -/
  KF : Nat := 0
  /-- the constant of the final norm -/
  epsF : Nat := 0
  /-- 1: the model's input is the embedding of the request's tokens -/
  toksrc : Nat := 0
  /-- log2 of the rows of the matrix hf: the final norm's quotients, the logits' digits -/
  lmhf : Nat := 0
  /-- the parts into which the columns of hf are cut -/
  NHf : Nat := 0
  /-- log2 of the rows of the matrix hd: the final norm's output -/
  lmhd : Nat := 0
  /-- log2 of the rows of the matrix hr: the final norm's and the costs' digits -/
  lmhr : Nat := 0
  /-- log2 of the rows of the matrix bH: the multiplicities of the head's lookups -/
  lmbH : Nat := 0
  /-- the lines wb_emb and wb_head -/
  wbH : Array Nat := #[0, 0]
  /-- the lines iotaH_0 to iotaH_5: as iota, for the i-th line callH, of which a file has at most
  six -/
  iotaH : Array Nat := Array.replicate 6 0
  /-- the acceptance policy's line C: the clip of a token's cost -/
  clipC : Nat := 0
  /-- the acceptance policy's line theta: the bound on the mean of the clipped costs -/
  theta : Nat := 0
  /-- the acceptance policy's line cap: the most tokens with a cost above the clip -/
  cap : Nat := 0
  /-- the acceptance policy's line s: the provider's statement of the scale 2^s of the logits -/
  logS : Nat := 0
  /-- the acceptance policy's line sh: 2^sh is added to every gap between logits -/
  digSh : Nat := 0
  /-- the acceptance policy's line sT, which selects the table that the head looks up -/
  tabS : Nat := 0
  /-- the acceptance policy's line F: that table's values are scaled by 2^F -/
  famF : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The record of the value lines. get: the value of a line by its name. A class of the expert
layers shares its digit tensor with the dense class, and the keys with the queries. The model has
expert layers at profile 3, and at profile 4 if NE is not 0. Without them the five classes of gate,
up and down of the expert layers have the form 0; the router's class keeps the file's value. -/
def hdrOf (get : String → Nat) : Hdr :=
  let wide := fun (name : String) => get (name ++ "_lo") + 2 ^ 32 * get (name ++ "_hi")
  let prof := get "prof" % 16
  let experts := prof == 3 || (prof == 4 && get "NE" != 0)
  let ifExperts := fun (x : Nat) => if experts then x else 0
  { prof := prof, lt := get "lt", L := get "L", ll := get "ll", d := get "d", H := get "H",
    Gk := get "G", dh := get "dh", f := get "f", fe := get "fe", NE := get "NE", V := get "V",
    eps := #[wide "eps1", wide "eps2"], cs := get "cs", theta0 := wide "theta0",
    hf := #[get "hq", get "hq", get "hv", get "ho", get "hgD", get "huD", get "hdD", get "hr",
      ifExperts (get "hgD"), ifExperts (get "huD"), ifExperts (get "hgD"), ifExperts (get "huD"),
      ifExperts (get "hdD")],
    ut := get "ut", la := get "la", nmin := get "nmin", D := get "D", tau := get "tau",
    lmaf := get "lmaf", NAf := get "NAf", lmad := get "lmad", NAd := get "NAd",
    lmar := get "lmar", lmb := get "lmb", lmq := get "lmq", lmx := get "lmx",
    wb := (["qk", "v", "o", "g", "u", "gs", "us", "gr", "ur", "dn", "dnr", "r"].map
      fun k => get ("wb_" ++ k)).toArray,
    iota := ((List.range 8).map fun c => get ("iota_" ++ toString c)).toArray,
    seed := wide "seed", lB := get "lB", Sx := get "S", rx := get "rx", kFM := get "kFM",
    kFD := get "kFD", lmS := get "lmS", NAs := get "NAs", lmh := get "lmh", lmo := get "lmo",
    lmbA := get "lmbA", iotaA0 := get "iotaA_0", MF := get "MF", KF := get "KF",
    epsF := wide "epsF", toksrc := get "toksrc", lmhf := get "lmhf", NHf := get "NHf",
    lmhd := get "lmhd", lmhr := get "lmhr", lmbH := get "lmbH",
    wbH := #[get "wb_emb", get "wb_head"],
    iotaH := ((List.range 6).map fun c => get ("iotaH_" ++ toString c)).toArray,
    clipC := get "C", theta := get "theta", cap := get "cap", logS := get "s",
    digSh := get "sh", tabS := get "sT", famF := get "F" }

/-- What the strict scan gives. -/
structure PolScan where
  /-- the frame's lines -/
  frame : Params.Lines
  /-- the value lines from prof to F: name and value, in the file's order -/
  values : List (String × Nat)
  /-- the value lines from prof to F as a record -/
  h : Hdr
  /-- the lines call: name, kind, segments -/
  polCalls : List (List String)
  /-- the lines callA -/
  polCallsA : List (List String)
  /-- the lines callH -/
  polCallsH : List (List String)
  /-- the line lidb, if it is there -/
  lidb : Option Nat
  /-- the line nminH, if it is there -/
  nminH : Option Nat
  /-- the line eg, if it is there; without it the gate table's step is 2^-8 -/
  eg : Option Nat
  /-- the line smax, if it is there; without it the gate table's bound is 4095 -/
  smax : Option Nat
  /-- the line rcl 1 is there: the router's logits are clamped -/
  rcl : Bool
  /-- the line gcl 1 is there: the key of the gate table is clamped -/
  gcl : Bool
  /-- the line xl 5 is there: a value of the residual stream has five limbs and not four -/
  xl : Bool
  /-- the 32 words of the four public tables' digests; empty if the file has no such lines -/
  tblPol : Array Nat
  deriving Repr, Inhabited

namespace PolScan

/-- The value of a line from prof to F by its name; 0 for a name that the file lacks. -/
def value (P : PolScan) (name : String) : Nat := (P.values.lookup name).getD 0

/-- The security target in bits: the line sec of the parameter file. hb is the C++ verifier's name
for the word of its statement that holds it. -/
def hb (P : PolScan) : Nat := P.frame.sec

/-- log2 of the columns of the committed weight matrix: the last number of the frame's
line table. -/
def lkW (P : PolScan) : Nat := P.frame.blockLog

/-- The step between the keys of the gate table is 2^-EG. -/
def EG (P : PolScan) : Nat := P.eg.getD 8

/-- The values of the gate table are clamped to this bound. -/
def SMAX (P : PolScan) : Nat := P.smax.getD 4095

/-- The limbs of a value of the residual stream. -/
def XL (P : PolScan) : Nat := if P.xl then 5 else 4

/-- The numbers that the file sets for a run. -/
def settings (P : PolScan) : Settings where
  lidb := P.lidb.getD lidbSealed
  nminH := P.nminH.getD 0
  tau := P.h.tau
  pow := P.frame.workPositions.request
  powS := P.frame.workPositions.shared
  powC := P.frame.workPositions.once
  hb := P.hb

end PolScan

/-- The names under which the reader of the frame's lines refuses. -/
def frameFaults : List String :=
  ["version-of-an-earlier-format", "version-of-another-field", "version-of-another-hash",
   "version-unknown", "parameter-line-missing", "parameter-line-order", "parameter-line-blanks",
   "parameter-line-values", "parameter-number-spelling", "parameter-range",
   "parameter-group-shape", "parameter-stages-count", "parameter-stages-shape",
   "parameter-own-code", "parameter-one-mask-code", "parameter-table-shape"]

/-- The refusal name for a fault in the frame's lines: the reader's reason up to its first ": " or
" (line ", then " (policy)". A reason that is not in frameFaults gives internal-parameter-name, so
the result is always one of a fixed list. The C++ routine (polPrescan, verifier/src/cp_verify.cpp)
passes on every reason that begins with parameter-; the frame's reader gives none outside the list,
so no file shows the difference. -/
def frameRefusal (fault : String) : String :=
  let name := ((fault.splitOn ": ").headD "").splitOn " (line " |>.headD ""
  if frameFaults.contains name then name ++ " (policy)" else "internal-parameter-name"

/-- Every name under which a function of this file refuses. The names of the two families that end
in a line's number or name are written out: both sets are fixed. No name holds anything that was
read from a file. What the names mean: verifier/docs/parameter-file.md. Five are not on that page:
internal-parameter-name, hid-hb, KL-length, close-list-long and internal-th. -/
def Config.names : List String :=
  frameFaults.map (· ++ " (policy)") ++
  ["internal-parameter-name", "statement-required", "shape-words",
   "policy-line-long", "policy-zero-byte", "policy-line-form", "policy-work-most", "policy-leafd",
   "policy-line-of-an-earlier-format", "policy-cert-words", "policy-lidb", "plan-identity-cap",
   "policy-nminH", "policy-gate-table", "policy-rcl", "policy-gcl", "policy-xl", "policy-tables",
   "policy-call-line", "policy-length", "hid-tau", "hid-hb", "policy-tau-hb", "table-digest-silu",
   "table-digest-sigmoid", "table-digest-rope", "table-digest-exp", "KL-length",
   "close-list-long", "internal-th"] ++
  (List.range (valueNames 4).length).map (fun i => "policy-line-" ++ toString (i + 2)) ++
  (valueNames 4).map ("policy-name-" ++ ·)

/-- The strict scan of the parameter file. Returns what the file says, or the name of the first test
that failed. -/
def polScan (pol : ByteArray) : Except String PolScan := do
  let (frame, rest) ←
    match Params.readLines pol with
    | .ok x => pure x
    | .error fault => .error (frameRefusal fault)
  -- three lines are read by name before the scan
  let pp := polWord rest "prof"
  let pts := polWord rest "toksrc"
  refuseIf ((pp.map (· / 16)) != some 1 || pts != some 1) "statement-required"
  let plt ←
    match polWord rest "lt" with
    | some x => pure x
    | none => .error "policy-name-lt"
  refuseIf (decide (plt < 4) || decide (16 < plt)) "shape-words"
  let prof := pp.getD 0 % 16
  let names := valueNames prof
  let s ← (linesOf rest.toList).foldlM (polStep frame prof names.toArray) {}
  refuseIf (s.vals.size != names.length) "policy-length"
  refuseIf (s.tbl.size != 0 && s.tbl.size != 32) "policy-tables"
  let values := names.zip s.vals.toList
  pure { frame := frame, values := values, h := hdrOf fun n => (values.lookup n).getD 0,
         polCalls := s.calls.toList, polCallsA := s.callsA.toList, polCallsH := s.callsH.toList,
         lidb := s.lidb, nminH := s.nminH, eg := s.eg, smax := s.smax, rcl := s.rcl, gcl := s.gcl,
         xl := s.xl, tblPol := s.tbl }

/-- The tests on nminH and tau that follow the scan, before the layout of a layer sub-proof is made
(C++: polLayout, verifier/src/cp_verify.cpp). nminH must be above nmin: without the line, nmin
holds for the head too, and a default is never written. Before these two the C++ routine reads its
own statement back (internal-statement-prescan); that test has no counterpart here. -/
def polBeforeLayout (P : PolScan) : Except String Unit := do
  refuseIf (P.nminH.any fun x => decide (x ≤ P.h.nmin)) "policy-nminH"
  refuseIf (!tauServed P.h.tau) "hid-tau"

/-- The tests on the file's numbers that the C++ verifier makes after it has made the layout of a
layer sub-proof (polLayout, verifier/src/cp_verify.cpp). The security target must be from 1 to
4096 and at most tau. The C++ verifier then checks that every call of the layout has multiplicities
of 32 bits, which is a test on the layout, and then makes the test polTablesAdmitted. -/
def polBehindLayout (P : PolScan) : Except String Unit := do
  refuseIf (decide (P.hb < 1) || decide (4096 < P.hb)) "hid-hb"
  refuseIf (decide (P.h.tau < P.hb)) "policy-tau-hb"

/-- The tables' lines are admitted only where all four tables exist, so that every digest can be
compared: at profile 4 with routed experts. -/
def polTablesAdmitted (P : PolScan) : Except String Unit :=
  refuseIf (P.tblPol.size != 0 && !(P.h.prof == 4 && P.h.NE != 0)) "policy-tables"

/-! ## The digests of the four public tables

The C++ verifier computes the four public tables itself and compares their digests with the
parameter file's lines. This file only offers the comparison (tableHeld): whether a given table is
the right function is not tested here. -/

/-- The four public tables of the model's integer arithmetic. -/
inductive PublicTable where
  /-- the gate's table -/
  | silu
  /-- the sigmoid's table; if the line gcl is there, the middle half of it and then the table of
  the clamp -/
  | sigmoid
  /-- the rotary table -/
  | rope
  /-- the softmax table -/
  | exp
  deriving DecidableEq, Repr, Inhabited

/-- The table's place among the digests' lines. -/
def PublicTable.index : PublicTable → Nat
  | .silu => 0
  | .sigmoid => 1
  | .rope => 2
  | .exp => 3

/-- The name under which a table is refused whose digest differs from the parameter file's. -/
def PublicTable.refusal : PublicTable → String
  | .silu => "table-digest-silu"
  | .sigmoid => "table-digest-sigmoid"
  | .rope => "table-digest-rope"
  | .exp => "table-digest-exp"

/-- The number under which a table's words are hashed by the hash of OnBytes/Hash/SecondHashFunction.lean, which
lean/TERMS.md calls the second hash function. -/
def tableHashNumber : Nat := 72

/-- The digest of a table that is given as the bytes of its 32-bit words. -/
def tableDigest (words : ByteArray) : ByteArray := secondHashFunction tableHashNumber words

/-- The digest that the parameter file gives for a table: 32 bytes; none if the file has no such
lines. -/
def PolScan.tableExpected (P : PolScan) (t : PublicTable) : Option ByteArray :=
  if P.tblPol.size == 32 then
    some (Fmt.cat ((P.tblPol.extract (8 * t.index) (8 * t.index + 8)).toList.map word32))
  else none

/-- Hashes a table, given as its 32-bit words, and compares the digest with the parameter file's
lines. Why the file has such lines: the C++ verifier computes the tables with its platform's
floating-point library, and two libraries may round a last bit differently; the digests fix which
tables a proof is about. The caller must pass the same array that its lookups read; otherwise the
table that is compared is not the table that is used. If the file has no such lines, nothing is
compared and the result is ok. -/
def tableHeld (P : PolScan) (t : PublicTable) (table : Array Nat) : Except String Unit :=
  let mine := tableDigest (table.foldl (fun b x => b ++ word32 x) ByteArray.empty)
  refuseIf ((P.tableExpected t).any fun d => d != mine) t.refusal

/-! ## The scale file, and the digest of the three files -/

/-- The scale file is made of whole 32-bit words. The C++ verifier checks this where it reads the
file (vf_input_files.h, cpConfRead), before any test on the content of a configuration file. -/
def klWhole (KL : ByteArray) : Except String Unit := refuseIf (KL.size % 4 != 0) "KL-length"

/-- The scale file is made of whole 32-bit words, at least eight. The second hash function takes no
list of fewer than eight words (secondHashFunctionTree). The C++ routine parDigests (verifier/src/cp_verify.cpp)
refuses a shorter scale file as KL-length before it hashes the file, as does parDigests here. -/
def klHeld (KL : ByteArray) : Except String Unit :=
  refuseIf (KL.size % 4 != 0 || decide (KL.size < 32)) "KL-length"

/-- The number of the scale file's words. -/
def klWords (KL : ByteArray) : Nat := KL.size / 4

/-- Word i of a file of 32-bit words, the lowest byte first. It is 0 from the end of the file on,
and no test of this file bounds i. -/
def klWord (KL : ByteArray) (i : Nat) : Nat :=
  if 4 * i + 4 ≤ KL.size then Fmt.leNat KL (4 * i) 4 else 0

/-- All 32-bit words of a file, in their order. Bytes after the last whole word are left out;
klWhole refuses a scale file that has such bytes. The layers' checks should take the scales only
from this array, so that what they read comes from the bytes that are hashed. Lean does not enforce
this. Layer.scalesOf (OnBytes/Model/LayerLayout.lean) tests the number of the scales' words. -/
def fileWords (b : ByteArray) : Array Nat := (Array.range (b.size / 4)).map (klWord b)

/-- The digest of a text file, with the number of words of the list that was hashed. The list is the
file's length in bytes, the bytes, and zeros up to a whole word and for seven words more. The length
is one word of 32 bits, so a file of 2^32 bytes or more has no such list and fails as
close-list-long. -/
def textTH (text : ByteArray) : Except String (ByteArray × Nat) := do
  refuseIf (decide (2 ^ 32 ≤ text.size)) "close-list-long"
  let w := word32 text.size ++ OnBytes.textWords text ++ Fmt.zeroBytes 28
  match secondHashFunctionTree w with
  | some d => pure (d, w.size / 4)
  | none => .error "internal-th"

/-- The digests of the three configuration files, each with the number of words of the list that was
hashed. -/
structure ParDigests where
  /-- the digest of the parameter file -/
  pol : ByteArray
  /-- the number of words of the list that was hashed for it -/
  polW : Nat
  /-- the digest of the scale file -/
  kl : ByteArray
  /-- the number of the scale file's words -/
  klW : Nat
  /-- the digest of the layout file -/
  lay : ByteArray
  /-- the number of words of the list that was hashed for it -/
  layW : Nat

/-- Hashes the three files. Without a layout file, zeros replace its digest and length. That case
only defines the digest: by its usage text the C++ verifier refuses every call without a layout
file (plan-layout). -/
def parDigests (pol KL : ByteArray) (layout : Option ByteArray) : Except String ParDigests := do
  let p ← textTH pol
  klHeld KL
  let k ←
    match secondHashFunctionTree KL with
    | some d => pure d
    | none => .error "KL-length"
  let l ←
    match layout with
    | some t => textTH t
    | none => pure (Fmt.zeroBytes 32, 0)
  pure { pol := p.1, polW := p.2, kl := k, klW := klWords KL, lay := l.1, layW := l.2 }

/-- One digest of the three: secondHashFunctionTree of the 27 words of a ParDigests in their order. -/
def hParOf (d : ParDigests) : Except String ByteArray :=
  match secondHashFunctionTree (d.pol ++ word32 d.polW ++ d.kl ++ word32 d.klW ++ d.lay ++ word32 d.layW) with
  | some x => pure x
  | none => .error "internal-th"

/-- The digest of the three configuration files that the verifier prints as h_par=. It is compared
with nothing: what a proof's chains bind is another digest of the same files, printed as
configuration=. -/
def hPar (pol KL : ByteArray) (layout : Option ByteArray) : Except String ByteArray := do
  hParOf (← parDigests pol KL layout)

/-- A digest of the second hash function as the C++ verifier prints it: word by word, each 32-bit
word as eight hex digits with the highest first. This is not the hex of the bytes in their order. -/
def hex64 (d : ByteArray) : String :=
  String.join ((List.range (d.size / 4)).map fun i =>
    Fmt.hex ⟨#[3, 2, 1, 0].map fun j => Fmt.byteAt d (4 * i + j)⟩)

/-! ## The acceptance policies -/

/-- True for the strictest policy: C = theta = 2^sh with sh below 63, cap = 0 and sT = sh - 4. A
proof under it says that each checked token is the model's first choice at its position: the token
with the largest logit, and of several such tokens the one with the lowest number (by the definition
of a token's cost, verifier/docs/parameter-file.md, section 8; nothing in this file tests it). With
other values an accepted proof can say less, and with some it says nothing: if theta = C and cap is
the number of checked tokens, every sequence of tokens passes. -/
def exactMatch (C theta cap sh sT : Nat) : Bool :=
  decide (sh < 63) && C == theta && cap == 0 && sT + 4 == sh && theta == 2 ^ sh

/-- The name of the policy's kind, one of four. Where sT = sh - 4 a token's cost is 2^sh plus its
logit gap: exact-match if the lines are those of exactMatch, else clipped-gap. For every other sT
the cost also counts a negative log-probability at the scale 2^sT: log-probability if sT equals the
line s, else another-table. The line s is the provider's statement of the scale of the model's
logits, and no test compares it with the model. So log-probability is only a name for sT = s: that
scale is the scale of the model's logits only if the provider's s is right. -/
def policyKind (C theta cap s sh sT : Nat) : String :=
  if exactMatch C theta cap sh sT then "exact-match"
  else if sT + 4 == sh then "clipped-gap"
  else if sT == s then "log-probability"
  else "another-table"

/-- How many of n checked tokens can at most have a cost above the clip C. n counts tokens of the
request; the reply's token, which follows the window, is not among them. The policy allows cap
tokens above the clip. It also bounds the sum of the clipped costs by theta n, and a cost is never
below 2^sh, so k tokens above the clip need k (C - 2^sh) ≤ n (theta - 2^sh). The result is the
smaller bound. For sh ≥ 63 the least cost counts as 2^64 - 1. A token above the clip can be any
token. The result does not bound how many tokens can be any token: what a cost of at most C rules
out depends on the model's logits, which the verifier does not see. By the C++ comment
(verifier/src/vf_common.h, aboveClip) the bound is attained for every model where sT = sh - 4, if
the lines admit a proof at all: that many of the checked tokens may be arbitrary if all the other
checked tokens are the model's first choices, which cost 2^sh each. -/
def aboveClip (n C theta cap sh : Nat) : Nat :=
  let least := if sh < 63 then 2 ^ sh else 2 ^ 64 - 1
  let k := min cap n
  if C ≤ least then k
  else min (if least < theta then n * (theta - least) / (C - least) else 0) k

/-- Finds, from the numbers alone, a named policy under which a result would mean nothing. n: the
number of checked tokens of the request, without the reply's token. A token's cost is at least 2^sh.
1: C is below 2^sh, so every token counts as C, whatever its cost. 2: theta is below 2^sh, so no
request can meet it. 3: theta is above C, which no parameter file may set. 4: theta = C and 0 < n ≤
cap, so no token is ruled out. 0: none of these. A policy at 0 can still let every token through. -/
def policyEmpty (n C theta cap sh : Nat) : Nat :=
  let least := if sh < 63 then 2 ^ sh else 2 ^ 64 - 1
  if C < least then 1
  else if theta < least then 2
  else if C < theta then 3
  else if theta == C && n != 0 && decide (n ≤ cap) then 4
  else 0

/-- A policy as a caller spells it on the command line, to say which policy it expects: the kind
exact-match or clipped-gap, and the values of five lines. With the kind these fix the line sT
(sh - 4). The seventh line, F, is not named: only 24 is admitted (policy-gap-words,
OnBytes/Model/HeadLayout.lean). -/
structure PolicyNamed where
  /-- exact-match or clipped-gap -/
  kind : String
  /-- the line C -/
  C : Nat
  /-- the line theta -/
  theta : Nat
  /-- the line cap -/
  cap : Nat
  /-- the line s -/
  s : Nat
  /-- the line sh -/
  sh : Nat
  deriving DecidableEq, Repr, Inhabited

/-- True if the parameter file's lines set the policy that the caller names. -/
def PolicyNamed.is (p : PolicyNamed) (fC fTheta fCap fS fSh fST : Nat) : Bool :=
  p.kind == policyKind fC fTheta fCap fS fSh fST && p.C == fC && p.theta == fTheta &&
  p.cap == fCap && p.s == fS && p.sh == fSh

/-- The number that one to ten digits without a leading zero spell; 0 itself is allowed. none for
every other text. -/
def numeral10 (t : String) : Option Nat :=
  let l := bytesOf t
  if l.isEmpty || decide (10 < l.length) || !l.all isDigit ||
      (l.head? == some 0x30 && decide (1 < l.length)) then none
  else some (digitsValue l)

/-- Reads a named policy: the kind and five numbers, with commas and no spaces between them. -/
def policyNamedRead (text : String) : Option PolicyNamed :=
  match text.splitOn "," with
  | [kind, a, b, c, d, e] =>
    if ["exact-match", "clipped-gap"].contains kind then
      match numeral10 a, numeral10 b, numeral10 c, numeral10 d, numeral10 e with
      | some C, some theta, some cap, some s, some sh => some ⟨kind, C, theta, cap, s, sh⟩
      | _, _, _, _, _ => none
    else none
  | _ => none

/-- True if theta0 is 10000 or 500000, dh ≤ 128 and lt ≤ 10: the C++ verifier's condition
rotary-table on the three numbers that determine the rotary table (rotaryServed,
vf_common.h). The C++ verifier computes that table with C library functions. A comment in
runStage (verifier/src/cp_verify.cpp) says that the condition admits the values at which every entry
is far from a rounding tie; this has not been shown (see verifier/docs/parameter-file.md). It is
one of the conditions without which the C++ verifier ends a run at best with the words that it is no
verification. It is tested at profile 4 only. Below profile 4 it counts as met, although, as the
same comment notes, the layers rotate queries and keys at every profile. -/
def rotaryServed (theta0 dh lt : Nat) : Bool :=
  (theta0 == 10000 || theta0 == 500000) && decide (dh ≤ 128) && decide (lt ≤ 10)

end OnBytes.Model
