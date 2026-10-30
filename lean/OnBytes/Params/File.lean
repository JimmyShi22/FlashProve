-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/File.lean: the first 32 lines of the parameter file, read by one strict reader.

The parameter file is the first of the public files. It is a text of named numbers. Its first 32
lines, from `version` to `table`, fix what is free in the frame of the protocol: the target, the
bits of work, the shapes of the codes and the stages of each proximity test. What follows from
these has no line and is derived: the slack of a code, every number of positions, the random
coordinates of the groups' and stages' codes (the table's are a number of the line `table`), the
later stages' mask messages. This is meant to keep a file from asking for a list of positions that
is too short for its own target. What follows the line `table` belongs to the model and is handed
on unread.

The reader is strict: one order, one spelling. A line is a name and its values, separated by
single spaces and ended by a line feed. A value is a decimal number without sign or leading zero,
of at most 15 digits; the value of `version` is four characters. There is no blank line, no
comment and no carriage return. Two files that differ in a byte are two sets of parameters: every
byte enters the digest of the public files. The tests and their order are those of the C++ reader
(`read_parameters` in blocks/frame/parameters.h). So are the words of a refusal, except that the
C++ reader appends the number of the line, as in "parameter-range: sec (line 2)". cp_verify
takes the part before the colon, or before " (line" where there is no colon, as the refusal's
name and appends " (policy)".

Main definitions: `Lines`, `GroupLine`, `StageLine`, `Work`, `readLines`.
What is not claimed: that a file which is read meets its own target. Only shapes are tested here;
the sizing decides on the target (OnBytes/Params/Configure.lean).
-/
import OnBytes.Base

namespace OnBytes.Params

/-- One stage of a proximity test after the first, as a line `stages` gives it. -/
structure StageLine where
  /-- the stage has 2 ^ k main rows -/
  k : Nat
  /-- the stage has 2 ^ h mask rows -/
  h : Nat
  /-- the stage's code has length 2 ^ logN -/
  logN : Nat
  /-- the stage's mask code has length 2 ^ maskLogN -/
  maskLogN : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A group of oracle messages under one code, with the stages of the test on it. -/
structure GroupLine where
  /-- the code has length 2 ^ logN -/
  logN : Nat
  /-- a message has length 2 ^ logL -/
  logL : Nat
  /-- the mask code has length 2 ^ maskLogN -/
  maskLogN : Nat
  /-- a mask message has length 2 ^ maskLogL -/
  maskLogL : Nat
  /-- the further stages; the last has k = h = 0 -/
  stages : List StageLine
  deriving DecidableEq, Repr, Inhabited

/-- The bits of proof of work before a verifier's message, for one kind of round error, by the
part of the protocol to which the round belongs. -/
structure Work where
  /-- in a request's own rounds -/
  request : Nat
  /-- in a batch's shared rounds -/
  shared : Nat
  /-- in the committer's rounds -/
  once : Nat
  deriving DecidableEq, Repr, Inhabited

/-- What the first 32 lines of the parameter file say. -/
structure Lines where
  /-- every round's error times 2 ^ -work is at most 2 ^ -sec -/
  sec : Nat
  /-- how the integer m of the assumed closeness theorem up to the Johnson radius is read where
  the codes are sized: 1 as the theorem prints it, 2 the other way (`johnson` in
  OnBytes/Params/Distance.lean) -/
  reading : Nat
  /-- what combining the rows of an interleaved word costs: 1 nothing, 2 a factor of their number -/
  rowcost : Nat
  /-- the most requests in a batch. A power of two: the tree over a batch's seals has a power of
  two of places, and errors and random entries are sized for this many requests -/
  slots : Nat
  /-- the answers to each out-of-domain sample -/
  answers : Nat
  /-- work where a polynomial that is not zero may vanish at the challenge -/
  workField : Work
  /-- work where two members of a list may have the same sample -/
  workSample : Work
  /-- work where a combination of words may be close though the words are not -/
  workCloseness : Work
  /-- work where a far word may agree at all drawn positions -/
  workPositions : Work
  /-- work where a vector that is not small may have small images -/
  workSmallness : Work
  /-- the bytes of a leaf's salt: a multiple of 8, from 40 to 64 -/
  salt : Nat
  /-- the bytes in which a proof lists each drawn position; 0: it lists none -/
  listed : Nat
  /-- the group of a link of a request's chain -/
  link : GroupLine
  /-- the folded table, encoded anew, in a batch -/
  folded : GroupLine
  /-- the table times the equality vector of the shared point, in a batch. One linear claim reads
  this group and `folded`, and the mask message that splits it belongs to both groups: so both
  have one mask code -/
  omega : GroupLine
  /-- the oracle message of `omega` together with a request's own vector, in the request's test.
  Its main code is that of `omega` -/
  own : GroupLine
  /-- as `folded`, in the committer's files: the key's one-time test and an entry's link -/
  onceFolded : GroupLine
  /-- as `omega`, in the committer's files -/
  onceOmega : GroupLine
  /-- as `own`, in the committer's files -/
  onceOwn : GroupLine
  /-- the multiplicities of the lookups of the key's proof of the ranges, which is meant to show
  that the table's entries are in their ranges -/
  onceRanges : GroupLine
  /-- a part of a lookup of `onceRanges` reads 2 ^ rangesPart rows of the matrix. Smaller parts
  cost the committer less memory and make the key longer. Only the range 1 to 40 is tested here;
  a value that gives a lookup more than 256 parts is refused in OnBytes/Plan/Ranges.lean -/
  rangesPart : Nat
  /-- the committed table has 2 ^ tableRowsLog rows -/
  tableRowsLog : Nat
  /-- the code of the table's rows has length 2 ^ tableLogN, at most 2 ^ 32 -/
  tableLogN : Nat
  /-- the data coordinates of a row -/
  tableData : Nat
  /-- the random coordinates of a row -/
  tableRandom : Nat
  /-- the number of coordinates of the point that a batch shares; the tableRowsLog coordinates
  that fold the table's rows are among them -/
  blockLog : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## Lines and values -/

/-- The search of `cutAt`. `seen` holds the bytes passed so far, the last one first. -/
def cutAtFrom (c : UInt8) : List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | _, [] => none
  | seen, x :: t => if x == c then some (seen.reverse, t) else cutAtFrom c (x :: seen) t

/-- The bytes before the first byte c, and the bytes after it. Nothing if c does not occur. -/
def cutAt (c : UInt8) (l : List UInt8) : Option (List UInt8 × List UInt8) := cutAtFrom c [] l

/-- The walk of `pieces`. `done` holds the finished pieces and `piece` the bytes of the present
one, each the last first. -/
def piecesFrom : List (List UInt8) → List UInt8 → List UInt8 → List (List UInt8)
  | done, piece, [] => (piece.reverse :: done).reverse
  | done, piece, x :: t =>
    if x == 0x20 then piecesFrom (piece.reverse :: done) [] t else piecesFrom done (x :: piece) t

/-- The pieces between the spaces of a line. A line with n spaces has n + 1 pieces. -/
def pieces (l : List UInt8) : List (List UInt8) := piecesFrom [] [] l

/-- What is left of l after the prefix p. Nothing if l does not begin with p. -/
def behind : List UInt8 → List UInt8 → Option (List UInt8)
  | [], l => some l
  | _ :: _, [] => none
  | a :: p, b :: l => if a == b then behind p l else none

/-- A reader of the text that is left: it gives a value and the remaining text, or the name of a
refusal. -/
abbrev Reading : Type → Type := StateT (List UInt8) (Except String)

/-- Refuses under a name. -/
def refuse {α : Type} (why : String) : Reading α := fun _ => .error why

/-- Refuses under a name unless b is true. -/
def demand (b : Bool) (why : String) : Reading Unit := if b then pure () else refuse why

/-- The values of the next line. The line must begin with `head` and one space. `count` is the
number of values that it must have; nothing: one or more. -/
def words (head : String) (count : Option Nat) : Reading (List (List UInt8)) := fun t =>
  match cutAt 0x0A t with
  | none => .error ("parameter-line-missing: " ++ head)
  | some (l, rest) =>
    match behind (head.toUTF8.toList ++ [0x20]) l with
    | none => .error ("parameter-line-order: " ++ head)
    | some vs =>
      let v := pieces vs
      if v.any (·.isEmpty) then .error ("parameter-line-blanks: " ++ head)
      else if count.any (· != v.length) then .error ("parameter-line-values: " ++ head)
      else .ok (v, rest)

/-- The number that decimal digits spell. Nothing for an empty value, one of more than 15
characters, one with a leading zero, or one with a character that is no digit. The bound of 15 is
the C++ reader's: every value is then below 2 ^ 50, and there no sum or small multiple of values
leaves 64 bits. -/
def number (w : List UInt8) : Option Nat :=
  if w.isEmpty || decide (15 < w.length) || (w.head? == some 0x30 && decide (1 < w.length)) ||
      w.any (fun c => c < 0x30 || 0x39 < c) then none
  else some (w.foldl (fun x c => 10 * x + (c.toNat - 0x30)) 0)

/-- The walk of `allOf`. `seen` holds the values so far, the last one first. -/
def allOfFrom {α : Type} : List α → List (Option α) → Option (List α)
  | seen, [] => some seen.reverse
  | _, none :: _ => none
  | seen, some a :: l => allOfFrom (a :: seen) l

/-- All values of a list, or nothing if one is missing. -/
def allOf {α : Type} (l : List (Option α)) : Option (List α) := allOfFrom [] l

/-- The numbers of the next line. -/
def numbers (head : String) (count : Option Nat) : Reading (List Nat) := do
  let v ← words head count
  match allOf (v.map number) with
  | some l => pure l
  | none => refuse "parameter-number-spelling"

/-- The one number of the next line, which must lie from lo to hi. -/
def one (head : String) (lo hi : Nat) : Reading Nat := do
  match ← numbers head (some 1) with
  | [x] =>
    demand (decide (lo ≤ x) && decide (x ≤ hi)) ("parameter-range: " ++ head)
    pure x
  | _ => refuse ("parameter-line-values: " ++ head)

/-! ## The lines -/

/-- The version line. This program serves the one word H821: format 8; field 2, which is
p = 2 ^ 64 - 2 ^ 32 + 1; hash 1, which is BLAKE2b. The names of the refusals are those of
`version_refusal` (blocks/frame/version.h). -/
def versionLine : Reading Unit := do
  match ← words "version" (some 1) with
  | [[0x48, 0x38, 0x32, 0x31]] => pure ()
  | [[0x48, b, c, _]] =>
    if b == 0x47 || b == 0x37 then refuse "version-of-an-earlier-format"
    else if b == 0x38 && c != 0x32 then refuse "version-of-another-field"
    else if b == 0x38 then refuse "version-of-another-hash"
    else refuse "version-unknown"
  | _ => refuse "version-unknown"

/-- A line of work: three numbers of bits, each at most 58 (the C++ reader's reason: a nonce has
8 bytes) and below the target. -/
def workLine (head : String) (sec : Nat) : Reading Work := do
  match ← numbers head (some 3) with
  | [a, b, c] =>
    demand ([a, b, c].all fun w => decide (w ≤ 58) && decide (w < sec))
      ("parameter-range: " ++ head)
    pure ⟨a, b, c⟩
  | _ => refuse ("parameter-line-values: " ++ head)

/-- The longest code of a group with mask rows, as a logarithm. The bound on the closeness of a
repeated mask code needs the long domain to be one coset of a subgroup, so its length divides
p - 1 = 2 ^ 32 * (2 ^ 32 - 1). Beyond 2 ^ 32 a domain is a union of cosets. -/
def mostGroupLogN : Nat := 32

/-- The stages that the numbers of a line spell, four numbers for each stage. Nothing unless the
numbers come in fours, every stage has k ≤ 8, h ≤ k, logN ≤ `mostGroupLogN` and maskLogN ≤ logN, the
last stage has k = 0 and no other stage has. -/
def stagesOf : List Nat → Option (List StageLine)
  | [] => some []
  | k :: h :: n :: nz :: rest =>
    if decide (k ≤ 8) && decide (h ≤ k) && decide (n ≤ mostGroupLogN) && decide (nz ≤ n) &&
        (if rest.isEmpty then k == 0 else k != 0) then
      (stagesOf rest).map (⟨k, h, n, nz⟩ :: ·)
    else none
  | _ => none

/-- The two lines of a group: its shape and its stages. -/
def groupLines (name : String) : Reading GroupLine := do
  match ← numbers ("group " ++ name) (some 5) with
  | [j, n, l, nz, lz] =>
    demand ((j == 1) && decide (n ≤ mostGroupLogN) && decide (l < n) &&
      decide (nz ≤ n) && decide (lz < nz)) ("parameter-group-shape: " ++ name)
    let s ← numbers ("stages " ++ name) none
    demand (s.length % 4 == 0 && decide (s.length ≤ 32)) ("parameter-stages-count: " ++ name)
    match stagesOf s with
    | some st => pure ⟨n, l, nz, lz, st⟩
    | none => refuse ("parameter-stages-shape: " ++ name)
  | _ => refuse ("parameter-line-values: group " ++ name)

/-- True if x is a power of two. -/
def isPowerOfTwo (x : Nat) : Bool := x != 0 && x &&& (x - 1) == 0

/-- The 32 lines, in their order. Two tests compare groups. "parameter-own-code": `own` has the
main code of `omega`, since both hold the same oracle message. "parameter-one-mask-code": `folded`
has the mask code of `omega`, since one mask message belongs to both groups. Both tests are also
made on the committer's groups. -/
def lines : Reading Lines := do
  versionLine
  let sec ← one "sec" 1 256
  let reading ← one "reading" 1 2
  let rowcost ← one "rowcost" 1 2
  let slots ← one "slots" 1 (2 ^ 20)
  demand (isPowerOfTwo slots) "parameter-range: slots"
  let answers ← one "answers" 1 4
  let _ ← one "record" 1 1
  let wf ← workLine "work field" sec
  let ws ← workLine "work sample" sec
  let wc ← workLine "work closeness" sec
  let wp ← workLine "work positions" sec
  let wm ← workLine "work smallness" sec
  let salt ← one "salt" 40 64
  demand (salt % 8 == 0) "parameter-range: salt"
  let listed ← one "listed" 0 8
  let link ← groupLines "link"
  let folded ← groupLines "folded"
  let omega ← groupLines "omega"
  let own ← groupLines "own"
  let onceFolded ← groupLines "once-folded"
  let onceOmega ← groupLines "once-omega"
  let onceOwn ← groupLines "once-own"
  let onceRanges ← groupLines "once-ranges"
  let rangesPart ← one "ranges-part" 1 40
  demand (own.logN == omega.logN && own.logL == omega.logL && onceOwn.logN == onceOmega.logN &&
    onceOwn.logL == onceOmega.logL) "parameter-own-code"
  demand (folded.maskLogN == omega.maskLogN && folded.maskLogL == omega.maskLogL &&
    onceFolded.maskLogN == onceOmega.maskLogN && onceFolded.maskLogL == onceOmega.maskLogL)
    "parameter-one-mask-code"
  match ← numbers "table" (some 6) with
  | [b, n, i, m, e, w] =>
    -- As in the C++ reader, the table's code has at most 2 ^ 32 positions: its points are then one
    -- coset of a subgroup. This test stands alone and first: 2 ^ n is computed only for n ≤ 32
    demand (decide (n ≤ 32)) "parameter-table-shape"
    demand (decide (b ≤ 20) && i != 0 && decide (i + m < 2 ^ n) && (e == 0) &&
      decide (w ≤ 40) && decide (b ≤ w)) "parameter-table-shape"
    pure { sec, reading, rowcost, slots, answers, workField := wf, workSample := ws,
           workCloseness := wc, workPositions := wp, workSmallness := wm, salt, listed, link,
           folded, omega, own, onceFolded, onceOmega, onceOwn, onceRanges, rangesPart,
           tableRowsLog := b, tableLogN := n, tableData := i, tableRandom := m,
           blockLog := w }
  | _ => refuse "parameter-line-values: table"

/-- Reads the parameter file. Returns what its first 32 lines say and the bytes after them, or
the name of the first test that failed. -/
def readLines (file : ByteArray) : Except String (Lines × ByteArray) :=
  (lines file.toList).map fun x => (x.1, ⟨x.2.toArray⟩)

end OnBytes.Params
