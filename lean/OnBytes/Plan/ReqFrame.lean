-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/ReqFrame.lean: from the arrays that the sub-proofs declare and a layout file to the
links of a request and their layout.

A request's proof is a chain of links, one for each sub-proof (OnBytes/Iop/Req.lean). A moment of a
link is one of the prover's messages in which oracle messages of the link go out. A sub-proof
declares, moment by moment, the arrays that it commits to. A layout file says into which oracle
messages they go and where each element lies. Both sides read the file.

The file. Lines of numbers and single letters, separated by blanks. A line that begins with # is
skipped, and so is a line that holds only blanks, tabs and carriage returns. Links, moments and
groups are counted from 1; arrays, rows and places from 0.
   a group:   link moment group class rows life
   a block:   link moment group array R a K e low row place br bj 0
A group is one oracle message of that moment of that link. (This is the file's word. Elsewhere in
this directory a group is a set of oracle messages that are tested together.) Class N: rows over the
base field. Class B: rows over the base field that are kept for "life" later links, up to their last
reader. Class W: rows over the extension field. Groups come in the order link, moment, group.
A block holds the elements (R + i, K + c), i < 2^a, c < 2^e, of an array, which is named by its
number among the arrays of its moment. Element number x = c 2^a + i (low = r) or i 2^e + c (low = c)
lies in row "row" + x / 2^bj of the group, at place "place" + x mod 2^bj. So a block takes 2^br
rows, with br + bj = a + e; that equation is tested with the layout (reqLayoutOk), not here. The
last number must be 0.
The mask row of a link has no line: it belongs to the first oracle message of the link's first
moment.

How a line is read. The C++ programs read a line with the C library's formatted scan, and this
file follows that routine's ways, since both sides must accept the same files. Before every number
and letter, white space is skipped (blank, tab, line feed, vertical tab, form feed, carriage
return). A number may have a sign and leading zeros and ends before the first byte that is no
digit. A number with a minus sign is taken from 2^64; a number of 2^64 or more counts as 2^64 - 1.
A letter is any one byte. A line ends at its first zero byte. A line is a block's if 14 items can
be read and nothing but white space follows; else it is a group's if the same holds with 6 items.

Main definitions: scanLine, LayoutGroup, LayoutBlock, LayoutLines, layoutRead, reqFrame.
C++ counterpart: layout_read() and req_frame() in blocks/frame/req_frame.h.

Not claimed here: a layout that passes here is still to be tested against the codes and against
itself, by reqOk (OnBytes/Iop/Req.lean) and reqLayoutOk (OnBytes/Iop/ReqRows.lean).
-/
import OnBytes.Params.Items
import OnBytes.Model.StagesLinks

namespace OnBytes.Plan

open OnBytes.Params
open OnBytes.Model.Stages (FrameArray FrameLink)

/-! ## Reading a line -/

/-- White space, as the C library's scan has it. -/
def isSpace (c : UInt8) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

/-- A decimal digit. -/
def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- What is asked for next: a number, or a single byte. -/
inductive Ask where
  | number
  | letter
  deriving DecidableEq, Repr

/-- Reads the decimal digits at the head of a list. Returns their value, continued from v (each
digit turns v into 10 v + digit), their number added to n, and what follows them. A value of 2^64
or more is returned as 2^64: the callers ask no more of such a value than that it is that large, and
a numeral of very many digits then costs no more than its length. -/
def digits : List UInt8 → Nat → Nat → Nat × Nat × List UInt8
  | c :: l, v, n =>
    if isDigit c then digits l (min (2 ^ 64) (10 * v + (c.toNat - 48))) (n + 1) else (v, n, c :: l)
  | [], v, n => (v, n, [])

/-- A number at the head of a list that does not begin with white space: its value as a word of 64
bits, and what follows. Nothing if there is no digit after the sign, or none at all. -/
def scanNumber (l : List UInt8) : Option (Nat × List UInt8) :=
  let minus := l.head? == some 45
  let x := digits (if minus || l.head? == some 43 then l.drop 1 else l) 0 0
  if x.2.1 == 0 then none
  else if 2 ^ 64 ≤ x.1 then some (2 ^ 64 - 1, x.2.2)
  else some (if minus then (2 ^ 64 - x.1) % 2 ^ 64 else x.1, x.2.2)

/-- Reads the items that are asked for, one after the other, and stops at the first that cannot be
read. A letter is returned as its byte's number. -/
def scanLine : List Ask → List UInt8 → List Nat
  | [], _ => []
  | a :: as, l =>
    let rest := l.dropWhile isSpace
    match a with
    | .number =>
      match scanNumber rest with
      | some x => x.1 :: scanLine as x.2
      | none => []
    | .letter =>
      match rest with
      | c :: t => c.toNat :: scanLine as t
      | [] => []

/-- What is asked of a block's line: 14 items, and one more byte, which must not be there. -/
def blockAsks : List Ask :=
  List.replicate 8 .number ++ [.letter] ++ List.replicate 5 .number ++ [.letter]

/-- What is asked of a group's line: 6 items, and one more byte, which must not be there. -/
def groupAsks : List Ask :=
  List.replicate 3 .number ++ [.letter, .number, .number, .letter]

/-! ## The lines of a file -/

/-- A group's line. Link, moment and group are counted from 0 here. -/
structure LayoutGroup where
  link : Nat
  moment : Nat
  group : Nat
  /-- the class: the byte N, B or W -/
  cls : Nat
  rows : Nat
  life : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A block's line. Link, moment and group are counted from 0 here. -/
structure LayoutBlock where
  link : Nat
  moment : Nat
  group : Nat
  array : Nat
  laid : LaidBlock
  deriving DecidableEq, Repr, Inhabited

/-- The lines of a layout file: the groups in their order, and the blocks in theirs. -/
structure LayoutLines where
  groups : List LayoutGroup := []
  blocks : List LayoutBlock := []
  deriving DecidableEq, Repr, Inhabited

/-- A number that is counted from 1 and lies below 2^20. -/
def counted (x : Nat) : Bool := x != 0 && decide (x < 2 ^ 20)

/-- One line that is neither blank nor a comment: a block, a group, or nothing. -/
def readLine (line : List UInt8) : Option (LayoutBlock ⊕ LayoutGroup) :=
  let text := line.takeWhile (· != 0)
  match scanLine blockAsks text with
  | [link, moment, group, array, R, a, K, e, c, row, place, br, bj, sj] =>
    if counted link && counted moment && counted group && decide (array < 2 ^ 20) &&
        (c == 114 || c == 99) && sj == 0 && decide (a < 48) && decide (e < 48) &&
        decide (br < 48) && decide (bj < 48) then
      some (.inl ⟨link - 1, moment - 1, group - 1, array,
        { firstI := R, firstC := K, firstRow := row, firstPlace := place, bitsI := a, bitsC := e,
          rowBits := br, placeBits := bj, iIsLow := c == 114 }⟩)
    else none
  | _ =>
    match scanLine groupAsks text with
    | [link, moment, group, c, rows, life] =>
      if counted link && counted moment && counted group && (c == 78 || c == 66 || c == 87) &&
          rows != 0 && decide (rows < 2 ^ 32) && decide (life < 2 ^ 20) &&
          ((life != 0) == (c == 66)) then
        some (.inr ⟨link - 1, moment - 1, group - 1, c, rows, life⟩)
      else none
    | _ => none

/-- The loop of linesOf. cur: the bytes of the line that is being read, the last one first. done:
the lines so far, the last one first. -/
def linesLoop : List UInt8 → List UInt8 → List (List UInt8) → List (List UInt8)
  | [], [], done => done.reverse
  | [], cur, done => (cur.reverse :: done).reverse
  | c :: l, cur, done =>
    if c == 10 then linesLoop l [] (cur.reverse :: done) else linesLoop l (c :: cur) done

/-- The lines of a text: the bytes between line feeds. After a last line feed there is no line. -/
def linesOf (text : List UInt8) : List (List UInt8) := linesLoop text [] []

/-- A line is skipped if it holds nothing but blanks, tabs and carriage returns, or begins
with #. -/
def skipped (line : List UInt8) : Bool :=
  (line.all fun c => c == 32 || c == 9 || c == 13) || line.head? == some 35

/-- Reads lines into groups and blocks, the last ones first. -/
def gatherLines : List (List UInt8) → LayoutLines → Option LayoutLines
  | [], out => some out
  | line :: rest, out =>
    if skipped line then gatherLines rest out
    else
      match readLine line with
      | some (.inl b) => gatherLines rest { out with blocks := b :: out.blocks }
      | some (.inr g) => gatherLines rest { out with groups := g :: out.groups }
      | none => none

/-- Reads a layout file. Nothing if a line is neither a group's nor a block's, or has a number
that is not admitted. -/
def layoutRead (text : ByteArray) : Option LayoutLines :=
  (gatherLines (linesOf text.toList) {}).map fun x => ⟨x.groups.reverse, x.blocks.reverse⟩

/-! ## The links and their layout -/

/-- What the reading of the groups carries along. -/
structure GroupsSoFar where
  /-- for each link its oracle messages so far -/
  sent : Array (Array ReqMessage)
  /-- by link, moment and group: the number of the oracle message in its link -/
  message : Array (Array (Array Nat))

/-- Takes one group's line in. Nothing if the link or the moment does not exist, if the groups of a
moment are not numbered in turn, if a moment comes after a later one of its link, or if the next
link has a group already. The first oracle message of a link holds the link's mask row and cannot be
kept, so a life there is refused. answers: how many answers every sample gets. The numbers of the
codes are left 0: the caller fills them in. -/
def takeGroup (links : Array FrameLink) (answers : Nat) (s : GroupsSoFar) (g : LayoutGroup) :
    Option GroupsSoFar := do
  let l ← links[g.link]?
  if l.moment.size ≤ g.moment then none
  -- Only numbers are kept of the link's messages so far, so that the arrays are changed in place.
  let count := (s.sent.getD g.link #[]).size
  let lastMoment := (s.sent.getD g.link #[]).back?.map (·.moment)
  if g.group != ((s.message.getD g.link #[]).getD g.moment #[]).size then none
  if lastMoment.any fun x => decide (g.moment < x) then none
  if !(s.sent.getD (g.link + 1) #[]).isEmpty then none
  if count == 0 && g.life != 0 then none
  let m : ReqMessage :=
    { shape :=
        { code := 0, mainRows := g.rows, mainDeg := if g.cls == 87 then 3 else 1,
          maskRows := if count == 0 then 1 else 0, maskCode := 0, answers := answers }
      leafClass := 0
      moment := g.moment
      life := g.life }
  pure
    { sent := s.sent.modify g.link (·.push m)
      message := s.message.modify g.link fun x => x.modify g.moment fun y => y.push count }

/-- What the reading of the blocks carries along. -/
structure BlocksSoFar where
  /-- for each link its arrays so far, each with its blocks the last one first -/
  layout : Array (Array ReqArray)
  /-- by link, moment and array: the array's number in its link's layout, if it has one yet -/
  array : Array (Array (Array (Option Nat)))

/-- Takes one block's line in. Nothing if its group or its array does not exist. All blocks of an
array lie in one group. At an array's first block the group's class and life are compared with what
the sub-proof declares: an array lies in rows over the extension field exactly if its elements are
in that field, and its group is kept for at least as many links as the array's last reader is on. -/
def takeBlock (links : Array FrameLink) (G : GroupsSoFar) (s : BlocksSoFar) (b : LayoutBlock) :
    Option BlocksSoFar := do
  let l ← links[b.link]?
  let declared ← l.moment[b.moment]?
  let message ← ((G.message.getD b.link #[]).getD b.moment #[])[b.group]?
  let a ← declared[b.array]?
  let known := ((s.array.getD b.link #[]).getD b.moment #[]).getD b.array none
  let here := s.layout.getD b.link #[]
  match known with
  | some place =>
    let x ← here[place]?
    if x.message != message then none
    pure { s with
      layout := s.layout.setIfInBounds b.link
        (here.setIfInBounds place { x with blocks := b.laid :: x.blocks }) }
  | none =>
    let holds ← (G.sent.getD b.link #[])[message]?
    if (holds.shape.mainDeg == 3) != a.overE then none
    if holds.life < a.life then none
    pure
      { layout := s.layout.setIfInBounds b.link
          (here.push ⟨a.name, message, a.rows, a.columns, [b.laid]⟩)
        array := s.array.modify b.link fun x => x.modify b.moment fun y =>
          y.setIfInBounds b.array (some here.size) }

/-- The links of a request, with the oracle messages of each, and the layout of their arrays.
answers: how many answers every sample gets. The numbers of the codes are left 0, and a link's plain
scalars too: they are the caller's. Nothing if the file does not fit what the sub-proofs declare, or
if a declared array has no block. -/
def reqFrame (links : Array FrameLink) (file : LayoutLines) (answers : Nat) :
    Option (List ReqLink × ReqLayout) := do
  let G ← file.groups.foldlM (takeGroup links answers)
    { sent := links.map fun _ => #[]
      message := links.map fun l => l.moment.map fun _ => #[] }
  let B ← file.blocks.foldlM (takeBlock links G)
    { layout := links.map fun _ => #[]
      array := links.map fun l => l.moment.map fun m => m.map fun _ => none }
  if !(B.array.all fun l => l.all fun m => m.all (·.isSome)) then none
  pure (G.sent.toList.map (fun m => ⟨0, m.toList⟩),
    ⟨B.layout.toList.map fun l => l.toList.map fun a => { a with blocks := a.blocks.reverse }⟩)

end OnBytes.Plan
