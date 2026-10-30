-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ItemTests.lean: which values of four kinds of parameter items are read back as
they were spelled: tests with code. Definitions alone.

The four kinds are the items that a proof file's first chain has and a key file's chains have not:
"request's shape", "layout", "links' identifiers" and "pending rows". Their spellers are in
OnBytes/Params/Spell.lean, their readers in OnBytes/Params/Items.lean. The tests for the other kinds
are in Johnson/HB/LLHARD/KB9/ItemsOk.lean, and these are built on them.

Why tests are needed. A speller does not spell every value faithfully.
  * A number from 2 ^ 64 on is spelled modulo 2 ^ 64.
  * Of an oracle message of a link the speller writes neither the two codes nor the number of
    answers. The reader fills in those of the chain of links, or the word for "no code" where the
    message has no rows of that kind.
  * Where such a message has no main rows, the speller writes the degree 1.
  * Of the stages of the last proximity test the speller leaves out the first. The reader puts a
    stage in front that follows from the chain's two codes.
  * The reader refuses a degree other than 1 and 3, a message that is kept beyond the last link, and
    an array's name with a byte outside 0x20 to 0x7E.

  `wordsB`: a list of numbers. `blockB`, `arrayB`, `arraysB`, `layoutB`: the item "layout".
    `messageB`, `reqLinkB`, `keptB`, `reqB`: the item "request's shape". Each asks its parts' tests,
    and of a list that it has fewer than 2 ^ 64 members.
  `wordsOf`, `linksWords`: the numbers that the reader of a chain of links reads before it builds
    its value.

Limits. That a value which passes is read back as spelled is another file's. That a value which
fails is not read back so is said nowhere. Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.ItemsOk
import Fmt.ParamsReadLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.KB9 (wB stagesB noticeB)

/-- A list of numbers with the word of its length in front. -/
def wordsB (l : List Nat) : Bool := wB l.length && l.all wB

/-- A block of an array: eight numbers. -/
def blockB (b : LaidBlock) : Bool :=
  wB b.firstI && wB b.firstC && wB b.firstRow && wB b.firstPlace && wB b.bitsI && wB b.bitsC &&
    wB b.rowBits && wB b.placeBits

/-- An array: its name is within the format's rule for names and shorter than 2 ^ 64 bytes. -/
def arrayB (a : ReqArray) : Bool :=
  Fmt.nameFit a.name && wB a.message && wB a.sizeI && wB a.sizeC && wB a.blocks.length &&
    a.blocks.all blockB

/-- The arrays of one link. -/
def arraysB (l : List ReqArray) : Bool := wB l.length && l.all arrayB

/-- The item "layout". -/
def layoutB (y : ReqLayout) : Bool := wB y.link.length && y.link.all arraysB

/-- The six numbers of an oracle message of a link, in the order of the bytes. -/
def wordsOf (m : ReqMessage) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (m.shape.mainRows, m.shape.mainDeg, m.shape.maskRows, m.leafClass, m.moment, m.life)

/-- An oracle message of a link, under the two codes and the number of answers of its chain of
links: six numbers; what the reader demands of the degree; and the three fields that are not spelled
hold what the reader fills in. -/
def messageB (code maskCode answers : Nat) (m : ReqMessage) : Bool :=
  wB m.shape.mainRows && wB m.shape.mainDeg && wB m.shape.maskRows && wB m.leafClass &&
    wB m.moment && wB m.life && (m.shape.mainDeg == 1 || m.shape.mainDeg == 3) &&
    (m.shape.mainRows != 0 || m.shape.mainDeg == 1) &&
    m.shape.code == (if m.shape.mainRows == 0 then noId else code) &&
    m.shape.maskCode == (if m.shape.maskRows == 0 then noId else maskCode) &&
    m.shape.answers == answers

/-- A link of a request. -/
def reqLinkB (code maskCode answers : Nat) (l : ReqLink) : Bool :=
  wB l.plain && wB l.messages.length && l.messages.all (messageB code maskCode answers)

/-- What the reader of a chain of links reads of the links: for each its number of plain scalars and
its messages' numbers. -/
def linksWords (s : ReqShape) : List (Nat × List (Nat × Nat × Nat × Nat × Nat × Nat)) :=
  s.link.map fun l => (l.plain, l.messages.map wordsOf)

/-- No oracle message is kept beyond the last link: the reader's own demand, at `linksWords`. -/
def keptB (s : ReqShape) : Bool :=
  zipT (List.range (linksWords s).length) (linksWords s) |>.all fun x =>
    x.2.2.all fun m => decide (x.1 + m.2.2.2.2.2 < (linksWords s).length)

/-- The item "request's shape". The first stage of the last test is the one that the reader puts in
front. -/
def reqB (s : ReqShape) : Bool :=
  wB s.code && wB s.maskCode && wB s.link.length &&
    s.link.all (reqLinkB s.code s.maskCode s.answers) && wB s.atStart.length &&
    s.atStart.all noticeB && wB s.answers &&
    s.last.head? == some (⟨s.code, s.maskCode, 1, 0⟩ : IoppStage) && stagesB (s.last.drop 1) &&
    keptB s

end Johnson.AtFull.Made
