-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Spell.lean: the bytes of the parameter items.

OnBytes/Params/Items.lean reads the items of a chain's parameter bytes into records. This file goes
the other way: from a record to the item's bytes, as the format pages have them (rules R12.x to
R14.x; docs/format/README.md has the pages' index). It is used where the records are derived
from the public files and the bytes that are hashed must be formed (OnBytes/Params/Configure.lean).
The C++ counterpart of a record's function is the overload `public_bytes` beside the struct
(blocks/iop/).

Main definitions: `spellCodes`, `spellNotice`, `spellLin`, `spellLink`, `spellBinding`,
`spellRanges`, `spellReq`, `spellLayout`, `spellWords`.
What is not claimed here: that reading undoes spelling. OnBytes/Params/TestItems.lean tests it on
examples.
-/
import OnBytes.Params.Items

namespace OnBytes.Params

/-- A number as a word of eight bytes, the lowest first. A number from 2 ^ 64 on is spelled modulo
2 ^ 64. -/
def spellWord (n : Nat) : ByteArray := Fmt.u64n n

/-- Numbers as words, one after the other. -/
def spellRow (l : List Nat) : ByteArray := Fmt.cat (l.map spellWord)

/-- A list of words: the word of its length, then the words. -/
def spellWords (l : List Nat) : ByteArray := Fmt.list spellWord l

/-- A code: three words. -/
def spellCode (c : Code) : ByteArray := spellRow [c.logN, c.ell, c.r]

/-- The item "codes". -/
def spellCodes (c : Codes) : ByteArray :=
  Fmt.list spellCode c.base.toList ++ Fmt.list spellCode c.mask.toList

/-- An oracle message's shape: six words. One shape has one spelling: without main rows the word of
the code says "no code" and the degree is 1; without mask rows the word of the mask code says "no
code". -/
def spellShape (s : OracleShape) : ByteArray :=
  spellRow [if s.mainRows != 0 then s.code else noId, if s.maskRows != 0 then s.maskCode else noId,
    s.mainRows, if s.mainRows != 0 then s.mainDeg else 1, s.maskRows, s.answers]

/-- A notice: a shape and a class of leaves. -/
def spellNotice (n : OracleNotice) : ByteArray := spellShape n.shape ++ spellWord n.leafClass

/-- A stage: four words. -/
def spellStage (s : IoppStage) : ByteArray := spellRow [s.code, s.maskCode, s.k, s.h]

/-- A list of stages. -/
def spellStages (l : List IoppStage) : ByteArray := Fmt.list spellStage l

/-- The choices of a proximity test: one word. -/
def spellChoice (c : IoppChoice) : ByteArray := Fmt.bool c.masksRide

/-- A stored table's shape: six words. -/
def spellIndex (s : IndexShape) : ByteArray :=
  spellCode s.code ++ spellRow [s.v, s.answers, s.saltBytes]

/-- The shape of the step that folds a table's rows. -/
def spellFoldeq (S : FoldeqShape) : ByteArray :=
  spellIndex S.index ++ spellShape S.u ++ Fmt.bool S.rowsHigh ++ spellRow [S.leafClass, S.columns]

/-- The item "the test on the table". -/
def spellLin (S : LinShape) : ByteArray :=
  spellFoldeq S.fold ++ spellRow [S.kLo, S.matrixRows] ++ spellShape S.omega ++ spellShape S.w ++
    Fmt.bool S.omegaRowsHigh ++ Fmt.bool S.wRowsHigh ++ spellShape S.sharedSplit ++
    spellShape S.ownSplit ++
    spellRow [S.omegaLeafClass, S.sharedSplitLeafClass, S.wLeafClass, S.ownSplitLeafClass,
      S.sharedMaskCode, S.ownMaskCode] ++
    Fmt.bool S.masksAhead ++ spellStages S.testU ++ spellStages S.testOmega ++
    spellStages S.testOwn ++ spellStages S.testOwnOmega ++ spellChoice S.choice

/-- The item "the link". -/
def spellLink (S : LinkShape) : ByteArray :=
  spellIndex S.table ++ spellRow [S.columnsFirst, S.columnsFurther, S.code, S.maskCode, S.rows] ++
    Fmt.bool S.rowsHigh ++ spellWord S.leafClass ++ Fmt.bool S.masksAhead ++
    spellStages S.later ++ spellChoice S.choice

/-- The item "binding tree". -/
def spellBinding (s : LinBindingShape) : ByteArray := spellRow [s.logLeaves, s.saltBytes]

/-- A run: four words. -/
def spellRun (r : WfRun) : ByteArray := spellRow [r.firstPlace, r.firstRow, r.places, r.stride]

/-- A part of a lookup. -/
def spellPart (p : WfPart) : ByteArray := spellWord p.logPlaces ++ Fmt.list spellRun p.runs

/-- A lookup. -/
def spellLookup (l : WfLookup) : ByteArray :=
  spellRow [l.d, l.mu, l.live] ++ Fmt.list Fmt.elt l.digitWeight ++ Fmt.elt l.offset ++
    Fmt.elt l.paddingKey ++ Fmt.list spellPart l.parts ++ spellWords l.firstBound

/-- The item "ranges". -/
def spellRanges (x : WfPublic) : ByteArray :=
  Fmt.list spellLookup x.lookups ++ spellNotice x.message ++ spellWord x.messageId ++
    spellStages x.stages ++ spellChoice x.choice

/-- An oracle message of a link: six words. Its two codes and its answers are not spelled: they are
the chain's. That the copies equal the chain's numbers is not tested here: the program's callers ask
`reqOk` (OnBytes/Iop/Req.lean) first, as the C++ asks `req_shape_fault` (blocks/iop/req.h). -/
def spellReqMessage (m : ReqMessage) : ByteArray :=
  spellRow [m.shape.mainRows, if m.shape.mainRows != 0 then m.shape.mainDeg else 1,
    m.shape.maskRows, m.leafClass, m.moment, m.life]

/-- A link. -/
def spellReqLink (l : ReqLink) : ByteArray :=
  spellWord l.plain ++ Fmt.list spellReqMessage l.messages

/-- A chain of links. The first stage of the last test is not spelled, whatever the record holds
there: it follows from the chain's two codes. -/
def spellReq (s : ReqShape) : ByteArray :=
  spellRow [s.code, s.maskCode] ++ Fmt.list spellReqLink s.link ++ Fmt.list spellNotice s.atStart ++
    spellWord s.answers ++ spellStages (s.last.drop 1) ++ spellChoice s.choice

/-- A block of an array: nine words. -/
def spellBlock (b : LaidBlock) : ByteArray :=
  spellRow [b.firstI, b.firstC, b.firstRow, b.firstPlace, b.bitsI, b.bitsC, b.rowBits,
    b.placeBits] ++ Fmt.bool b.iIsLow

/-- An array of a link. -/
def spellArray (a : ReqArray) : ByteArray :=
  Fmt.textS a.name ++ spellRow [a.message, a.sizeI, a.sizeC] ++ Fmt.list spellBlock a.blocks

/-- The item "layout". -/
def spellLayout (l : ReqLayout) : ByteArray := Fmt.list (Fmt.list spellArray) l.link

end OnBytes.Params
