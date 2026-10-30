-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/ItemsOk.lean: WHICH VALUES OF A KEY FILE's PARAMETER ITEMS ARE READ BACK AS
THEY WERE SPELT: tests with code, one for each kind of value. Definitions alone. The closed facts at
the written sizes stand in Johnson/HB/LLHARD/KB9/ItemsFull.lean, so that this file imports the
format's and the planner's files alone.

Why. The spellers (OnBytes/Params/Spell.lean) do not spell every value faithfully. A number from 2 ^
64 on is spelt modulo 2 ^ 64. An oracle message's shape without main rows is spelt with "no code"
and the degree 1, whatever its fields hold; without mask rows with "no code" for the mask code. An
element of the field is refused by the reader from the modulus on. So "reading undoes spelling"
holds on a part of the values alone. These tests say which.

  `wB` a number below 2 ^ 64 · `eltB` an element below the modulus · `codeB`, `codesB`, `shapeB`,
    `noticeB`, `stageB`, `stagesB`, `indexB`, `foldeqB`, `linB`, `bindingB`, `runB`, `partB`,
    `lookupB`, `rangesB`: each asks its parts' tests, and of a list that it has fewer than 2 ^ 64
    members. `shapeB` asks besides what the reader `oracleShape` (OnBytes/Params/Items.lean)
    demands, and that the fields which the speller overwrites hold what it writes.
  `itemsB z`: the five items of a key's one-time chain at the sizes z.

Limits. Tests alone. That a value which passes is read back as spelt is
Johnson/HB/LLHARD/KB9/ItemsBack.lean's. Nothing on soundness.
-/
import OnBytes.Params.Spell
import OnBytes.Plan.KeyOneTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params OnBytes.Plan

/-- A number that a word of eight bytes holds. -/
def wB (n : Nat) : Bool := decide (n < 2 ^ 64)

/-- An element of the base field as the reader admits it. -/
def eltB (x : F) : Bool := decide (x.toNat < Fmt.Fld.two.p)

/-- A code: three words. -/
def codeB (c : Code) : Bool := wB c.logN && wB c.ell && wB c.r

/-- The codes: two lists with fewer than 2 ^ 64 members. -/
def codesB (c : Codes) : Bool :=
  wB c.base.toList.length && c.base.toList.all codeB && wB c.mask.toList.length &&
    c.mask.toList.all codeB

/-- Six words; what the reader demands; and the fields that the speller overwrites hold what it
writes. -/
def shapeB (s : OracleShape) : Bool :=
  wB s.code && wB s.maskCode && wB s.mainRows && wB s.mainDeg && wB s.maskRows && wB s.answers &&
    (s.mainDeg == 1 || s.mainDeg == 3) && (s.mainRows != 0 || (s.code == noId && s.mainDeg == 1)) &&
    (s.maskRows != 0 || s.maskCode == noId)

/-- A notice: its shape and a word. -/
def noticeB (n : OracleNotice) : Bool := shapeB n.shape && wB n.leafClass

/-- A stage: four words. -/
def stageB (s : IoppStage) : Bool := wB s.code && wB s.maskCode && wB s.k && wB s.h

/-- A list of stages. -/
def stagesB (l : List IoppStage) : Bool := wB l.length && l.all stageB

/-- A stored table's shape: a code and three words. -/
def indexB (s : IndexShape) : Bool := codeB s.code && wB s.v && wB s.answers && wB s.saltBytes

/-- The shape of the step that folds a table's rows. -/
def foldeqB (S : FoldeqShape) : Bool :=
  indexB S.index && shapeB S.u && wB S.leafClass && wB S.columns

/-- The item "the test on the table". -/
def linB (S : LinShape) : Bool :=
  foldeqB S.fold && wB S.kLo && wB S.matrixRows && shapeB S.omega && shapeB S.w &&
    shapeB S.sharedSplit && shapeB S.ownSplit && wB S.omegaLeafClass &&
    wB S.sharedSplitLeafClass && wB S.wLeafClass && wB S.ownSplitLeafClass &&
    wB S.sharedMaskCode && wB S.ownMaskCode && stagesB S.testU && stagesB S.testOmega &&
    stagesB S.testOwn && stagesB S.testOwnOmega

/-- The item "binding tree": two words. -/
def bindingB (s : LinBindingShape) : Bool := wB s.logLeaves && wB s.saltBytes

/-- A run: four words. -/
def runB (r : WfRun) : Bool := wB r.firstPlace && wB r.firstRow && wB r.places && wB r.stride

/-- A part of a lookup: a word and its runs. -/
def partB (p : WfPart) : Bool := wB p.logPlaces && wB p.runs.length && p.runs.all runB

/-- A lookup. -/
def lookupB (l : WfLookup) : Bool :=
  wB l.d && wB l.mu && wB l.live && wB l.digitWeight.length && l.digitWeight.all eltB &&
    eltB l.offset && eltB l.paddingKey && wB l.parts.length && l.parts.all partB &&
    wB l.firstBound.length && l.firstBound.all wB

/-- The item "ranges". -/
def rangesB (x : WfPublic) : Bool :=
  wB x.lookups.length && x.lookups.all lookupB && noticeB x.message && wB x.messageId &&
    stagesB x.stages

/-- **The five items of a key's one-time chain.** -/
def itemsB (z : KeySized) : Bool :=
  noticeB z.once.input && rangesB z.ranges.x && bindingB z.binding && codesB z.codes &&
    linB z.once.shape

end Johnson.KB9
