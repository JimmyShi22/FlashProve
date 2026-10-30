-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1All.lean: the verifier's decision for the first toy (a product test), all blocks put together:
`dec : Par → Fmt.View → Bool`.

The first toy is a test protocol for the claim that three rows a, b, c of one oracle message have
a_i b_i = c_i for every i (the heads of Fmt/M1Types.lean and Fmt/M1Psc.lean). This file gives the
verifier's decision, accept or refuse, as one function of the sizes and of the view of a transcript.
Definitions that compute, with tests (#guard) on sizes. Core Lean; total; generic in the sizes.

Main names:
  `blocks`: the six functions of the blocks:
      `sampleRow` (Fmt/M1Send.lean): the sample row;
      `pscBlock` (Fmt/M1Psc.lean): ZERO (the zero-check) and the sum-check's three rows;
      `foldStep`, `baseOK` (Fmt/M1Fold.lean): a fold, and the last block;
      `csStep`, `csFits` (Fmt/M1Cs.lean): the code switch, with its test on sizes.
  `decM P V`: the pass through all blocks (`decWith`, Fmt/M1Dec.lean) at these blocks, on the toy's
    own view (`View`, Fmt/M1Types.lean).
  `toyPar` (Fmt/M1Plan.lean): the full parameters: the six codes (Fmt/M1Codes.lean: `Full`) were
    inferred and are confirmed, all six, by an answer to questions about the programs
    (the C++ implementation that comes with this Lean code; read off a run of theirs, and
    by a second verifier of theirs).
  `tinyPar` (Fmt/M1Plan.lean): sizes of this library's own for trials (K = 4). The rows a, b, c
  have 2^K
    entries (`Par`, Fmt/M1Types.lean).
  `parTiny2`: K = 2.
  `parTheirTiny`: the programs' own tiny parameters, by an answer (K = 4; codes (7, 16, 3),
    (8, 8, 3), (9, 8, 5); mask codes (7, 16, 3), (8, 32, 3), (9, 128, 5); 3, 3, 5 positions; 6 bits
    of work). A code is a triple (a, l, r): codewords of length 2^a, messages of l entries, a tail
    of r entries (`Code`, Fmt/M1Codes.lean).

Tests:
  All four sets of sizes meet the test on sizes of Fmt/M1Dec.lean (`stagesOK`).
  At the full parameters: thirty rounds, and 229 and 290 entries that fill the later stages' mask
    rows up (`fillOf`).
  At `parTiny2`: twenty rounds.
  At `tinyPar`: a view without rounds is refused.
  The room for a fold's hiding polynomial is a clause of its own in `stagesOK` (`hideFits`,
    Fmt/M1Dec.lean: h + 2 (k - h) + 1 entries in a mask row). Made-up sizes with a second stage at
    k = h = 4 fit with mask rows of 8 places. With 4 places they do not fit: there the blocks' own
    test between neighbouring stages (`fitsAll`) still holds, and `hideFits` fails at that stage.
  At their tiny parameters this library's functions of the sizes give the numbers that the answer
  prints: 22
    rounds; seeds of 8, 8, 9 elements; 11 rows under each switch; 146 elements (3,504 bytes) in the
    clear; 23 and 55 entries that fill the later stages' mask rows up.

The code switch that `dec` runs (Fmt/M1Cs.lean: `csStep`) is a faster twin of the one that is
written as the text lists it (`csStepLit`: all rows, then their sum under the powers of theta): that
the two give the same values is a theorem, for all arguments: Fmt/M1CsEq.lean (`csStep_eq`); tests
at three tiny shapes are in Fmt/M1Cs.lean.

`dec` tests (D4) and (D5), labels of a wording of the programs' description not held against it as
it ships, for parts of a verifier's check, on the claim that all blocks before have moved. (D4) is
the last block's linear check, (D5) its checks at the drawn positions (`baseOK`, Fmt/M1Fold.lean).

Notation: sizes ⟨fld, K, stages, work, salt⟩: the fields of `Par` (Fmt/M1Types.lean); `.two`: field
2, `Fld.two`, one of the format's two fields (`Fld`, Fmt/Rules1.lean); a stage ⟨C, Z, k, h, t⟩: the
fields of `Stage` (Fmt/M1Types.lean).

Limits:
  `dec` does not test (D1) form, (D2) work, (D3) openings. These are the reader's and the compiled
    verifier's (the five labels in words: the head of Fmt/M1Types.lean).
  That an honest run is accepted and an altered one refused is not shown in this file: the prover
    of this library's own at tiny sizes is another file's (Fmt/M1Own.lean).
  That `dec` is what the programs decide: no theorem says it.
  This file's sources include no proof file of theirs; of their numbers only sizes, parameters and
    first values.
  The programs' own honest and false proof files have gone through `dec`, behind the readers (their
    altered ones: the next limit): the verdicts on their honest, altered and false files
    (Fmt/M1FullProg*.lean; before the compiled verifier: Run/M1Engine*.lean) and the nineteen
    intermediate values that they print (computed in Lean by `targets`, which walks the rounds by a
    copy of the steps of `decWith` and is not `dec` itself: Fmt/M1Targets.lean; compared in
    Fmt/M1FullProgPTv.lean, M1FullProgPRv.lean, M1FullProgPFv.lean) agree: tests when these files
    compile, no theorem.
  In Fmt/ and Run/ no altered file of theirs is shown to reach `dec`. In Fmt/M1FullProg*.lean the
    reader refuses each of them, before `dec` is run (`whoF`, Fmt/M1Full.lean). An outcome in
    Run/M1Engine*.lean does not tell which check of the compiled verifier failed.
  (By an answer a second verifier of theirs, written from the same text that was available for this
    library, gives their programs' numbers.)

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Dec
import Fmt.M1Send
import Fmt.M1Psc
import Fmt.M1Fold
import Fmt.M1Cs
import Fmt.M1Plan

namespace Fmt.M1

/-- The six functions of the blocks (the fields of `Blocks`, Fmt/M1Dec.lean). -/
def blocks : Blocks := ⟨sampleRow, pscBlock, foldStep, csFits, csStep, baseOK⟩

def decM (P : Par) (V : View) : Bool := decWith blocks P V

/-- The decision: `decM` on the general untyped view of a transcript (Fmt/View.lean). -/
def dec (P : Par) (V : _root_.Fmt.View) : Bool := decWith blocks P (ofView V)

/-- sizes of this library's own for trials (K = 2; the same term as `parTiny2`; not `tinyPar` of
Fmt/M1Plan.lean) -/
def parTiny : Par :=
  ⟨.two, 2,
    [⟨⟨6, 4, 2⟩, ⟨6, 16, 2⟩, 2, 0, 2⟩, ⟨⟨7, 2, 2⟩, ⟨7, 32, 2⟩, 1, 1, 2⟩,
      ⟨⟨9, 2, 2⟩, ⟨9, 128, 2⟩, 0, 0, 2⟩],
    0, 40⟩

/-- small sizes of this library's own (K = 2) -/
def parTiny2 : Par :=
  ⟨.two, 2,
    [⟨⟨6, 4, 2⟩, ⟨6, 16, 2⟩, 2, 0, 2⟩, ⟨⟨7, 2, 2⟩, ⟨7, 32, 2⟩, 1, 1, 2⟩,
      ⟨⟨9, 2, 2⟩, ⟨9, 128, 2⟩, 0, 0, 2⟩],
    0, 40⟩

/-- the programs' own tiny parameters, by an answer (the head, `parTheirTiny`) -/
def parTheirTiny : Par :=
  ⟨.two, 4,
    [⟨⟨7, 16, 3⟩, ⟨7, 16, 3⟩, 2, 0, 3⟩, ⟨⟨8, 8, 3⟩, ⟨8, 32, 3⟩, 1, 1, 3⟩,
      ⟨⟨9, 8, 5⟩, ⟨9, 128, 5⟩, 0, 0, 5⟩],
    6, 40⟩

/-- the entries that fill a later stage's mask rows up, the pad among them -/
def fillOf (prev s : Stage) : Nat := 2 ^ s.h * s.Z.l - (2 * prev.Z.l + prev.C.r + 2 * prev.Z.r)

#guard stagesOK blocks parTheirTiny
#guard nRounds parTheirTiny == 22
#guard parTheirTiny.stages.map (fun s => s.na + 1) == [8, 8, 9]
#guard parTheirTiny.stages.dropLast.map (fun s => nRows s.t) == [11, 11]
#guard (parTheirTiny.stages.getLast?.map fun s => s.C.l + s.Z.l + s.C.r + s.Z.r) == some 146
#guard (parTheirTiny.stages.zip (parTheirTiny.stages.drop 1)).map (fun x => fillOf x.1 x.2) == [23, 55]
#guard (toyPar.stages.zip (toyPar.stages.drop 1)).map (fun x => fillOf x.1 x.2) == [229, 290]
#guard stagesOK blocks toyPar
#guard stagesOK blocks tinyPar
#guard stagesOK blocks parTiny2
-- the room for a hiding polynomial's public vector (hideFits) is a clause of its own: sizes with a
-- second stage at k = h = 4 (five entries): with mask rows of 8 places the sizes fit; with 4 they
-- do not, though every other clause holds (the blocks' own test between neighbours among them)
#guard stagesOK blocks ⟨.two, 4, [⟨⟨9, 16, 3⟩, ⟨9, 16, 3⟩, 2, 0, 3⟩, ⟨⟨9, 1, 3⟩, ⟨9, 8, 3⟩, 4, 4, 3⟩, ⟨⟨10, 1, 3⟩, ⟨10, 32, 3⟩, 0, 0, 3⟩], 4, 40⟩ &&
  !stagesOK blocks ⟨.two, 4, [⟨⟨9, 16, 3⟩, ⟨9, 16, 3⟩, 2, 0, 3⟩, ⟨⟨9, 1, 3⟩, ⟨9, 4, 3⟩, 4, 4, 3⟩, ⟨⟨10, 1, 3⟩, ⟨10, 32, 3⟩, 0, 0, 3⟩], 4, 40⟩ &&
  fitsAll blocks [⟨⟨9, 16, 3⟩, ⟨9, 16, 3⟩, 2, 0, 3⟩, ⟨⟨9, 1, 3⟩, ⟨9, 4, 3⟩, 4, 4, 3⟩, ⟨⟨10, 1, 3⟩, ⟨10, 32, 3⟩, 0, 0, 3⟩] &&
  [(⟨⟨9, 16, 3⟩, ⟨9, 16, 3⟩, 2, 0, 3⟩ : Stage), ⟨⟨9, 1, 3⟩, ⟨9, 4, 3⟩, 4, 4, 3⟩].map hideFits == [true, false]
#guard nRounds toyPar == 30
#guard nRounds parTiny2 == 20
#guard decM tinyPar ⟨[], []⟩ == false
#guard dec tinyPar ⟨[], []⟩ == false

end Fmt.M1
