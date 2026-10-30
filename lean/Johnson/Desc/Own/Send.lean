-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Send.lean: the three makers of an out-of-domain sample (the places of the pad, the
left side of a sample row, the seeds cut out of what a round drew), as a named part of the
description, for every block that sends or admits a sampled oracle message.

Definitions with code; no theorem here.
Main names:
  `padMade codes s`: the places of the pad of an oracle message of the shape s, by increasing index:
    for each answer one place (three where the pad lies in main rows over the base field), at the
    end of the last row of the mask table, or of the main table where the message has no mask row.
  `formMade codes s o seed answer`: the left side of the sample row of the message number o for one
    answer: the equality vector at the seed's point on every entry that is no pad, the seed's factor
    times the basis on the pad of this answer, 0 on the pads of the other answers.
  `seedsMade bits n l`: the elements l that a round of seeds has drawn, cut into n seeds, each of
    `bits` coordinates and a factor.
Every place at which one of them returns nothing, and what that refusal checks:
  padMade, one place: the row that takes the pad has fewer places than the pad needs. It checks that
    the message length of the code of that row is at least the number of answers (three times that
    number where the pad lies in main rows over the base field): padMade_isSome_iff,
    Johnson/Desc/Own/SendAgree.lean. The same test by itself is `padFits`
    (Johnson/Top/H0/Tw/K2/Target.lean).
  formMade, one place: padMade returns nothing. It checks the same, and nothing else: it does not
    test that the seed's point has as many coordinates as the cube, nor that the seed's factor is
    not 0.
  seedsMade, two places: no seed is left to cut and an element is left over; or a seed is to be cut
    and at most `bits` elements are left. Together they check that l has exactly n * (bits + 1)
    elements (seedsMade_length, Johnson/Desc/Own/SendAgree.lean).
How far the text is its own: it is the hand-written program's Send.pad, Send.form and Send.seedsOf
(OnBytes/Iop/Send.lean) taken over token for token under new names, formMade calling padMade where
Send.form calls Send.pad. It adds no second, independent eye on what these makers should make. The
three older names are called nowhere.
What is taken from the hand-written program's files: the records Codes, Code, OracleShape,
SampleCube, PadPlace, SampleSeed, Row and Tensor with their fields, the types Part and E, and
functions that always return: Send.cube, Send.front, Tensor.eq, Tensor.entry, Row.addUnit, Row.add,
thetaE, mulE, subE, zeroE. No function of these files that says yes or no, or that may return
nothing, is called.
That the three are the program's, at all arguments, is proved beside, in
Johnson/Desc/Own/SendAgree.lean, which no block imports.
Limits: Whether these makers make what a sample needs is not said here. No soundness is claimed, and
nothing is said on hiding.

-/
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- The places of the pad, by increasing index. Nothing if the row is too short for the pad. -/
def padMade (codes : Codes) (s : OracleShape) : Option (List PadPlace) :=
  let c := Send.cube codes s
  let part : Part := if c.hasMask then .mask else .main
  let rows := if c.hasMask then s.maskRows else s.mainRows
  let rowBits := if c.hasMask then c.maskRowBits else c.mainRowBits
  let len :=
    if c.hasMask then (codes.mask.getD s.maskCode default).ell
    else (codes.base.getD s.code default).ell
  let each := if c.hasMask || s.mainDeg == 3 then 1 else 3
  if len < each * s.answers then none
  else
    some ((List.range s.answers).flatMap fun i =>
      (List.range each).map fun t =>
        let place := len - each * s.answers + each * i + t
        { part := part, index := (rows - 1) + place * 2 ^ rowBits, answer := i,
          basis := thetaE t })

/-- The left side of the sample row of o for one answer. Nothing if the pad has no room. -/
def formMade (codes : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed) (answer : Nat) :
    Option Row := do
  let c := Send.cube codes s
  let places ← padMade codes s
  let onMain := Tensor.eq (seed.z.take c.mainBits) (Send.front seed.z c c.mainBits false)
  let onMask := Tensor.eq (seed.z.take c.maskBits) (Send.front seed.z c c.maskBits true)
  let row0 : Row := places.foldl (fun (r : Row) p =>
    let underZ := (if p.part == .main then onMain else onMask).entry p.index
    r.addUnit o p.part p.index
      (subE (if p.answer == answer then mulE seed.beta p.basis else zeroE) underZ))
    { kind := .sample }
  let row1 := if c.hasMain then row0.add o .main onMain else row0
  pure (if c.hasMask then row1.add o .mask onMask else row1)

/-- The drawn elements cut into n seeds. Nothing unless there are exactly n (bits + 1) elements. -/
def seedsMade (bits : Nat) : Nat → List E → Option (List SampleSeed)
  | 0, [] => some []
  | 0, _ :: _ => none
  | n + 1, l =>
    match l.drop bits with
    | [] => none
    | beta :: rest => (seedsMade bits n rest).map fun t => ⟨l.take bits, beta⟩ :: t

end VerifiableInference.Desc.Own
