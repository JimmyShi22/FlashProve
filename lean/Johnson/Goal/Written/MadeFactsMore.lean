-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Written/MadeFactsMore.lean: three more closed facts at the sizes of the joined written
term (`writtenSized`, Johnson/Goal/Written/Made.lean). Each is the conclusion of a law on what the
planner makes (Johnson/Desc/Ok/SizedFitsNine.lean). These laws have a planner's yes as their
premise, and the written term is returned by no planner: so at the written term their conclusions
are asked again, as tests with code.

Definitions.
  `nineFitsB Z`: at all nine proximity tests of the three files the stages that the shape names are
    the stages for which the errors were computed, under the file's finished list of codes
    (`sizedFits`, OnBytes/Plan/Ranges.lean, at the nine triples of `nineFits`). The law:
    `configure_fits`.
  `rightTestB Z`: the key file's test on the table is the one-time test, and the proof file's is
    not. The law: `configure_rightTest`.
  `linkCodesB Z`: the two codes that the proof file's request names are those of its links' group.
    The law: `proofSized_linkCodes`.
  `moreTests Z`: the three, as a list.
Statements.
  `more_yes`: the three say yes at `writtenSized`.
  `nine_plant`: with one more row variable in the last priced stage of the entry file's test
    `nineFitsB` says no. `right_plant`: with the key file's test on the table said to be no one-time
    test `rightTestB` says no. `codes_plant`: with one more in a number of the code of the links'
    group `linkCodesB` says no. At each plant the two others of the three and the six tests on the
    sizes of Johnson/Goal/Written/MadeFacts.lean say yes.
  That the three files' sized tables are one (the law: `configure_oneTable`) is `oneSizedTableB`,
    among these six.
By evaluations in Lean's kernel (`decide +kernel`): all.

What of OnBytes/Model/ is used: nothing by name.

Limits. For the entry file's link no word of the sizes says which of the table's two distances its
price is computed at: that part of the condition on the right test is asked by nothing. At the three
plants the tests that read the plans are not stated again: they read of the sizes the line on slots,
the settings and the link's table's shape, which the plants leave (`plans_over`, MadeFacts.lean).
Nothing on soundness.
-/
import Johnson.Goal.Written.MadeFacts
import Johnson.Desc.Ok.SizedFitsNine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.Joined
open VerifiableInference.PlanWritten.Mixed
open OnBytes OnBytes.Params OnBytes.Plan Johnson.Desc.Ok

/-- At all nine proximity tests the shape's stages are the priced stages. -/
def nineFitsB (Z : Sized) : Bool := (nineFits Z).all fun p => sizedFits p.1 p.2.1 p.2.2

/-- The key file's test on the table is the one-time test; the proof file's is not. -/
def rightTestB (Z : Sized) : Bool :=
  Z.key.once.lines.oneTime && !Z.proof.batch.lines.oneTime

/-- The two codes that the proof file's request names are those of its links' group. -/
def linkCodesB (Z : Sized) : Bool :=
  decide (Z.proof.codes.base[Z.proof.request.code]? =
      some ⟨Z.proof.link.group.main.logN, Z.proof.link.group.main.ell,
        Z.proof.link.group.main.r⟩) &&
    decide (Z.proof.codes.mask[Z.proof.request.maskCode]? =
      some ⟨Z.proof.link.group.mask.logN, Z.proof.link.group.mask.ell,
        Z.proof.link.group.mask.r⟩)

/-- The three, as a list. -/
def moreTests (Z : Sized) : List Bool := [nineFitsB Z, rightTestB Z, linkCodesB Z]

/-- **The three say yes at the written sizes.** -/
theorem more_yes : moreTests writtenSized = [true, true, true] := by decide +kernel

/-- The stages with f at the last. -/
def atLast (f : StageSize → StageSize) : List StageSize → List StageSize
  | [] => []
  | [y] => [f y]
  | y :: ys => y :: atLast f ys

/-- The sizes with one more row variable in the last priced stage of the entry file's test. -/
def nineBent : Sized :=
  { writtenSized with link := { writtenSized.link with linked := { writtenSized.link.linked with
      stages := atLast (fun y => { y with g := { y.g with k := y.g.k + 1 } })
        writtenSized.link.linked.stages } } }

theorem nine_plant : moreTests nineBent = [false, true, true] ∧
    sizedTests nineBent = [true, true, true, true, true, true] := by decide +kernel

/-- The sizes with the key file's test on the table said to be no one-time test. -/
def rightBent : Sized :=
  { writtenSized with key := { writtenSized.key with once := { writtenSized.key.once with
      lines := { writtenSized.key.once.lines with oneTime := false } } } }

theorem right_plant : moreTests rightBent = [true, false, true] ∧
    sizedTests rightBent = [true, true, true, true, true, true] := by decide +kernel

/-- The sizes with one more in a number of the code of the links' group. -/
def codesBent : Sized :=
  { writtenSized with proof := { writtenSized.proof with link := { writtenSized.proof.link with
      group := { writtenSized.proof.link.group with
        main := { writtenSized.proof.link.group.main with
          r := writtenSized.proof.link.group.main.r + 1 } } } } }

theorem codes_plant : moreTests codesBent = [true, true, false] ∧
    sizedTests codesBent = [true, true, true, true, true, true] := by decide +kernel

end VerifiableInference.PlanWritten.Joined

#print axioms VerifiableInference.PlanWritten.Joined.more_yes
#print axioms VerifiableInference.PlanWritten.Joined.nine_plant
#print axioms VerifiableInference.PlanWritten.Joined.right_plant
#print axioms VerifiableInference.PlanWritten.Joined.codes_plant
