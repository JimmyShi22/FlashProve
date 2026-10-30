-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MadeOfPartsIsWritten.lean: the value in which the ledger of the planner's parts
ends (`madeOfParts`, Johnson/AtFull/Made/Ledger.lean) is its four fields with the eight strings
spelled from them; and at the written full-size parts it is `writtenMade.at (spelled writtenMade x
cfg)`.

`madeOfParts` is the text of the planner's last step with the sizes and the seven plans as letters.
`spelled` (Johnson/G/MadeSpelled.lean) is the same text as a function of the four fields that do not
hang on the digest. The two texts part at one place: the shape of the binding tree is spelled from
the lines that the planner was handed in the one, from the lines in the sizes in the other. So the
second law takes that these are the same lines.

`free_of_parts`: the four fields, by unfolding. `parts_spelled`: the whole, where the sizes hold the
lines. `parts_written`: at the written lines, sizes and seven plans, for every shapes and every
digest. No premise. `madeWritten_parts`: so the two equations of `MadeWritten`
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean) hold of that value.

Limits. That the planner returns that value is the ledger's law, under its premises. That the
letters are the written values at any files is shown nowhere here. Nothing on soundness.

-/
import Johnson.AtFull.Made.Ledger
import Johnson.AtFull.Made.MadeIsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.G Johnson.G.MadeFree
open VerifiableInference.PlanWritten (MadeWritten)
open VerifiableInference.PlanWritten.Joined (writtenMade writtenSized)
open VerifiableInference.Number.ByRuns (keyThree proofThree)

/-- The four fields of `madeOfParts` that do not hang on the digest are its letters. -/
theorem free_of_parts (l : Lines) (x : Shapes) (cfg : ByteArray) (z : Sized)
    (first shared second oneTime keyShared keySecond entry : Planned) :
    freeOf (madeOfParts l x cfg z first shared second oneTime keyShared keySecond entry) =
      ⟨z, [first, shared, second], [oneTime, keyShared, keySecond], entry⟩ := rfl

/-- `madeOfParts` is its four fields with the eight strings spelled from them, where the sizes
hold the lines that the planner was handed. -/
theorem parts_spelled (l : Lines) (x : Shapes) (cfg : ByteArray) (z : Sized)
    (first shared second oneTime keyShared keySecond entry : Planned) (hl : z.lines = l) :
    madeOfParts l x cfg z first shared second oneTime keyShared keySecond entry =
      (⟨z, [first, shared, second], [oneTime, keyShared, keySecond], entry⟩ : Free).at
        (spelled ⟨z, [first, shared, second], [oneTime, keyShared, keySecond], entry⟩ x cfg) := by
  subst hl
  rfl

/-- **At the written parts `madeOfParts` is the written value with the eight strings spelled
from it.** -/
theorem parts_written (x : Shapes) (cfg : ByteArray) :
    madeOfParts recordLines x cfg writtenSized proofThree.A.plan proofThree.B.plan
        proofThree.C.plan keyThree.A.plan keyThree.B.plan keyThree.C.plan pricedEntryFull =
      writtenMade.at (spelled writtenMade x cfg) :=
  parts_spelled recordLines x cfg writtenSized proofThree.A.plan proofThree.B.plan
    proofThree.C.plan keyThree.A.plan keyThree.B.plan keyThree.C.plan pricedEntryFull rfl

/-- The two equations of `MadeWritten` hold of `madeOfParts` at the written parts. -/
theorem madeWritten_parts (x : Shapes) (cfg : ByteArray) :
    MadeWritten (madeOfParts recordLines x cfg writtenSized proofThree.A.plan proofThree.B.plan
      proofThree.C.plan keyThree.A.plan keyThree.B.plan keyThree.C.plan pricedEntryFull) :=
  madeWritten_of_free (free_of_parts recordLines x cfg writtenSized proofThree.A.plan
    proofThree.B.plan proofThree.C.plan keyThree.A.plan keyThree.B.plan keyThree.C.plan
    pricedEntryFull)

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.free_of_parts
#print axioms Johnson.AtFull.Made.parts_spelled
#print axioms Johnson.AtFull.Made.parts_written
#print axioms Johnson.AtFull.Made.madeWritten_parts
