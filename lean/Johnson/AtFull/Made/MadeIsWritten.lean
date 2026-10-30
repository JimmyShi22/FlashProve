-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MadeIsWritten.lean: what the planner returns is the written full-size value with
the eight strings spelled from it; and what follows from that for single fields.

THE PREMISES ARE NOT SHOWN AT ANY FILES. The laws from the planner's return take that return, and
equations that say that parts of it are written values. To show these is other files' business.

A `Configured` (OnBytes/Params/Configure.lean) has twelve fields. Four do not hang on the digest of
the public files: the sizes and the plans (`Free`, Johnson/G/MadeFree.lean). Eight do: the digest
and the parameter bytes of the seven chains (`Hung`). `writtenMade` (Johnson/Goal/Written/Made.lean)
is a written value of the four. Several files state facts at `writtenMade.at h` for a letter h, or
at `Hung.none`, which is eight empty strings. Here it is said which h goes with the planner's
return: `spelled writtenMade x cfg` (Johnson/G/MadeSpelled.lean), not `Hung.none`.

`configure_eq_written_at`: from the planner's return, its sizes and the first plan of its proof
file. Two laws in a row: `free_of_sized` (Johnson/Goal/Written/ChainsW.lean) and
`configure_hung` (Johnson/G/MadeSpelled.lean). `free_of_two`, `configure_eq_written_at_of_two`: at
the written lines, from the key's sizing and `MadeWritten`
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean), by `sized_of_configure`
(Johnson/Goal/Numbers/MadeInScope.lean). `written_fields`: the written value's parts by name.
`fields_of_free`, `madeWritten_of_free`, `at_hung_of_free`: what follows where the four fields are
the written value.

Under the planner's return at the written lines and the key's sizing, `MadeWritten made` and `freeOf
made = writtenMade` follow from each other (`free_of_two`, `madeWritten_of_free`). They are two
forms of one debt: neither pays the other.

Limits. A fact on a function at `writtenMade.at Hung.none` carries to the planner's return only
where that function reads none of the eight strings: each function wants its own line, and none is
here. For `Johnson.G.sendsFrom` it is `sendsFrom_free` (Johnson/AtFull/Made/SendsLedger.lean).
Nothing on soundness.
-/
import Johnson.Goal.Written.ChainsW
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.G Johnson.G.MadeFree
open VerifiableInference.PlanWritten (proofSizedFull MadeWritten)
open VerifiableInference.PlanWritten.Joined (writtenMade writtenSized free_of_sized
  sized_of_configure)
open VerifiableInference.Number.ByRuns (keyThree proofThree)
open Lk6.AtPlan (keyFull)

/-- **What the planner returns is the written value with the eight strings spelled from it**, where
its sizes and the first plan of its proof file are the written ones. -/
theorem configure_eq_written_at {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hc : configure l x cfg bits = .ok made) (hs : made.sized = writtenSized)
    (hF : made.proof.head? = some proofThree.A.plan) :
    made = writtenMade.at (spelled writtenMade x cfg) := by
  have k := configure_hung hc
  rw [free_of_sized hc hs hF] at k
  exact k

/-- At the written lines, from the key's sizing and the two equations of `MadeWritten`: the four
fields are the written value. `made_of_written` (Johnson/Goal/Numbers/MadeInScope.lean) is this in
the goals' scope. -/
theorem free_of_two {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure recordLines x cfg bits = .ok made)
    (hk : Plan.keySized recordLines x.ranges = some keyFull) (hm : MadeWritten made) :
    freeOf made = writtenMade :=
  free_of_sized hc (sized_of_configure hc hk hm.1) hm.2

/-- And so the whole is the written value with the eight strings spelled from it. -/
theorem configure_eq_written_at_of_two {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hc : configure recordLines x cfg bits = .ok made)
    (hk : Plan.keySized recordLines x.ranges = some keyFull) (hm : MadeWritten made) :
    made = writtenMade.at (spelled writtenMade x cfg) :=
  configure_eq_written_at hc (sized_of_configure hc hk hm.1) hm.2

/-- The written value's parts, by name. -/
theorem written_fields :
    writtenSized.lines = recordLines ∧ writtenSized.set = recordSet ∧
      writtenSized.proof = proofSizedFull ∧ writtenSized.key = keyFull ∧
      writtenMade.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] ∧
      writtenMade.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] ∧
      writtenMade.entry = pricedEntryFull :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Where the four fields are the written value, each is the written value's. -/
theorem fields_of_free {made : Configured} (hf : freeOf made = writtenMade) :
    made.sized = writtenSized ∧ made.proof = writtenMade.proof ∧ made.key = writtenMade.key ∧
      made.entry = writtenMade.entry :=
  ⟨congrArg Free.sized hf, congrArg Free.proof hf, congrArg Free.key hf, congrArg Free.entry hf⟩

/-- Where the four fields are the written value, the two equations of `MadeWritten` hold. -/
theorem madeWritten_of_free {made : Configured} (hf : freeOf made = writtenMade) :
    MadeWritten made :=
  ⟨congrArg (fun W : Free => W.sized.proof) hf, congrArg (fun W : Free => W.proof.head?) hf⟩

/-- Where the four fields are the written value, the whole is the written value with its own eight
strings. -/
theorem at_hung_of_free {made : Configured} (hf : freeOf made = writtenMade) :
    made = writtenMade.at (hungOf made) := by
  have k := (at_free made).symm
  rw [hf] at k
  exact k

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.configure_eq_written_at
#print axioms Johnson.AtFull.Made.free_of_two
#print axioms Johnson.AtFull.Made.configure_eq_written_at_of_two
#print axioms Johnson.AtFull.Made.written_fields
#print axioms Johnson.AtFull.Made.fields_of_free
#print axioms Johnson.AtFull.Made.madeWritten_of_free
#print axioms Johnson.AtFull.Made.at_hung_of_free
