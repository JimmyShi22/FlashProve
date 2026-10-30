-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/NumberPrices/MadeAtWritten.lean: the written parts of what the planner configures at
the full size, joined into one term, with three parts left as letters; and the
public test on the prices (`Desc.madeOk`, Johnson/Desc/MadeOk.lean) at that term.

`joinMade` is a definition with three letters: the proof file's sizes, the key file's sizes, the
proof file's three written priced plans. `madeOk_join` holds for all three letters: a tool at
written data. No row is to be laid on it.

Definitions.
  `writtenLink`: the entry file's sizes, of the library's typed values.
  `joinMade PS KS F`: the four fields that do not hang on the digest (`Free`,
    Johnson/G/MadeFree.lean). The sizes: the written lines and setting (`recordLines`, `recordSet`),
    PS, KS, `writtenLink`, `recordCodes`. The proof file's plans: F's three. The key file's plans:
    `keyThree`'s (KeyAtWritten.lean). The entry file's plan: `pricedEntryFull`
    (Johnson/G/PricedEntryLit.lean).
Statements.
  `writtenLink_sized`: the planner's sizing of a link, at the written setting, lines and table,
    returns `writtenLink` and `recordCodes`: this is `record_link`
    (OnBytes/Params/EntryParamsRecord.lean).
  `entry_all`: `Desc.chainAll 32 pricedEntryFull` = true. `entry_set`: its setting is `recordSet`.
    `record_slots`: the written lines say 64 slots.
  `madeOk_join`: if `proofLitOk k F` = true (AtWritten.lean), then `Desc.madeOk` says yes at
    `(joinMade PS KS F).at h`, for every h.
By evaluations in Lean's kernel (`decide +kernel`): `entry_all`, `entry_set`, `record_slots`.

What of OnBytes/Model/ is used: nothing by name.

Limits. Three parts are letters. `Desc.madeOk` reads of the sizes the line on slots alone: PS, KS,
`recordSet`, `writtenLink` and `recordCodes` are not read by it. That the term is what the planner
configures at any public files is not said here. What holds a written error: see the head of
AtWritten.lean. Nothing on soundness.
-/
import Johnson.G.MadeFree
import Johnson.G.PricedEntryLit
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten
import OnBytes.Params.EntryParamsRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes OnBytes.Params Johnson.G Johnson.G.MadeFree

/-- The entry file's sizes, of the library's typed values. -/
def writtenLink : LinkSized := ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩

/-- The planner's sizing of a link returns it, with the written codes. -/
theorem writtenLink_sized :
    linkSized recordSet recordLines recordTable {} = some (writtenLink, recordCodes) := record_link

/-- **The written parts joined**, with the proof file's sizes, the key file's sizes and the proof
file's three written priced plans as letters. -/
def joinMade (PS : ProofSized) (KS : Plan.KeySized) (F : Three) : Free :=
  ⟨⟨recordLines, recordSet, PS, KS, writtenLink, recordCodes⟩,
    [F.A.plan, F.B.plan, F.C.plan], [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan],
    pricedEntryFull⟩

/-- The public test on a chain's plan says yes at the entry file's written priced plan. -/
theorem entry_all : Desc.chainAll 32 pricedEntryFull = true := by decide +kernel

/-- Its setting is the setting of the written lines. -/
theorem entry_set : pricedEntrySetFull = recordSet := by decide +kernel

/-- The written lines say 64 slots. -/
theorem record_slots : recordLines.slots = Desc.slots := by decide +kernel

/-- **The public test on the prices says yes at the joined term**, where the proof file's three
written priced plans pass their test. -/
theorem madeOk_join {k : ℕ} {F : Three} (hF : proofLitOk k F = true) (PS : ProofSized)
    (KS : Plan.KeySized) (h : Hung) : Desc.madeOk ((joinMade PS KS F).at h) = true :=
  (Desc.madeOk_iff _).2 ⟨keyOk_of_lit key_lit_ok _ rfl, entry_all,
    proofOk_of_lit hF _ rfl record_slots⟩

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.writtenLink_sized
#print axioms VerifiableInference.Number.ByRuns.entry_all
#print axioms VerifiableInference.Number.ByRuns.entry_set
#print axioms VerifiableInference.Number.ByRuns.record_slots
#print axioms VerifiableInference.Number.ByRuns.madeOk_join
