-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryDescRecord.lean: the description of an entry's chain does not depend on the
tables but for its statement.

OnBytes/Params/EntryRoundsRecord.lean states this under a hypothesis, `LinkDryBySizes`: the dry run
of a link's block states the same rounds, with the same stored openings, or none, at any two pairs
of keys that fit the tables' shape and name the same items. OnBytes/Iop/DrySizes.lean proves that of
every shape (`linkVerify_rounds_sizes`); `linkDryBySizes` is that law in the hypothesis's letters.
So the laws hold with no hypothesis on the dry run: if `Tie.entrySpec` gives a block and a
description, the block is the link's block at the two tables' own keys, and the description is made
of the rounds at keys of zeros, which are a function of the parameter bytes, and of the statement
(`entrySpec_eq_all`, `entrySpec_rounds_all`); at two other tables it is the same but for its
statement (`entrySpec_at_all`). At the parameter bytes typed for the full-size files of the setting
"record with work" the description is one closed value but for its statement: it is made of the
typed bytes and of `recordRounds`, which is the dry run's value at keys of zeros and is not typed
out (`record_entrySpec_all`). And at `recordLines` and the typed digest what `configure` has made
for an entry's chain is read whole: the made bytes are `recordBytes`, and `Link.read` returns
`recordRead` on them (`record_made_read`).

Main theorems: `linkDryBySizes`, `entrySpec_eq_all`, `entrySpec_rounds_all`, `entrySpec_at_all`,
`record_entrySpec_all`, `record_made_read`.
What is not claimed: that `Tie.entrySpec` gives a description.

That the block is a function of the parameter
bytes: it is made of the tables' answers and seeds, so nothing here serves where the
block's decision must be fixed before the tables are known. Nothing on a run on a view. That
`configure` says yes at `recordLines`, or that the digest of any three public files is `recordCfg`.
For proofs only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Iop.DrySizes
import OnBytes.Model.FitRecord
import OnBytes.Params.EntryDryRecord

set_option autoImplicit false

namespace OnBytes.Params

/-- **The rounds that the dry run of a link's block states depend on the tables' keys through their
sizes and items alone**, at every shape (`linkVerify_rounds_sizes`, OnBytes/Iop/DrySizes.lean). -/
theorem linkDryBySizes (S : LinkShape) : LinkDryBySizes S :=
  fun st _ _ _ _ f0 f0' f1 f1' i0 i1 => linkVerify_rounds_sizes st f0 f0' f1 f1' i0 i1

section
variable {p : Link} {first further : TableName} {block : Blk Unit} {S : Fmt.SpecX}

/-- If `Tie.entrySpec` gives a block and a description: the block is the
link's block at the two tables' own keys, and the description is made of the rounds at keys of zeros
and of the statement. -/
theorem entrySpec_eq_all (h : Tie.entrySpec p first further = some (block, S)) :
    (∃ k0 k1, tableKey p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 = some k1 ∧
      block = linkVerify p.link k0 k1) ∧
      ∃ r, entryRoundsAny p = some r ∧ S = entrySpecOf p r (Link.statement first further) :=
  entrySpec_eq_any (linkDryBySizes p.link) h

/-- The description's rounds, stored openings, plan and statement. -/
theorem entrySpec_rounds_all {r : Rounds} (hr : entryRoundsAny p = some r)
    (h : Tie.entrySpec p first further = some (block, S)) :
    S.base.rounds = r.map (·.1) ∧ S.stored = r.map (·.2) ∧ S.base.plan = p.given.plan ∧
      S.base.statement = Link.statement first further :=
  entrySpec_rounds_any (linkDryBySizes p.link) hr h

/-- A description that `Tie.entrySpec` gives at two tables is the one that it gives at two others,
but for its statement. -/
theorem entrySpec_at_all {first' further' : TableName} {block' : Blk Unit} {S' : Fmt.SpecX}
    (h : Tie.entrySpec p first further = some (block, S))
    (h' : Tie.entrySpec p first' further' = some (block', S')) :
    S = { S' with base := { S'.base with statement := Link.statement first further } } :=
  entrySpec_at_any (linkDryBySizes p.link) h h'

end

/-- **Under `recordRead` and for all tables**: a description that `Tie.entrySpec` gives is made of
the typed parameter bytes, the rounds `recordRounds` and the statement. Nothing says that it gives
one. -/
theorem record_entrySpec_all {first further : TableName} {block : Blk Unit} {S : Fmt.SpecX}
    (h : Tie.entrySpec recordRead first further = some (block, S)) :
    S = entrySpecOf recordRead recordRounds (Link.statement first further) :=
  record_entrySpec (linkDryBySizes recordLink) h

/-- **At `recordLines` and the typed digest, what `configure` has made for an entry's chain is read
whole**: the made bytes are `recordBytes`, and `Link.read` returns `recordRead` on them: the typed
plan, digest, items, codes and shape. -/
theorem record_made_read {x : Shapes} {bits : Nat} {made : Configured}
    (h : configure recordLines x recordCfg bits = .ok made) :
    made.entryLink = recordBytes ∧ Link.read made.entryLink = some recordRead := by
  have e : made.entryLink = recordBytes := record_entryLink h
  exact ⟨e, e ▸ record_read⟩

end OnBytes.Params

#print axioms OnBytes.Params.record_made_read
#print axioms OnBytes.Params.linkDryBySizes
#print axioms OnBytes.Params.entrySpec_eq_all
#print axioms OnBytes.Params.entrySpec_rounds_all
#print axioms OnBytes.Params.entrySpec_at_all
#print axioms OnBytes.Params.record_entrySpec_all
