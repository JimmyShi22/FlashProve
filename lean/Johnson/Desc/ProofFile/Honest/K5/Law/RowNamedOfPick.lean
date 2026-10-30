-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RowNamedOfPick.lean: one name of the namespace ProofFile.Honest.K5
that stands for the law of the same spelling in ProofFile.Honest.Small (Honest/Small/WantsStated.lean). No
statement, no proof and no definition stands here: one line `export`. Why: the callers in this
folder write this name short and import this file, and their texts stay.

Limits. A name below is no declaration: a list of declared names has it under ProofFile.Honest.Small
alone. What the law says, its premises and its Limits stand in Honest/Small/WantsStated.lean.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.NamedOfWants

namespace ProofFile.Honest.K5

export ProofFile.Honest.Small (rowNamed_of_pick)

end ProofFile.Honest.K5
