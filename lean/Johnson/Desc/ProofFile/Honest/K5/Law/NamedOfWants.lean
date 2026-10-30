-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/NamedOfWants.lean: ten names of the namespace ProofFile.Honest.K5
that stand for the laws of the same spelling in ProofFile.Honest.Small (Honest/Small/WantsStated.lean). No
statement, no proof and no definition stands here: one line `export`. Why: the callers in this
folder write these names short and import this file, and their texts stay.

Limits. A name below is no declaration: a list of declared names has it under ProofFile.Honest.Small
alone. What each law says, its premises and its Limits stand in Honest/Small/WantsStated.lean.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Desc.ProofFile.Honest.K5.Law.StatedK5
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsOfBook

namespace ProofFile.Honest.K5

export ProofFile.Honest.Small (wants_stated numbered_at planParts_at flat_parts_at rowNamed_of_parts
  ownerOf_name wants_at_plain ends_kind no_merge_of_kind partNamed_of)

end ProofFile.Honest.K5
