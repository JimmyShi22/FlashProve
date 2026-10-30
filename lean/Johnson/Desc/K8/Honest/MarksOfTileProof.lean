-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/MarksOfTileProof.lean: THE SMALLNESS TEST: THE PROOF OF `Spec.marks_of_tile`
(Johnson/Desc/K8/Honest/MarksOfTile.lean): where the tables tile, no read is marked twice, all marks
are set, and the reads are as many as the tables' segments. A lemma; none of the library's goals.

Of the three conclusions the first two are `marks_of_tiles`
(Johnson/Desc/First/TailClaims/MarksOfTiles.lean), at the premise "each table lies on a matrix of
the list"; the third is `count_of_tile` (Johnson/Desc/K8/Honest/MarksCount.lean). Nothing else is
done here.
Limits: those of the statement.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.MarksOfTile
import Johnson.Desc.K8.Honest.MarksCount
import Johnson.Desc.First.TailClaims.MarksOfTiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

theorem marks_of_tile : Spec.marks_of_tile := by
  intro tl funs s1 s3 hin h0 h2 hsz
  have hm : ∀ Fn ∈ funs.toList, Fn.mat < tl.NM := fun Fn h => by
    have e := Array.all_eq_true_iff_forall_mem.1 hin Fn (Array.mem_toList_iff.1 h)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    exact e.1
  obtain ⟨rd, e1, e2⟩ := TailClaims.Law.Marks.marks_of_tiles h0 h2 hsz hm
  exact ⟨rd, e1, e2, Marks.count_of_tile hm h0 h2⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.marks_of_tile
