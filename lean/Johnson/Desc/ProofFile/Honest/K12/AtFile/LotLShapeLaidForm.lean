-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeLaidForm.lean

It states no goal. No property of the protocol is claimed.

THE LOCAL SHAPE IN FRONT OF THE FIRST CHAIN's CLOSING
TEST, AS ONE STRUCTURE: what the last code switch has laid, read off the shape of statement, book and count of roots
(`CoreSh`, Johnson/Desc/Ground/Shape/Core.lean): six readings and five counts. A definition alone.

  `ClosingGroupLaid`   the closing group, the message that carries the claim, the fresh mask, their one tree and their
                       two places are the named ones, and they are the last of their lists

Limits. A definition: no state is shown to meet it. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.Ground.Shape.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.Ground.Sh (CoreSh GrpSh OrcSh TreeSh)

/-- **What the last code switch has laid, read off the shape.** group, carrier, mask, tree: the four numbers. G, x, z,
T: the four records' shapes. -/
structure ClosingGroupLaid (c : CoreSh) (group carrier mask tree : ℕ) (G : GrpSh) (x z : OrcSh)
    (T : TreeSh) : Prop where
  groupIs : c.st.groups[group]? = some G
  carrierIs : c.st.oracles[carrier]? = some x
  maskIs : c.st.oracles[mask]? = some z
  treeIs : c.book.trees[tree]? = some T
  carrierPlace : c.book.place[carrier]? = some (tree, 0)
  maskPlace : c.book.place[mask]? = some (tree, 1)
  /-- the mask stands right behind the carrier -/
  next : mask = carrier + 1
  groups : c.st.groups.length = group + 1
  messages : c.st.oracles.length = mask + 1
  places : c.book.place.length = mask + 1
  trees : c.book.trees.length = tree + 1

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.ClosingGroupLaid
