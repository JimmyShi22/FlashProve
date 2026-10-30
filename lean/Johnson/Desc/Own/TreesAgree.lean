-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/TreesAgree.lean: Johnson/Desc/Own/Trees.lean's treesMade is the hand-written
program's layTrees (OnBytes/Iop/Ground.lean), and treesCan says just whether layTrees gives
something.

Two equations, each at all arguments and without a premise. No block imports this file: it is for
whoever carries a law on the program's layTrees over to the description's own text.
Main names:
  `treesMade_eq`: treesMade codes sent = layTrees codes sent.
  `treesCan_eq`: treesCan codes sent = (layTrees codes sent).isSome.
Limits: nothing on whether this is the right way to lay trees. Nothing on soundness.

-/
import Johnson.Desc.Own.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

theorem treesMade_eq (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    treesMade codes sent = OnBytes.layTrees codes sent := by
  have e : OnBytes.layTrees codes sent =
      ((List.range sent.size).foldlM (fillStep codes sent (treeOf codes sent).2.2)
        ((treeOf codes sent).1, #[], Array.replicate (treeOf codes sent).1.size 0)).bind
        (closeTrees (treeOf codes sent).2.2) := rfl
  rw [e]
  unfold treesMade
  cases (List.range sent.size).foldlM (fillStep codes sent (treeOf codes sent).2.2)
    ((treeOf codes sent).1, #[], Array.replicate (treeOf codes sent).1.size 0) <;> rfl

theorem treesCan_eq (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    treesCan codes sent = (OnBytes.layTrees codes sent).isSome := by
  unfold treesCan
  rw [treesMade_eq]

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.treesMade_eq
#print axioms VerifiableInference.Desc.Own.treesCan_eq
