-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Join.lean: ONE SMALL TOOL OF THE LAST JOIN, AND THE ROAD OF IMPORTS TO IT. A law
file; no running text imports it.
  `list3`   a list of length 3 is its three members.
The last join is in Johnson/AtFull/Rows/JoinKey.lean, which imports this file: its
`rowsWB_of_pieces` spends `list3`. Rows.lean reaches `all27` (Cuts.lean) by this road alone.





The limits of «rowsWB = true» stand in the head of Rows.lean.

At the foot seven theorems of Tail.lean are asked for their axioms: their own file asks for five
others, not for these.
Limits. A tool. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.AtW
import Johnson.AtFull.Rows.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

theorem list3 {α : Type} (d : α) (l : List α) (h : l.length = 3) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, t⟩⟩⟩⟩
  · cases h
  · cases h
  · cases h
  · rfl
  · simp at h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.list3
#print axioms VerifiableInference.Desc.LinkJoin.good_one
#print axioms VerifiableInference.Desc.LinkJoin.fr_key0R
#print axioms VerifiableInference.Desc.LinkJoin.fr_key1R
#print axioms VerifiableInference.Desc.LinkJoin.fr_key2R
#print axioms VerifiableInference.Desc.LinkJoin.fr_entryR
#print axioms VerifiableInference.Desc.LinkJoin.fr_proof1R
#print axioms VerifiableInference.Desc.LinkJoin.fr_proof2R
