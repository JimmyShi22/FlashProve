-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendFlat.lean: THEOREMS. **From a block as a chain's maker lists it to the block that stands in the chain's flat list.** Over Johnson/Desc/Block.lean, where a chain has
a first and a last block as fields of their own. Chain.blocksInOrder lays each block of `first`, `front`, `back` and `last` with one clause more on its test on the plan (it has neither claims nor runs behind a batching): so the block at a seat is not the
listed block itself.
  bareOf        the block as Chain.blocksInOrder lays it
  flat_first    the first block stands, so laid, at the flat list's place 0
  flat_front    the i-th block of front stands, so laid, at place i + 1
  flat_back     the j-th block of back stands, so laid, behind first, front and all the links' flat lists
  pays_bare     what a block brings to the law of a sending (Pays) from the laid block's own test on the plan: for a maker of Pays from the listed block's test
What is not claimed. Nothing on a given chain. Nothing on soundness.

-/
import Johnson.RunOne.KeySendThrough

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes
open VerifiableInference.Desc (Block Chain Link)
open VerifiableInference.Desc.K1 (Par IsSend)

variable {S Cl : Type}

def bareOf (b : Block S Cl) : Block S Cl := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

theorem flat_eq (c : Chain S Cl) : c.blocksInOrder = bareOf c.first :: (c.front.map bareOf ++ c.links.flatMap Link.blocksInOrder ++ c.back.map bareOf ++ [bareOf c.last]) := rfl

theorem flat_first (c : Chain S Cl) : c.blocksInOrder[0]? = some (bareOf c.first) := by
  rw [flat_eq]
  rfl

theorem flat_front (c : Chain S Cl) (i : Nat) (b : Block S Cl) (h : c.front[i]? = some b) : c.blocksInOrder[i + 1]? = some (bareOf b) := by
  have hi : i < c.front.length := (List.getElem?_eq_some_iff.1 h).1
  rw [flat_eq, List.getElem?_cons_succ, List.append_assoc, List.append_assoc, List.getElem?_append_left (by rw [List.length_map]; exact hi), List.getElem?_map, h]
  rfl

theorem flat_back (c : Chain S Cl) (j : Nat) (b : Block S Cl) (h : c.back[j]? = some b) :
    c.blocksInOrder[c.front.length + (c.links.flatMap Link.blocksInOrder).length + j + 1]? = some (bareOf b) := by
  have hj : j < c.back.length := (List.getElem?_eq_some_iff.1 h).1
  rw [flat_eq, List.getElem?_cons_succ, List.getElem?_append_left (by simp only [List.length_append, List.length_map]; omega),
    List.getElem?_append_right (by rw [List.length_append, List.length_map]; exact Nat.le_add_right _ _), List.length_append, List.length_map,
    Nat.add_sub_cancel_left, List.getElem?_map, h]
  rfl

theorem pays_bare (P : Par) (stOf : S → Statement) (b : Block S Cl) (mk : b.planOk = true → Pays P stOf b) (h : (bareOf b).planOk = true) : Pays P stOf (bareOf b) := by
  have h' : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := h
  have hb := mk (Bool.and_eq_true_iff.1 h').1
  exact ⟨hb.plan, fun s s' r₁ r₂ gs hy => hb.send s s' r₁ r₂ gs hy⟩

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.flat_first
#print axioms Johnson.RunOne.KeySendGood.flat_front
#print axioms Johnson.RunOne.KeySendGood.flat_back
#print axioms Johnson.RunOne.KeySendGood.pays_bare
