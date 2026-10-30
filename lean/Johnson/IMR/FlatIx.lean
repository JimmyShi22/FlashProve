-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FlatIx.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT Block.lean's Chain.blocksInOrder | Link.blocksInOrder: AT WHICH NUMBER of a chain's flat list a block in
front of a link's batching stands.
OBJECT. Chain.blocksInOrder · Link.blocksInOrder (Johnson/Desc/Block.lean): GENERAL IN THE CHAIN: no block of the protocol is named.
WHY. Johnson/IMR/PureChain.lean's hear_split (c.blocksInOrder = pre ++ b :: post) leaves pre and post under «there is».
LETTERS. c: a chain · l i: the link's number and the block's number in front of its batching · Lk b: c.links[l]? = some Lk · Lk.hear[i]? = some b.
Compiled with the whole library.

  flatIx c l i      := (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length + (1 + i)): the first block and the front · the links in front, flat · «link l: laid» · i.
  hear_at_flat      c.blocksInOrder[flatIx c l i]? = some b.
  hear_cut          c.blocksInOrder = c.blocksInOrder.take (flatIx c l i) ++ b :: c.blocksInOrder.drop (flatIx c l i + 1): pre AND post ARE TERMS OF c, l AND i.

What is not claimed. Which number flatIx c l i is at onlineDescription's chain (341 at K6's place by a count not shown here: it wants each link's flat list's length). That b stands in the flat list once. No soundness.
-/
import Johnson.Desc.Block

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Chain Link)

theorem getElem?_append_some {α : Type} {X : List α} {j : Nat} {b : α} (h : X[j]? = some b) (Y : List α) :
    (X ++ Y)[j]? = some b := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

theorem getElem?_append_add {α : Type} (X Y : List α) (j : Nat) : (X ++ Y)[X.length + j]? = Y[j]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The number, from 0, in a chain's flat list of block number i in front of the batching of link number l: the first block and the front · the links in front, flat · «link l: laid» · i. -/
def flatIx {σ C : Type} (c : Chain σ C) (l i : Nat) : Nat :=
  (1 + c.front.length) + (((c.links.take l).flatMap Link.blocksInOrder).length + (1 + i))

/-- **THE CUT, PINNED: the block stands in the flat list AT THAT NUMBER**: so pre := c.blocksInOrder.take (flatIx c l i), a term of c, l and i. General in the chain. -/
theorem hear_at_flat {σ C : Type} {c : Chain σ C} {l i : Nat} {Lk : Link σ C} {b : Block σ C}
    (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b) : c.blocksInOrder[flatIx c l i]? = some b := by
  obtain ⟨hl, e⟩ := List.getElem?_eq_some_iff.1 h1
  have hs : c.links = c.links.take l ++ Lk :: c.links.drop (l + 1) := by
    rw [← e, ← List.drop_eq_getElem_cons hl, List.take_append_drop]
  have hLk : Lk.blocksInOrder[1 + i]? = some b := by
    unfold Link.blocksInOrder
    refine getElem?_append_some (getElem?_append_some (getElem?_append_some ?_ _) _) _
    rw [Nat.add_comm, List.getElem?_cons_succ]
    exact h2
  have hM : (c.links.flatMap Link.blocksInOrder)[((c.links.take l).flatMap Link.blocksInOrder).length + (1 + i)]? =
      some b := by
    generalize c.links.take l = P at hs ⊢
    generalize c.links.drop (l + 1) = Q at hs
    rw [hs, List.flatMap_append, List.flatMap_cons, getElem?_append_add]
    exact getElem?_append_some hLk _
  unfold Chain.blocksInOrder flatIx
  refine getElem?_append_some (getElem?_append_some ?_ _) _
  have hA : (1 + c.front.length) =
      (({ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } : Block σ C) ::
        c.front.map fun b : Block σ C => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }).length := by
    rw [List.length_cons, List.length_map, Nat.add_comm]
  rw [hA, getElem?_append_add]
  exact hM

/-- The cut itself. -/
theorem hear_cut {σ C : Type} {c : Chain σ C} {l i : Nat} {Lk : Link σ C} {b : Block σ C}
    (h1 : c.links[l]? = some Lk) (h2 : Lk.hear[i]? = some b) :
    c.blocksInOrder = c.blocksInOrder.take (flatIx c l i) ++ b :: c.blocksInOrder.drop (flatIx c l i + 1) := by
  obtain ⟨hl, e⟩ := List.getElem?_eq_some_iff.1 (hear_at_flat h1 h2)
  rw [← e, ← List.drop_eq_getElem_cons hl, List.take_append_drop]

end IM

#print axioms IM.hear_at_flat
#print axioms IM.hear_cut
