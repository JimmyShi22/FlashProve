-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/LayAlone.lean: THE RULE THAT PLACES THE MESSAGES OF ONE SENDING IN TREES (layTrees,
OnBytes/Iop/Ground.lean), AT A TREE THAT HOLDS ONE MESSAGE ALONE: THE TREE's WHOLE SHAPE IS A FUNCTION
OF THE CODES AND THAT MESSAGE's SHAPE. One definition, statements and proofs, over
OnBytes/Tie/Pv/Keeps/LayOne.lean, whose lay_one has the depth and the sum of the widths: here all
four fields, by its own tools.


Why. The last chain takes Omega over from the shared chain: the new tree in its book bears the
shared tree's number and source, and a shape that is laid anew for Omega alone
(Johnson/Desc/Third/Law/TreeShape.lean). The shared tree's shape was laid with the split's message
beside Omega in one sending. That the two shapes are one is a sentence on the public parameters.

  shapeAlone codes s   the shape of a tree that holds one message of the shape s alone.
  lay_alone            a message alone in its tree: its tree's shape is shapeAlone.
  lay_single           a sending of one message.
  lay_alone_same       two sendings, a message of one shape alone in its tree in each: one shape.
  lay_first_of_two     a sending of two messages that lie in two trees, against the first sent
                       alone.
  alone_of_cnt_two     "the first message's tree has one part" (cnt, Johnson/Desc/Book/BookFits.lean)
                       says that the second lies in another tree.
IS IT EMPTY? lay_alone's premises are met by every sending of one message that layTrees lays
(lay_single is that case). For two messages: no example is shown here.
WHAT IS NOT HERE. Anything on a state, a book or a run. Nothing on soundness.
-/
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open OnBytes.Params (laidOf layPass layStep)
open OnBytes.Tie.Pv.Keeps.Fit

/-- The shape of a tree that holds one message of the shape s alone. -/
def shapeAlone (codes : Codes) (s : OracleShape) : TreeShape :=
  { logN := depth1 codes s
    logNzk := if 0 < s.maskRows then (codes.mask.getD s.maskCode default).logN else 0
    mainSymbols := #[s.mainRows * s.mainDeg]
    maskSymbols := #[s.maskRows * 3] }

/-- The last step turns the depth alone. -/
theorem fixShape_rest (t : TreeShape) : (fixShape t).logNzk = t.logNzk ∧
    (fixShape t).mainSymbols = t.mainSymbols ∧ (fixShape t).maskSymbols = t.maskSymbols := by
  unfold fixShape
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- **A message alone in its tree: the tree's shape.** -/
theorem lay_alone {codes : Codes} {sent : Array OracleNotice} {T : TreeLay} {i0 : Nat}
    (h : layTrees codes sent = some T) (hi0 : i0 < sent.size)
    (uniq : ∀ j, j < sent.size → T.tree.getD j 0 = T.tree.getD i0 0 → j = i0) :
    T.shapes.getD (T.tree.getD i0 0) {} = shapeAlone codes (sent.getD i0 default).shape := by
  obtain ⟨_, hN, _⟩ := lay_one h hi0 uniq
  obtain ⟨filled, hf, eT, eS⟩ := layTrees_some h
  obtain ⟨pi, pl⟩ := laid_spec (codes := codes) hi0
  rw [eT] at uniq hN ⊢
  obtain ⟨sz, g⟩ := fill_spec _ _ _ _ pl.1 uniq sent.size filled (Nat.le_refl _) hf
  rw [if_pos hi0] at g
  obtain ⟨b1, b2, b3⟩ := pi.1 ((laidOf codes sent).2.2.getD i0 0)
  have hlt : (laidOf codes sent).2.2.getD i0 0 < filled.1.size := by rw [sz]; exact pl.1
  rw [eS, getD_map _ _ _ {} _ hlt, g] at hN ⊢
  obtain ⟨r1, r2, r3⟩ := fixShape_rest
    (fillOne codes sent i0 ((laidOf codes sent).1.getD ((laidOf codes sent).2.2.getD i0 0) {}))
  have e : ∀ t : TreeShape, t = ⟨t.logN, t.logNzk, t.mainSymbols, t.maskSymbols⟩ := fun _ => rfl
  rw [e (fixShape _), hN, r1, r2, r3]
  unfold fillOne shapeAlone
  dsimp only
  rw [b1, b2, b3]
  simp

/-- One message alone is laid into tree 0. -/
theorem tree_single {codes : Codes} {n : OracleNotice} {T : TreeLay}
    (h : layTrees codes #[n] = some T) : T.tree.getD 0 0 = 0 := by
  obtain ⟨_, _, eT, _⟩ := layTrees_some h
  rw [eT]
  cases hm : (n.shape.mainRows == 0) <;> simp [laidOf, layPass, layStep, hm]

/-- A sending of one message. -/
theorem lay_single {codes : Codes} {n : OracleNotice} {T : TreeLay}
    (h : layTrees codes #[n] = some T) : T.shapes.getD 0 {} = shapeAlone codes n.shape := by
  have := lay_alone (i0 := 0) h (by simp) (fun j hj _ => by
    have : j < 1 := by simpa using hj
    omega)
  rw [tree_single h] at this
  simpa using this

/-- Two sendings, a message of one shape alone in its tree in each: one shape. -/
theorem lay_alone_same {codes : Codes} {sent sent' : Array OracleNotice} {T T' : TreeLay}
    {i i' : Nat} (h : layTrees codes sent = some T) (hi : i < sent.size)
    (uniq : ∀ j, j < sent.size → T.tree.getD j 0 = T.tree.getD i 0 → j = i)
    (h' : layTrees codes sent' = some T') (hi' : i' < sent'.size)
    (uniq' : ∀ j, j < sent'.size → T'.tree.getD j 0 = T'.tree.getD i' 0 → j = i')
    (es : (sent'.getD i' default).shape = (sent.getD i default).shape) :
    T'.shapes.getD (T'.tree.getD i' 0) {} = T.shapes.getD (T.tree.getD i 0) {} := by
  rw [lay_alone h hi uniq, lay_alone h' hi' uniq', es]

/-- **A sending of two messages that lie in two trees, against the first sent alone.** -/
theorem lay_first_of_two {codes : Codes} {n0 n1 : OracleNotice} {T₂ T₁ : TreeLay}
    (h₂ : layTrees codes #[n0, n1] = some T₂) (h₁ : layTrees codes #[n0] = some T₁)
    (hne : T₂.tree.getD 1 0 ≠ T₂.tree.getD 0 0) :
    T₂.shapes.getD (T₂.tree.getD 0 0) {} = T₁.shapes.getD 0 {} := by
  have a := lay_alone (i0 := 0) h₂ (by simp) (fun j hj e => by
    have hj' : j < 2 := by simpa using hj
    rcases Nat.lt_or_ge j 1 with q | q
    · omega
    · obtain rfl : j = 1 := by omega
      exact absurd e hne)
  rw [a, lay_single h₁]
  simp

/-- "The first message's tree has one part" says that the second lies in another tree. -/
theorem alone_of_cnt_two (tree : Array Nat) (h : cnt tree (tree.getD 0 0) 2 = 1) :
    tree.getD 1 0 ≠ tree.getD 0 0 := by
  intro e
  have : cnt tree (tree.getD 0 0) 2 = 2 := by
    simp [cnt, e]
  omega

end VerifiableInference.Desc.Book

#print axioms VerifiableInference.Desc.Book.lay_alone
#print axioms VerifiableInference.Desc.Book.lay_single
#print axioms VerifiableInference.Desc.Book.lay_first_of_two
#print axioms VerifiableInference.Desc.Book.alone_of_cnt_two
