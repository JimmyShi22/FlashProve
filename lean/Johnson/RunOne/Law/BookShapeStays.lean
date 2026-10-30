-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/BookShapeStays.lean: THEOREMS. A TREE's SHAPE IN THE VERIFIER STATE's BOOK OF TREES: it
stays wherever the book keeps its trees; where oracle messages are seated, each new tree has the layout's shape; K14's second part lays a
tree with the shape of the layout of Omega alone. General: no premise on a plan, no chain named but in omega_tree.


Words: a "book" is the verifier state's table of trees (TreeBook); a "layout" is what layTrees, the routine that places a prover's
message's oracle messages in trees, returns.

Main names:
  treeShape B z                the shape of the book's tree number z.
  treeShape_keeps              it stays along BookKeeps (OnBytes/Slice/BlkSeat.lean).
  keeps_of_seated | treeShape_made   of Book.Seated (Johnson/Desc/Book/Seated.lean): older trees stay; new tree τ has the layout's shape.
  keeps_left | keeps_right | getD_some   glue.
  omega_tree                   an accepting run of K14's second part lays, behind the older trees, a tree with the shape of the layout of
                               Omega ALONE at the state's codes. Kin: laid_tree_shape
                               (Johnson/Desc/Third/Law/TreeShape.lean) states the like and more.
User: Johnson/RunOne/Law/BookAt32.lean.
What is not claimed. Which sub-protocols keep the book or seat messages: their own laws say it (Book.recvP_seat | adoptP_seat,
K1.decideSend_seated, H2K.Out.k12_out). Nothing on a tree's number, source, parts or root. Nothing on soundness.

-/
import OnBytes.Slice.BlkSeat
import Johnson.Desc.Book.BookFitsGround
import Johnson.Desc.Third.Law.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.BookShapeStays
open OnBytes OnBytes.Params
open OnBytes.Slice (BookKeeps)
open VerifiableInference.Desc
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart)

/-! ## 1 A tree's shape -/

/-- The shape of the book's tree number z. -/
def treeShape (B : TreeBook) (z : ℕ) : Option TreeShape := (B.trees[z]?).map (·.shape)

/-- **A tree's shape stays** along BookKeeps. -/
theorem treeShape_keeps {B B' : TreeBook} (h : BookKeeps B B') {z : ℕ} {T : TreeShape}
    (e : treeShape B z = some T) : treeShape B' z = some T := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨t', ht', hs, -, -⟩ := h.tree z t ht
  unfold treeShape
  rw [ht']
  exact congrArg some hs

section
variable {B B' : TreeBook} {n n0 : ℕ} {lay : TreeLay} {num : ℕ → ℕ} {src : ℕ → Fmt.Src}

/-- Where messages are seated, every older place and tree is as it was. -/
theorem keeps_of_seated (h : Book.Seated B B' n n0 lay num src) : BookKeeps B B' :=
  ⟨fun o p e => by
      rw [h.places o (Array.getElem?_eq_some_iff.1 e).1]
      exact e,
    fun t T e => ⟨T, by
      rw [h.trees t (Array.getElem?_eq_some_iff.1 e).1]
      exact e, rfl, rfl, rfl⟩⟩

/-- Where messages are seated, new tree τ has the layout's shape. -/
theorem treeShape_made (h : Book.Seated B B' n n0 lay num src) {τ : ℕ} (hτ : τ < lay.shapes.size) :
    treeShape B' (B.trees.size + τ) = some (lay.shapes.getD τ {}) := by
  obtain ⟨t, ht, hs, -⟩ := h.made τ hτ
  unfold treeShape
  rw [ht]
  exact congrArg some hs

end


theorem keeps_left {A A' B : TreeBook} (e : A = A') (h : BookKeeps A B) : BookKeeps A' B := e ▸ h
theorem keeps_right {A B B' : TreeBook} (e : B' = B) (h : BookKeeps A B) : BookKeeps A B' := e ▸ h

theorem getD_some {α : Type} (A : Array α) (i : ℕ) (d : α) (h : i < A.size) : A[i]? = some (A.getD i d) := by
  rw [Array.getElem?_eq_getElem h, Array.getElem_eq_getD d]

/-! ## 2 Omega's tree in the last chain's book -/

/-- **K14's second part lays a tree with the shape of the layout of Omega alone**, at the state's codes, behind the older trees. (Kin:
laid_tree_shape states the like and more.) -/
theorem omega_tree {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    ∃ lay, layTrees s.st.codes #[{ shape := p.S.omega, leafClass := p.S.omegaLeafClass }] = some lay ∧
      treeShape s'.book s.book.trees.size = some (lay.shapes.getD 0 {}) := by
  obtain ⟨x, a, dot, b, -, ha, -, hb, e⟩ := Third.Law.k14Second_inv p s s' rs gs h
  subst e
  obtain ⟨q, t, y, a0, d₁, -, -, hy, h0, -, h1, h2⟩ := Third.Law.takeOver_inv _ _ _ _ _ ha
  obtain ⟨y', hy', hs⟩ := Third.Law.takeOver_shape _ _ _ _ _ ha
  obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
  rw [hs] at h0
  obtain ⟨-, lay, hl, hS⟩ := Book.adoptP_seat _ a0.2 _ _ a0.1 h0
  have eb : b.book = a0.2.book :=
    (Third.Law.addRowP_book _ _ _ _ hb).trans
      ((Third.Law.joinP_book _ _ _ _ _ h2).trans (Third.Law.elsewhereP_book _ _ _ _ _ h1))
  have h0' : 0 < lay.shapes.size := Nat.lt_of_le_of_lt (Nat.zero_le _) (hS.fits 0 (show 0 < 1 from Nat.zero_lt_one)).1
  refine ⟨lay, hl, ?_⟩
  show treeShape b.book s.book.trees.size = _
  rw [eb]
  exact treeShape_made hS h0'

end Johnson.RunOne.Law.BookShapeStays

#print axioms Johnson.RunOne.Law.BookShapeStays.treeShape_keeps
#print axioms Johnson.RunOne.Law.BookShapeStays.keeps_of_seated
#print axioms Johnson.RunOne.Law.BookShapeStays.treeShape_made
#print axioms Johnson.RunOne.Law.BookShapeStays.keeps_left
#print axioms Johnson.RunOne.Law.BookShapeStays.keeps_right
#print axioms Johnson.RunOne.Law.BookShapeStays.getD_some
#print axioms Johnson.RunOne.Law.BookShapeStays.omega_tree
