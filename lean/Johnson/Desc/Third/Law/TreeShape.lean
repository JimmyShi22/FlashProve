-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/TreeShape.lean: THE LAST CHAIN, K14's SECOND PART: WHENCE THE NEW TREE IN THE
BOOK HAS ITS SHAPE. Two theorems beside `Laid` (Johnson/Desc/Third/Law/LaidDef.lean), from the same
accepting run. No definition; it changes no other file.



Why. `Laid.tree` says of Omega's copy's tree tO in the last chain's book its NUMBER and its SOURCE,
which are taken from Omega's tree t in the shared chain's book. Of its SHAPE it says nothing. The
text (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean, takeOver) does not take the shape from t, and the
sub-protocol has no round, so no prover's message sets it: it asks that Omega has the public shape
p.S.omega and lets the plain ground's adoptP lay a tree for one message of that shape and the public
leaf class, at the state's codes.

  adoptP_one_tree   adoptP accepting at ONE message and ONE given tree: the new tree, written out.
  laid_tree_shape   K14's second part accepting: the tree at the book's next free place has the
                    shape number 0 of the layout of ⟨p.S.omega, p.S.omegaLeafClass⟩ at the state's
                    codes, and its one part is the new message.
OBJECT. (batchLinearConstraintsSecondPart p).decide. USER. The last table's field on the book at Omega's copy.
IS IT EMPTY? The sub-protocol accepts on the honest walk of both stored key files (synthetic
weights): an evaluation inside this project printed, at both, "WALKS … 20 | 13 | 5 ;
none | none | none": the last chain's walk has its five states and stops nowhere. A print, no theorem.
WHAT IS NOT HERE, TWO THINGS. (1) tO.shape = t.shape. The text compares the two nowhere (its own
head says so). Both are functions of the codes and the plan: t's by its own making at "send o_omega".
(2) THAT THE TEST ON y REACHES t: tO pairs t's number and source with a shape
computed anew; the test "y.shape = S.omega" is on y, Omega's entry in the SHARED statement: that it
reaches t wants "the tree at the shared book's place of Omega was laid under that entry": the
correspondence of the book's places and the statement's messages on the SHARED chain: a fact on the
verifier's own book-keeping there (kin: BookFits, Johnson/Desc/Book/BookFits.lean; Seated.made
at "send o_omega"): not proved here, and asked by neither theorem.
Nothing on soundness.
-/
import Johnson.Desc.Third.Law.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.Later
open VerifiableInference.Desc.Ground (adoptP adoptL elsewhereP joinP addRowP)

namespace VerifiableInference.Desc.Third.Law

/-- adoptP accepting at ONE message and ONE given tree: the new tree, written out. -/
theorem adoptP_one_tree {L : Type} (d : DState L) (n : OracleNotice) (num : Nat) (src : Fmt.Src)
    (a : Array Nat × DState L) (h : adoptP d #[n] #[(num, src)] = some a) :
    ∃ lay, layTrees d.st.codes #[n] = some lay ∧
      a.2.book.trees[d.book.trees.size]? = some
        { shape := lay.shapes.getD 0 {}, number := num, src := src
          parts := #[d.st.oracles.size] } := by
  unfold adoptP at h
  split at h
  · cases hl : VerifiableInference.Desc.Own.treesMade d.st.codes #[n] with
    | none =>
      rw [hl] at h
      cases h
    | some lay =>
      rw [hl] at h
      have e := Option.some.inj h
      have hlay : layTrees d.st.codes #[n] = some lay :=
        (VerifiableInference.Desc.Own.treesMade_eq _ _).symm.trans hl
      have hk0 : lay.tree.getD 0 0 = 0 := by
        rw [layTrees_tree hlay]
        exact laidOf_one _ _
      have hk : ((d.book.trees.push
            { shape := lay.shapes.getD 0 {}, number := num, src := src }).modify
          (d.book.trees.size + lay.tree.getD 0 0)
          (fun x => { x with parts := x.parts.push (d.st.oracles.size + 0) }))[d.book.trees.size +
            lay.tree.getD 0 0]? =
          some { shape := lay.shapes.getD 0 {}, number := num, src := src
                 parts := (#[] : Array Nat).push (d.st.oracles.size + 0) } := by
        rw [hk0]
        have hX : (d.book.trees.push
            ({ shape := lay.shapes.getD 0 {}, number := num, src := src } :
              Tree))[d.book.trees.size +
              0]? = some { shape := lay.shapes.getD 0 {}, number := num, src := src } := by
          simp
        exact modify_same _ _ _ _ hX
      have hs : a.2.book.trees[d.book.trees.size + lay.tree.getD 0 0]? =
          some { shape := lay.shapes.getD 0 {}, number := num, src := src
                 parts := (#[] : Array Nat).push (d.st.oracles.size + 0) } := by
        rw [← e]
        simpa using hk
      rw [hk0, Nat.add_zero] at hs
      exact ⟨lay, hlay, by simpa using hs⟩
  · cases h

/-- **K14's second part accepting: the new tree's shape is the layout's, at the public shape and the
state's codes.** -/
theorem laid_tree_shape {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    ∃ (lay : TreeLay) (tO : Tree),
      layTrees s.st.codes #[⟨p.S.omega, p.S.omegaLeafClass⟩] = some lay ∧
      s'.book.trees[s.book.trees.size]? = some tO ∧ tO.shape = lay.shapes.getD 0 {} ∧
      tO.parts = #[s.st.oracles.size] := by
  obtain ⟨x, a, dot, b, _, ha, _, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  obtain ⟨q, t, y, a0, d₁, _, _, hy, h0, _, h1, h2⟩ := takeOver_inv _ _ _ _ _ ha
  obtain ⟨y', hy', hsh⟩ := takeOver_shape _ _ _ _ _ ha
  obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
  rw [hsh] at h0
  obtain ⟨lay, hlay, hO⟩ := adoptP_one_tree _ _ _ _ _ h0
  have eb : b.book = a0.2.book :=
    (addRowP_book _ _ _ _ hb).trans ((joinP_book _ _ _ _ _ h2).trans (elsewhereP_book _ _ _ _ _ h1))
  refine ⟨lay, { shape := lay.shapes.getD 0 {}, number := t.number, src := t.src
                 parts := #[s.st.oracles.size] }, hlay, ?_, rfl, rfl⟩
  show b.book.trees[s.book.trees.size]? = _
  rw [eb]
  exact hO

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.adoptP_one_tree
#print axioms VerifiableInference.Desc.Third.Law.laid_tree_shape
