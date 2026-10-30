-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/TreesStay.lean: OVER A SENDING OF KIND K1 (the first segment's
opening; a segment's later moment) EVERY TREE THAT IS LAID HAS BEEN OPENED AT NO LIST; in one
relation with what the library has already (Johnson/Desc/K1/Law/EarlierTreesUnchanged.lean): every older tree
of the book stays as it is, whole. A relation on the walk's three (statement, book, count of roots)
that the ground's nine calls of such a chain keep; so the library's laws on the kind's two texts
hand it out with no walk of these texts. A tool for `AllOpen`'s clause "a tree of one list has not
been opened" (Returns/ReadOpen.lean). A definition; statements with their proofs.

  `treesStay a b` b's book has at least as many trees as a's · each of a's trees stands in b's book
                    at its number, the same (THE LIBRARY's `TreesOlder`, to the sign) · a tree of
                    b's book at a number from a's number of trees on has `lists` = 0 (new against
                    the elder sealed library's text; of the younger: Returns/FreshTrees.lean's head)
  `treesStay_same`, `treesStay_refl`, `treesStay_trans` where the book is the same · reflexive ·
                    transitive
  `treesStay_recv`, `coreRecv_treesStay` a receiving keeps it, at every number of the chain's first
                    tree; so the library's `CoreRecv` holds of it
  `commit_stays`, `first_stays` THE TOPS: over a yes of `K1.commitAtS` | `K1.firstSegmentOpening`

By, the library's: `recvP_seat` (Johnson/Desc/Book/BookFitsGround.lean), `Seated`
(Johnson/Desc/Book/Seated.lean) · `CoreRecv`, `coreStill_same` (Johnson/Desc/CoreKeeps.lean) ·
`commitAtS_keeps`, `firstAtS_keeps` (Johnson/Desc/K1/KeepsAtSCore.lean). This folder's `recvP_fresh`
(Returns/FreshTrees.lean). `coreRecv_treesStay`'s eight lines on the calls that leave the book are
the library's `coreRecv_places`' (Johnson/IMR/BookFitsSeat.lean). NEAR RELATIVES, NOT CALLED
(another road: they walk the kind's texts, at two rounds): `TreesOlder`, `commitAtS_treesOlder`,
`firstAtS_treesOlder` (Johnson/Desc/K1/Law/EarlierTreesUnchanged.lean): the second clause of the two tops here;
that file says of itself "Nothing on the new trees".

Limits. THE CODE SWITCH DOES NOT KEEP THIS RELATION: its yes counts a list more at older trees: so
no walk over all sub-protocols carries it. Nothing on adopting. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.FreshTrees
import Johnson.Desc.K1.KeepsAtSCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (Core ByC CoreStill CoreRecv coreStill_same)
open VerifiableInference.Desc.K1.RelCore (coreS)

/-- **Every older tree as it was; every new tree opened at no list.** -/
def treesStay (a b : Core) : Prop :=
  a.book.trees.size ≤ b.book.trees.size ∧
    (∀ j, j < a.book.trees.size → b.book.trees[j]? = a.book.trees[j]?) ∧
    ∀ j t, a.book.trees.size ≤ j → b.book.trees[j]? = some t → t.lists = 0

theorem treesStay_same (a b : Core) (h1 : b.book = a.book) (_ : b.roots = a.roots) :
    treesStay a b := by
  refine ⟨by rw [h1], fun j _ => by rw [h1], fun j t hj ht => ?_⟩
  rw [h1, Array.getElem?_eq_none hj] at ht
  cases ht

theorem treesStay_refl (a : Core) : treesStay a a := treesStay_same a a rfl rfl

theorem treesStay_trans {a b c : Core} (h : treesStay a b) (k : treesStay b c) :
    treesStay a c := by
  refine ⟨Nat.le_trans h.1 k.1, fun j hj => ?_, fun j t hj ht => ?_⟩
  · rw [k.2.1 j (Nat.lt_of_lt_of_le hj h.1), h.2.1 j hj]
  · rcases Nat.lt_or_ge j b.book.trees.size with lt | ge
    · rw [k.2.1 j lt] at ht
      exact h.2.2 j t hj ht
    · exact k.2.2 j t ge ht

theorem treesStay_recv {L : Type} (ft : Nat) (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array Nat) (h : Ground.recvP ft d sent = some (ids, d')) :
    treesStay (Ground.coreOf d) (Ground.coreOf d') := by
  obtain ⟨-, lay, -, Se⟩ := Book.recvP_seat ft d d' sent ids h
  refine ⟨?_, fun j hj => Se.trees j hj, fun j t hj ht => recvP_fresh ft d d' sent ids h hj ht⟩
  show d.book.trees.size ≤ d'.book.trees.size
  rw [Se.size]
  exact Nat.le_add_right _ _

theorem coreRecv_treesStay (ft : Nat) : CoreRecv ft treesStay where
  refl := treesStay_refl
  trans := fun h k => treesStay_trans h k
  newGroup := fun d d' c m n h =>
    treesStay_same _ _ (coreStill_same.newGroup d d' c m n h).1
      (coreStill_same.newGroup d d' c m n h).2
  admit := fun d d' o r h =>
    treesStay_same _ _ (coreStill_same.admit d d' o r h).1 (coreStill_same.admit d d' o r h).2
  join := fun d d' g o k h =>
    treesStay_same _ _ (coreStill_same.join d d' g o k h).1 (coreStill_same.join d d' g o k h).2
  addRow := fun d d' g r h =>
    treesStay_same _ _ (coreStill_same.addRow d d' g r h).1 (coreStill_same.addRow d d' g r h).2
  takeMask := fun d d' o n h =>
    treesStay_same _ _ (coreStill_same.takeMask d d' o n h).1
      (coreStill_same.takeMask d d' o n h).2
  closeLedger := fun d d' o h =>
    treesStay_same _ _ (coreStill_same.closeLedger d d' o h).1
      (coreStill_same.closeLedger d d' o h).2
  spendAsMask := fun d d' o h =>
    treesStay_same _ _ (coreStill_same.spendAsMask d d' o h).1
      (coreStill_same.spendAsMask d d' o h).2
  elsewhere := fun d d' m o t h =>
    treesStay_same _ _ (coreStill_same.elsewhere d d' m o t h).1
      (coreStill_same.elsewhere d d' m o t h).2
  recv := fun d d' sent ids h => treesStay_recv ft d d' sent ids h

/-- **Over a segment's later moment.** -/
theorem commit_stays {Cl : Type} (Q : K1.Par) (link moment : Nat) (arrays : Option (List Nat))
    {s v : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS Q link moment arrays : Block S Cl).decide s rs gs = .ok v) :
    treesStay (coreS s) (coreS v) :=
  K1.RelCore.commitAtS_keeps Q (coreRecv_treesStay Q.gp.firstTree) link moment arrays s rs gs v h

/-- **Over the first segment's opening.** -/
theorem first_stays {Cl : Type} (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    {s v : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening q gp : Block S Cl).decide s rs gs = .ok v) :
    treesStay (coreS s) (coreS v) :=
  K1.RelCore.firstAtS_keeps q gp (coreRecv_treesStay gp.firstTree) s rs gs v h

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.treesStay_same
#print axioms VerifiableInference.Desc.K2.Honest.Returns.treesStay_refl
#print axioms VerifiableInference.Desc.K2.Honest.Returns.treesStay_trans
#print axioms VerifiableInference.Desc.K2.Honest.Returns.treesStay_recv
#print axioms VerifiableInference.Desc.K2.Honest.Returns.coreRecv_treesStay
#print axioms VerifiableInference.Desc.K2.Honest.Returns.commit_stays
#print axioms VerifiableInference.Desc.K2.Honest.Returns.first_stays
