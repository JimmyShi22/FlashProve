-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/EarlierTreesUnchanged.lean: a sending of kind K1 leaves every older tree of the record's
book as it was. It stands beside `Booked` (Johnson/Desc/K1/Law/BookAtRecord.lean), which says where
the new messages sit and how many trees come, and nothing on the older trees.

Main names: `TreesOlder`; `treesSent_older`, `partsLaid_older` (the two functions that write the
book's trees); `decideSend_treesOlder` (the kind's decision); `sendAtS_treesOlder`,
`commitAtS_treesOlder`, `firstAtS_treesOlder` (the three blocks at the first chain's record).

What is not claimed. Nothing on the new trees. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.BookAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.First (S)

variable {L Cl : Type}

/-- Every tree of the book in front stands in the book behind, at its number, as it was. -/
def TreesOlder (bk bk' : TreeBook) : Prop :=
  ∀ j, j < bk.trees.size → bk'.trees[j]? = bk.trees[j]?

theorem TreesOlder.refl (bk : TreeBook) : TreesOlder bk bk := fun _ _ => rfl

theorem treesSent_older (first : Nat) : ∀ (l : List TreeShape) (roots : Nat) (trees : Array Tree)
    (j : Nat), j < trees.size → (treesSent first l roots trees)[j]? = trees[j]?
  | [], _, _, _, _ => rfl
  | _ :: l, roots, trees, j, hj => by
    show (treesSent first l (roots + 1) (trees.push _))[j]? = _
    rw [treesSent_older first l _ _ j (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_neg (by omega)]

theorem partsLaid_older (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (trees : Array Tree) (j : Nat) (hj : j < base) :
    (partsLaid sent lay n0 base trees)[j]? = trees[j]? := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih, Array.getElem?_modify, if_neg (by omega)]

/-- **The kind's decision.** -/
theorem decideSend_treesOlder (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    TreesOlder d.book d'.book := by
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  intro j hj
  show (partsLaid _ _ _ d.book.trees.size (treesSent _ _ _ d.book.trees))[j]? = _
  rw [partsLaid_older _ _ _ _ _ j hj, treesSent_older _ _ _ _ j hj]

/-- **W's sending.** -/
theorem sendAtS_treesOlder (P : Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') : TreesOlder s.book s'.book := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (map_ok _ _ _).1 hy
      exact decideSend_treesOlder P _ _ x.2 r₁ r₂ x.1 hx
    · cases h
  · cases h

/-- **A segment's later moment.** -/
theorem commitAtS_treesOlder (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    TreesOlder s.book s'.book := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays _ y _ gs hy
    obtain ⟨e1, _⟩ := joinOwnP_book _ _ _ _ _ _ _ h3
    have hb := decideSend_treesOlder P _ _ d₁ r₁ r₂ ids h2
    rw [(putFork_left _ _).1, (putLink_left _ _).1]
    show TreesOlder s.book y.held.w.book
    rw [e1]
    exact hb
  · cases h

/-- **The first segment's opening.** -/
theorem firstAtS_treesOlder (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    TreesOlder s.book s'.book := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  obtain ⟨g, d₁, ids, d₂, h3, h4, f₁, own, mine, f₂, h5⟩ := firstOwn_ok _ _ _ _ _ _ _ h2
  obtain ⟨a1, _⟩ := newGroupP_book _ _ _ _ _ h3
  obtain ⟨b1, _⟩ := joinOwnP_book _ _ _ _ _ _ _ h5
  have hb := decideSend_treesOlder _ _ d₁ d₂ r₁ r₂ ids h4
  show TreesOlder s.book d'.book
  rw [b1]
  rw [a1] at hb
  exact hb

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sendAtS_treesOlder
#print axioms VerifiableInference.Desc.K1.commitAtS_treesOlder
#print axioms VerifiableInference.Desc.K1.firstAtS_treesOlder
