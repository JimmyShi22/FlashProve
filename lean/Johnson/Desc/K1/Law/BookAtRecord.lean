-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/BookAtRecord.lean: WHAT A SENDING DOES TO THE RECORD's BOOK OF TREES, AND WHAT
IT LEAVES OF THE CARRIED RECORD. Statements with their proofs, of the kind's decision and of its
three blocks at the first chain's record.

Why. The kind's law names a message by its NUMBER in the statement; a table that speaks of a tenant
(a tree and a place in it) goes from the one to the other by the record's own book
(`TreeBook.place`: for each message's number its tree and place). So whoever ties the two wants to
know where the book stands in front of a sending, and what the sending lays.
Main names:
  `layOf P`: how the place's messages are laid into trees: of the plan alone.
  `Booked P bk n bk' n'`: **what a sending does**: bk, n: the book and the number of messages in
    front; bk', n': behind. The older places stay, in their order; the new messages' places follow:
    message number n + i sits in the tree number (the book's trees in front) + `(layOf P).tree i`,
    at `(layOf P).part i`; the book has `(layOf P).shapes.size` trees more; the statement has
    `P.sent.size` messages more.
  `Booked.older`, `Booked.newer`: read off at a number, where the book in front has a place for
    every message.
  `decideSend_booked`: the kind's decision. `joinOwnP_book`, `newGroupP_book`: what stands around it
    in the blocks leaves the book and the number of messages.
  `sendAtS_booked`, `commitAtS_booked`, `firstAtS_booked`: **the three blocks.**
  `commitAtS_left`, `firstAtS_left`: a mark stays and none is laid; what the links left is as it
    was.

What is not claimed. That the book in front holds the plan's number of trees. That `layOf P` is what
a table's numbers name. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.K1.Law.SeedAtRecord
import Johnson.Desc.K13.Law.K1Ids

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)

variable {L Cl : Type}

/-- How the place's messages are laid into trees. -/
def layOf (P : Par) : TreeLay := (layTrees P.codes P.sent).getD {}

/-- **What a sending does to the book and to the number of messages.** -/
structure Booked (P : Par) (bk : TreeBook) (n : Nat) (bk' : TreeBook) (n' : Nat) : Prop where
  place : bk'.place = bk.place ++ (Array.range P.sent.size).map fun i =>
    (bk.trees.size + (layOf P).tree.getD i 0, (layOf P).part.getD i 0)
  trees : bk'.trees.size = bk.trees.size + (layOf P).shapes.size
  msgs : n' = n + P.sent.size

/-- An older message's place stays. -/
theorem Booked.older {P : Par} {bk bk' : TreeBook} {n n' : Nat} (h : Booked P bk n bk' n')
    {o : Nat} (ho : o < bk.place.size) : bk'.place[o]? = bk.place[o]? := by
  rw [h.place, Array.getElem?_append_left ho]

/-- A new message's place, where the book in front has a place for every message. -/
theorem Booked.newer {P : Par} {bk bk' : TreeBook} {n n' : Nat} (h : Booked P bk n bk' n')
    (hn : bk.place.size = n) {i : Nat} (hi : i < P.sent.size) :
    bk'.place[n + i]? =
      some (bk.trees.size + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) := by
  rw [h.place, ← hn, Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Array.getElem?_map, Array.getElem?_range, if_pos hi]
  rfl

/-- Behind it too the book has a place for every message. -/
theorem Booked.full {P : Par} {bk bk' : TreeBook} {n n' : Nat} (h : Booked P bk n bk' n')
    (hn : bk.place.size = n) : bk'.place.size = n' := by
  rw [h.place, h.msgs, Array.size_append, Array.size_map, Array.size_range, hn]

theorem treesSent_size (first : Nat) : ∀ (l : List TreeShape) (roots : Nat) (trees : Array Tree),
    (treesSent first l roots trees).size = trees.size + l.length
  | [], _, _ => rfl
  | _ :: l, roots, trees => by
    show (treesSent first l (roots + 1) _).size = _
    rw [treesSent_size first l, Array.size_push, List.length_cons]
    omega

theorem partsLaid_size (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (trees : Array Tree) : (partsLaid sent lay n0 base trees).size = trees.size := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih, Array.size_modify]

/-- **The kind's decision.** -/
theorem decideSend_booked (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    Booked P d.book d.st.oracles.size d'.book d'.st.oracles.size := by
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  refine ⟨rfl, ?_, ?_⟩
  · show (partsLaid _ _ _ _ (treesSent _ _ _ _)).size = _
    rw [partsLaid_size, treesSent_size, Array.length_toList]
    rfl
  · show (d.st.oracles.toList ++ outs _ _ _ _ _).toArray.size = _
    rw [List.size_toArray, List.length_append, K13.Law.outs_length, Array.length_toList]
    simp [shapesOf]

theorem joinP_book (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : Ground.joinP d g o kept = some d') :
    d'.book = d.book ∧ d'.st.oracles.size = d.st.oracles.size := by
  unfold Ground.joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, by simp [withMessageInGroup]⟩
  · cases h

theorem joinAll_book (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat)) (d d' : DState L),
    joinAll groundG p g l d = some d' →
      d'.book = d.book ∧ d'.st.oracles.size = d.st.oracles.size
  | [], d, d', h => by
    obtain rfl : d = d' := Option.some.inj h
    exact ⟨rfl, rfl⟩
  | _ :: l, d, d', h => by
    obtain ⟨d₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := joinP_book d d₁ _ _ _ h1
    obtain ⟨b1, b2⟩ := joinAll_book p g l d₁ d' h2
    exact ⟨b1.trans a1, b2.trans a2⟩

/-- The joining leaves the book and the number of messages. -/
theorem joinOwnP_book (p : GPar) (d d' : DState L) (f f' : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (h : joinOwnP groundG p d f sent ids = some (f', d')) :
    d'.book = d.book ∧ d'.st.oracles.size = d.st.oracles.size := by
  unfold joinOwnP at h
  split at h
  · obtain ⟨d₁, h1, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : d₁ = d' := (Prod.mk.inj e).2
    exact joinAll_book p _ _ d d₁ h1
  · cases h

/-- So does the opening of a group. -/
theorem newGroupP_book (d d' : DState L) (code maskCode g : Nat)
    (h : Ground.newGroupP d code maskCode = some (g, d')) :
    d'.book = d.book ∧ d'.st.oracles.size = d.st.oracles.size := by
  unfold Ground.newGroupP at h
  split at h
  · obtain rfl := (Prod.mk.inj (Option.some.inj h)).2
    exact ⟨rfl, rfl⟩
  · cases h

/-! ## The three blocks -/

/-- **W's sending.** -/
theorem sendAtS_booked (P : Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (map_ok _ _ _).1 hy
      exact decideSend_booked P _ _ x.2 r₁ r₂ x.1 hx
    · cases h
  · cases h

theorem putLink_left (s : S) (X : LinkCtx) :
    (s.putLink X).book = s.book ∧ (s.putLink X).failed = s.failed := by
  unfold S.putLink
  split <;> first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩)

theorem putFork_left (s : S) (X : Fork) :
    (s.putFork X).book = s.book ∧ (s.putFork X).failed = s.failed := by
  unfold S.putFork
  split <;> first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩)

/-- **A segment's later moment.** -/
theorem commitAtS_booked (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays _ y _ gs hy
    obtain ⟨e1, e2⟩ := joinOwnP_book _ _ _ _ _ _ _ h3
    have hb := decideSend_booked P _ _ d₁ r₁ r₂ ids h2
    rw [(putFork_left _ _).1, (putLink_left _ _).1, (putFork_st _ _).1, (putLink_st _ _).1]
    show Booked P s.book s.st.oracles.size y.held.w.book y.held.w.st.oracles.size
    rw [e1, e2]
    exact hb
  · cases h

/-- It lays no mark and takes none; what the links left is as it was. -/
theorem commitAtS_left (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.failed = s.failed ∧ s'.out = s.out := by
  refine ⟨?_, (commitAtS_ok P link moment arrays s s' rs gs h).choose_spec.choose_spec.2.2.2⟩
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, _, rfl⟩ := (map_ok _ _ _).1 h
    rw [(putFork_left _ _).2, (putLink_left _ _).2]
    rfl
  · cases h

/-- **The first segment's opening.** -/
theorem firstAtS_booked (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    Booked (firstPar q gp) s.book s.st.oracles.size s'.book s'.st.oracles.size := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  obtain ⟨g, d₁, ids, d₂, h3, h4, f₁, own, mine, f₂, h5⟩ := firstOwn_ok _ _ _ _ _ _ _ h2
  obtain ⟨a1, a2⟩ := newGroupP_book _ _ _ _ _ h3
  obtain ⟨b1, b2⟩ := joinOwnP_book _ _ _ _ _ _ _ h5
  have hb := decideSend_booked _ _ d₁ d₂ r₁ r₂ ids h4
  show Booked _ s.book s.st.oracles.size d'.book d'.st.oracles.size
  rw [b1, b2]
  rw [a1, a2] at hb
  exact hb

/-- It lays no mark and takes none; what the links left is as it was. -/
theorem firstAtS_left (q : Params.First) (gp : GPar) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s rs gs = .ok s') :
    s'.failed = s.failed ∧ s'.out = s.out := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, _, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact ⟨rfl, rfl⟩

end VerifiableInference.Desc.K1
