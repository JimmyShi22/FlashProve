-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SeatedAtRecord.lean: WHAT ONE SENDING OF KIND K1 LAYS INTO THE RECORD's BOOK,
WHOLE: `Book.Seated` (Johnson/Desc/Book/Seated.lean) of the book in front and the book behind, at
the kind's decision and at its three blocks at the first chain's record. Statements with their
proofs. It proves nothing of its own on the book: the receiving's law is `Book.recvP_seat`
(Johnson/Desc/Book/BookFitsGround.lean); that what runs behind the receiving leaves the book and
the count of roots is `Ground.coreStill_same` (Johnson/Desc/CoreKeeps.lean) through the kind's walk
(Johnson/Desc/K1/KeepsCore.lean).
Main names:
  `SeatedBy P bk n r bk' n' r'`: bk, n, r: the book, the number of messages and the count of roots
    in front; bk', n', r': behind: `Book.Seated bk bk' P.sent.size n (layOf P) …`: the i-th new
    message is seated at (trees in front + its tree in the layout, its part); older places and
    older trees are as they were; EACH NEW TREE τ HAS THE LAYOUT's SHAPE, THE NUMBER firstTree + (r
    + τ), THE SOURCE "own root r + τ", and just its messages of this sending as parts; the layout
    is what `layTrees` lays of the place's codes and notices; r' = r + the layout's trees; n' = n +
    the place's messages.
  `decideSend_seated`: the kind's decision. `sendAtS_seated`, `commitAtS_seated`,
    `firstAtS_seated`: **the three blocks.**

What is not claimed. That what a block DECLARES (its field "oracles") is that layout: another file's
(Johnson/Desc/K1/Law/Declares.lean). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.BookAtRecord
import Johnson.Desc.K1.Law.SendP3
import Johnson.Desc.K1.KeepsCore
import Johnson.Desc.Book.BookFitsGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (coreOf coreStill_same)

variable {L Cl : Type}

/-- **What one sending lays into the book.** -/
structure SeatedBy (P : Par) (bk : TreeBook) (n r : Nat) (bk' : TreeBook) (n' r' : Nat) :
    Prop where
  lay : layTrees P.codes P.sent = some (layOf P)
  seated : Book.Seated bk bk' P.sent.size n (layOf P) (fun τ => P.gp.firstTree + (r + τ))
    (fun τ => .own (r + τ))
  roots : r' = r + (layOf P).shapes.size
  msgs : n' = n + P.sent.size

/-- **The kind's decision.** -/
theorem decideSend_seated (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    SeatedBy P d.book d.st.oracles.size d.roots d'.book d'.st.oracles.size d'.roots := by
  have hb := decideSend_booked P owed d d' r₁ r₂ ids h
  obtain ⟨d₁, hr, _⟩ := decideSend_parts P owed d d' r₁ r₂ ids h
  obtain ⟨ha, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  obtain ⟨_, lay, hl, hS⟩ := Book.recvP_seat _ d d₁ P.sent ids hr
  obtain ⟨_, lay', hl', _, rfl⟩ := (recvP_iff _ d d₁ P.sent ids).1 hr
  obtain rfl : lay = lay' := Option.some.inj (hl.symm.trans hl')
  rw [ha.2.1] at hl
  have hlay : layOf P = lay := by
    unfold layOf
    rw [hl]
    rfl
  refine ⟨by rw [hlay]; exact hl, ?_, rfl, hb.msgs⟩
  show Book.Seated d.book (recvD P.gp.firstTree d P.sent (layOf P)).book _ _ _ _ _
  rw [hlay]
  exact hS

/-- **W's sending.** -/
theorem sendAtS_seated (P : Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    SeatedBy P s.book s.st.oracles.size s.roots s'.book s'.st.oracles.size s'.roots := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (map_ok _ _ _).1 hy
      exact decideSend_seated P _ _ x.2 r₁ r₂ x.1 hx
    · cases h
  · cases h

theorem putLink_roots (s : S) (X : LinkCtx) : (s.putLink X).roots = s.roots := by
  unfold S.putLink
  split <;> first | rfl | (split <;> rfl)

theorem putFork_roots (s : S) (X : Fork) : (s.putFork X).roots = s.roots := by
  unfold S.putFork
  split <;> first | rfl | (split <;> rfl)

/-- **A segment's later moment.** -/
theorem commitAtS_seated (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    SeatedBy P s.book s.st.oracles.size s.roots s'.book s'.st.oracles.size s'.roots := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays _ y _ gs hy
    obtain ⟨_, e2⟩ := joinOwnP_book _ _ _ _ _ _ _ h3
    obtain ⟨e1, e3⟩ := RelCore.joinOwnP_keeps coreStill_same _ _ _ _ _ _ h3
    have hb := decideSend_seated P _ _ d₁ r₁ r₂ ids h2
    rw [(putFork_left _ _).1, (putLink_left _ _).1, (putFork_st _ _).1, (putLink_st _ _).1,
      putFork_roots, putLink_roots]
    show SeatedBy P s.book s.st.oracles.size s.roots y.held.w.book y.held.w.st.oracles.size
      y.held.w.roots
    have e1' : y.held.w.book = d₁.book := e1
    have e3' : y.held.w.roots = d₁.roots := e3
    rw [e1', e2, e3']
    exact hb
  · cases h

/-- **The first segment's opening.** -/
theorem firstAtS_seated (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    SeatedBy (firstPar q gp) s.book s.st.oracles.size s.roots s'.book s'.st.oracles.size
      s'.roots := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  obtain ⟨g, d₁, ids, d₂, h3, h4, f₁, own, mine, f₂, h5⟩ := firstOwn_ok _ _ _ _ _ _ _ h2
  obtain ⟨a1, a2⟩ := newGroupP_book _ _ _ _ _ h3
  have a3 : d₁.roots = _ := (coreStill_same.newGroup _ d₁ _ _ g h3).2
  obtain ⟨_, b2⟩ := joinOwnP_book _ _ _ _ _ _ _ h5
  obtain ⟨b1, b3⟩ := RelCore.joinOwnP_keeps coreStill_same _ _ _ _ _ _ h5
  have hb := decideSend_seated _ _ d₁ d₂ r₁ r₂ ids h4
  show SeatedBy _ s.book s.st.oracles.size s.roots d'.book d'.st.oracles.size d'.roots
  have b1' : d'.book = d₂.book := b1
  have b3' : d'.roots = d₂.roots := b3
  rw [b1', b2, b3']
  rw [a1, a2, a3] at hb
  exact hb

end VerifiableInference.Desc.K1
