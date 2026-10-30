-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Left.lean: WHAT AN ACCEPT OF THE CODE SWITCH LEAVES OF THE VERIFIER's STATE,
as
far as the claims that stay open across the switch read it. One structure of Prop, five theorems. A
law file: no sub-protocol imports it.

Why. Four sorts of claims stay open across a code switch (Johnson/Top/H0/K2Ties/T5.lean). Of the
verifier's state they read: the request's words; the pending claims on the committed table and the
number of the index masks' message (`S.out`, through `S.rows`); of the statement: the codes, the
shape of an earlier oracle message, the sample rows of an earlier sampled one; of the book: where an
earlier message sits, and that tree's number. The switch sends new messages and lays new rows: it
turns none of these.

What is said.
  `Left s s'`: these parts of s' are those of s.
  `Left.refl`, `Left.trans`: so it passes a quiet step in front of the kind's decision and one
  behind.
  `left_of_yes`: AN ACCEPT OF THE KIND's DECISION (`decideWith sendByL8`,
    Johnson/Top/H0/Tw/K2C/Kind.lean) GIVES IT: by `keeps` (Laws.lean), `yes_grows` and
    `yes_keeps_whole` at the sample rows' relation (KeepsWhole.lean;
    Johnson/Desc/K1/Law/SmpStay.lean), `yes_seated` (SeatedAt.lean).
  `left_of_same`: a step that turns neither the statement, the book, `out`, `req` nor the mark, and
    that ends outside the members' places as it began, gives it.

Limits. (1) Of the kind's decision alone: what stands in a written description is that decision
behind a door (a quiet step in front, one behind, guards): each door owes `Left` too. (2) One
direction: nothing is said of what the switch lays. (3) No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Top.H0.Tw.K2C.Laws
import Johnson.Top.H0.Tw.K2C.Reply
import Johnson.Top.H0.Tw.K2C.HeadRest
import Johnson.Top.H0.Tw.K2C.KeepsWhole
import Johnson.Top.H0.Tw.K2C.SeatedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes OnBytes.Model
open _root_.Tw.K2 (sendByL8)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith)

/-- **What an accept of the code switch leaves of the verifier's state.** -/
structure Left (s s' : S) : Prop where
  failed : s'.failed = s.failed
  out : s'.out = s.out
  req : s'.req = s.req
  /-- the pending claims on the committed table, as the table of joints reads them -/
  rows : s'.rows = s.rows
  /-- the codes; every earlier oracle message stands there with its shape -/
  grows : Desc.Grows s.st s'.st
  /-- every earlier sampled oracle message stands there with its sample rows -/
  smp : Desc.K1.SmpStay s.st s'.st
  /-- every earlier message sits where it sat -/
  places : ∀ (j : Nat) (q : Nat × Nat), s.book.place[j]? = some q → s'.book.place[j]? = some q
  /-- every earlier tree has its number -/
  trees : ∀ (j : Nat) (t : Tree), s.book.trees[j]? = some t →
    ∃ t' : Tree, s'.book.trees[j]? = some t' ∧ t'.number = t.number

theorem Left.refl (s : S) : Left s s :=
  ⟨rfl, rfl, rfl, rfl, Desc.Grows.refl _, Desc.K1.SmpStay.refl _, fun _ _ h => h,
    fun _ t h => ⟨t, h, rfl⟩⟩

theorem Left.trans {a b c : S} (h : Left a b) (k : Left b c) : Left a c :=
  ⟨k.failed.trans h.failed, k.out.trans h.out, k.req.trans h.req, k.rows.trans h.rows,
    Desc.Grows.trans h.grows k.grows, h.smp.trans k.smp,
    fun j q e => k.places j q (h.places j q e),
    fun j t e => by
      obtain ⟨t', e', n'⟩ := h.trees j t e
      obtain ⟨t'', e'', n''⟩ := k.trees j t' e'
      exact ⟨t'', e'', n''.trans n'⟩⟩

/-- The pending claims, where the state does not stand at the members' places. -/
theorem rows_off {s : S} (h : ∀ a, s.here ≠ .mem a) : s.rows = s.out.pending := by
  unfold S.rows
  split
  · rename_i a e
    exact absurd e (h a)
  · rfl

/-- A step that turns none of the parts read. -/
theorem left_of_same {s s' : S} (h1 : s'.failed = s.failed) (h2 : s'.out = s.out)
    (h3 : s'.req = s.req) (h4 : s'.st = s.st) (h5 : s'.book = s.book)
    (h6 : ∀ a, s.here ≠ .mem a) (h7 : ∀ a, s'.here ≠ .mem a) : Left s s' := by
  refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rows_off h6, rows_off h7, h2]
  · rw [h4]
    exact Desc.Grows.refl _
  · rw [h4]
    exact Desc.K1.SmpStay.refl _
  · intro j q e
    rw [h5]
    exact e
  · intro j t e
    rw [h5]
    exact ⟨t, e, rfl⟩

/-- **An accept of the kind's decision leaves these parts.** -/
theorem left_of_yes {p : P2} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : decideWith sendByL8 p s rs gs = .ok s') : Left s s' := by
  obtain ⟨k1, k2, k3⟩ := K2.keeps _ _ _ _ _ _ h
  obtain ⟨x, lay, _, _, _, B⟩ := K2.yes_seated h
  have hh : (∀ a, s.here ≠ .mem a) ∧ ∀ a, s'.here ≠ .mem a := by
    rcases K2.stands _ _ _ _ _ _ h with ⟨_, e⟩ | ⟨_, a, e⟩ | ⟨_, a, e⟩
    · have e' := K2.switchBetween h e
      exact ⟨fun a c => (by cases e.symm.trans c), fun a c => (by cases e'.symm.trans c)⟩
    · obtain ⟨b, e', _⟩ := K2.switchHead_rest h e
      exact ⟨fun a c => (by cases e.symm.trans c), fun a c => (by cases e'.symm.trans c)⟩
    · obtain ⟨b, e'⟩ := K2.switchFin h e
      exact ⟨fun a c => (by cases e.symm.trans c), fun a c => (by cases e'.symm.trans c)⟩
  refine ⟨k1, k2, k3, ?_, K2.yes_grows h, K2.yes_keeps_whole Desc.K1.groundKeeps_smpStay h, ?_, ?_⟩
  · rw [rows_off hh.1, rows_off hh.2, k2]
  · intro j q e
    have hj : j < s.book.place.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at e
      cases e
    rw [B.places j hj]
    exact e
  · intro j t e
    have hj : j < s.book.trees.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at e
      cases e
    obtain ⟨t₀, t', e0, e1, n, _⟩ := B.trees j hj
    rw [e] at e0
    obtain rfl := Option.some.inj e0
    exact ⟨t', e1, n⟩

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.Left.trans
#print axioms VerifiableInference.Desc.First.K2Ties.left_of_same
#print axioms VerifiableInference.Desc.First.K2Ties.left_of_yes
