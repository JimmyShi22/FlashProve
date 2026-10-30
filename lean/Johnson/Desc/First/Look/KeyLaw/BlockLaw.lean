-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/BlockLaw.lean: WHAT THE KIND'S OWN BLOCK LEAVES WHERE IT SAYS YES,
for every seat in a carried record and every place: a ledger was open with its count at the place's
first hidden value; the hearing (hearE, Statement.lean) at the planner's own entries returned; the
record behind is the seat's "put" of what was heard.

Main names:
  bindX, namedX, needX: "do", a named value and a test in Except, backward.
  block_law: THE BLOCK's YES.
  okView_shown: a view whose words are below the prime: so are its rounds', shown without the sealed
    digest and without the opened columns.

Limits. Nothing on the three runs of claims.

-/
import Johnson.Desc.First.Look.KeyLaw.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork)

theorem bindX {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem namedX {α : Type} {n : String} {o : Option α} {a : α} (h : named n o = .ok a) :
    o = some a := by
  cases o with
  | none => cases h
  | some x =>
    cases h
    rfl

theorem needX {n : String} {c : Bool} {u : Unit} (h : need n c = .ok u) : c = true := by
  cases c with
  | false => cases h
  | true => rfl

/-- **The block's yes.** -/
theorem block_law {S Cl : Type} (σ : SeatG S Cl) (before : List (ℕ × ℕ)) (bits : ℕ)
    (guests : List (First.Look.Guest S Cl)) (p : PG) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (lookupKind σ before bits guests p).decide s rs gs = .ok s') :
    ∃ F g G es, σ.fork s = some F ∧ F.next = p.first ∧ F.ns = p.ns ∧ p.entries = some es ∧
      hearE p.face es F rs = some (g, G) ∧ s' = σ.put s g G := by
  have h' : (do
      let F ← named "K3: no ledger is open" (σ.fork s)
      need "K3: rows are owed in front" (σ.owed s).noneWaits
      need "K3: the ledger's count of slots" (F.next == p.first)
      need "K3: the ledger's room" (F.ns == p.ns)
      let x ← named "K3: the hearing" (hearG p F rs)
      pure (σ.put s x.1 x.2) : Except String S) = .ok s' := h
  obtain ⟨F, h1, h'⟩ := bindX h'
  obtain ⟨_, -, h'⟩ := bindX h'
  obtain ⟨_, h3, h'⟩ := bindX h'
  obtain ⟨_, h4, h'⟩ := bindX h'
  obtain ⟨x, h5, h'⟩ := bindX h'
  cases h'
  have e5 := namedX h5
  rw [hearG_eq] at e5
  cases he : p.entries with
  | none => rw [he] at e5; cases e5
  | some es =>
    rw [he] at e5
    exact ⟨F, x.1, x.2, es, namedX h1, by simpa using needX h3, by simpa using needX h4, rfl, e5,
      rfl⟩

/-- A view whose words are below the prime. -/
theorem okView_shown (v : Fmt.View) (h : viewWordsBelowPrime v = true) :
    viewWordsBelowPrime ⟨v.rounds.map noDigest, []⟩ = true := by
  unfold viewWordsBelowPrime at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨?_, rfl⟩
  rw [List.all_map]
  exact h.1

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.block_law
#print axioms VerifiableInference.Desc.K3.KeyLaw.okView_shown
