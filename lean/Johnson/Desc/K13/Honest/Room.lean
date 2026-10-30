--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Room.lean: THE LEDGER's ROOM, FROM THE PREMISES TO THE RETURN: where the
ledger of an oracle message's mask entries is open and has n entries left, the taking of n entries
(`takeMasksP`, Johnson/Desc/First/Base/Ground.lean) returns.
Statements with their proofs.

Why. Kind K13's batching takes 1 + 2 kCol fresh mask entries off the ledger of the index masks'
message, and rejects where they are not left ("K13.mask-entries", Johnson/Desc/K13/Text.lean). A
rejection there harms no soundness law, so no law of the kind counts the room. An honest prover's
acceptance needs it.
Main names:
  `LeftAt st o n`: the message o is there, has a ledger, the ledger is not shut, and at least n
    entries are left. `leftAtC`: the same as a test with code; `leftAtC_iff`.
  `takeMask_returns`: one entry is handed out, and one less is left.
  `takeMasks_returns`: **the taking of n entries returns.**
  `leftAt_of_ledgerAt`: in the count of the kind's laws (`LedgerAt`,
    Johnson/Desc/K13/Law/LedgerWithin.lean): at the ledger of k takes, open, where k + n is at most
    the shape's count of free entries.

What is not claimed. That the ledger at the batching's place is not shut: no law of the kind says
it. That it has that room: that is a comparison on
the plan (the free entries of the index masks' message against all takes in front and the
batching's own), not made here. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.LedgerWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open VerifiableInference.Desc.Ground (takeMaskP takeMaskL takeMasksInto takeMasksP ok has)
open Desc.Plain (DState)
open VerifiableInference.Desc.K13.Law

/-- The message o has an open ledger with at least n entries left. -/
def LeftAt (st : Statement) (o n : ℕ) : Prop :=
  ∃ (x : Oracle) (l : Ledger), st.oracles[o]? = some x ∧ x.ledger = some l ∧ l.closed = false ∧
    n ≤ l.left

/-- The same as a test with code. -/
def leftAtC (st : Statement) (o n : ℕ) : Bool :=
  match (st.oracles[o]?).bind (·.ledger) with
  | some l => !l.closed && decide (n ≤ l.left)
  | none => false

/-- The test says what the sentence says. -/
theorem leftAtC_iff (st : Statement) (o n : ℕ) : leftAtC st o n = true ↔ LeftAt st o n := by
  unfold leftAtC LeftAt
  constructor
  · intro h
    cases hx : st.oracles[o]? with
    | none =>
      rw [hx] at h
      cases h
    | some x =>
      rw [hx] at h
      cases hl : x.ledger with
      | none =>
        have h' : (match x.ledger with
          | some l => !l.closed && decide (n ≤ l.left)
          | none => false) = true := h
        rw [hl] at h'
        cases h'
      | some l =>
        have h' : (match x.ledger with
          | some l => !l.closed && decide (n ≤ l.left)
          | none => false) = true := h
        rw [hl] at h'
        have h2 : (!l.closed && decide (n ≤ l.left)) = true := h'
        rw [Bool.and_eq_true] at h2
        exact ⟨x, l, rfl, hl, by simpa using h2.1, of_decide_eq_true h2.2⟩
  · rintro ⟨x, l, hx, hl, hc, hn⟩
    rw [hx]
    show (match x.ledger with
      | some l => !l.closed && decide (n ≤ l.left)
      | none => false) = true
    rw [hl]
    show (!l.closed && decide (n ≤ l.left)) = true
    rw [hc, decide_eq_true hn]
    rfl

variable {L : Type}

/-- **One entry is handed out**, and one less is left. -/
theorem takeMask_returns {d : DState L} {o n : ℕ} (h : LeftAt d.st o (n + 1)) :
    ∃ (i : ℕ) (d' : DState L), takeMaskP d o = some (i, d') ∧ LeftAt d'.st o n := by
  obtain ⟨x, l, hx, hl, hc, hn⟩ := h
  have hb : (d.st.oracles[o]?).bind (·.ledger) = some l := by
    rw [hx]
    exact hl
  have hok : ok (takeMaskL d.st o) = true := by
    simp only [ok, takeMaskL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, hb]
    refine ⟨by rw [hx]; rfl, ?_, ?_, ?_⟩
    · rw [hx]
      show x.ledger.isSome = true
      rw [hl]
      rfl
    · show (!l.closed) = true
      rw [hc]
      rfl
    · show decide (0 < l.left) = true
      exact decide_eq_true (by omega)
  refine ⟨nextOf l, { d with st := layLedger d.st o (taken l) }, ?_, ?_⟩
  · unfold takeMaskP
    rw [if_pos hok, hb]
    rfl
  · exact ⟨_, taken l, layLedger_at hx (taken l), rfl, hc, by show n ≤ l.left - 1; omega⟩

/-- The loop of the taking returns. -/
theorem takeMasksInto_returns (o : ℕ) : ∀ (n : ℕ) (d : DState L) (acc : Array ℕ), LeftAt d.st o n →
    ∃ t, takeMasksInto o n d acc = some t
  | 0, d, acc, _ => ⟨(acc.toList, d), rfl⟩
  | n + 1, d, acc, h => by
    obtain ⟨i, d', ht, h'⟩ := takeMask_returns h
    obtain ⟨t, hh⟩ := takeMasksInto_returns o n d' (acc.push i) h'
    refine ⟨t, ?_⟩
    unfold takeMasksInto
    rw [ht]
    exact hh

/-- **The taking of n entries returns.** -/
theorem takeMasks_returns {d : DState L} {o n : ℕ} (h : LeftAt d.st o n) :
    ∃ t, takeMasksP d o n = some t :=
  takeMasksInto_returns o n d #[] h

/-- In the count of the kind's laws. -/
theorem leftAt_of_ledgerAt {st : Statement} {o k n : ℕ} (h : LedgerAt st o k)
    (hc : ∀ x l, st.oracles[o]? = some x → x.ledger = some l → l.closed = false)
    (hn : ∀ x, st.oracles[o]? = some x → k + n ≤ Send.freeMaskEntries x.shape.maskRows
      (st.codes.mask.getD x.shape.maskCode default).ell x.shape.answers) : LeftAt st o n := by
  obtain ⟨x, l, hx, hl, _, _, _, _, hleft, _⟩ := h
  have := hn x hx
  exact ⟨x, l, hx, hl, hc x l hx hl, by omega⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.leftAtC_iff
#print axioms VerifiableInference.Desc.K13.Honest.takeMask_returns
#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_returns
#print axioms VerifiableInference.Desc.K13.Honest.takeMasks_returns
#print axioms VerifiableInference.Desc.K13.Honest.leftAt_of_ledgerAt
