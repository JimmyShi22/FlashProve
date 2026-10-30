-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/KeepsAllM3.lean: kind K13, the members' batching: THE KIND's WHOLE CLAUSE ON
WHAT ITS STEP LEAVES AND BY HOW MUCH IT MOVES THE LEDGERS (`K13KeepsAll`): `K13Keeps` (KeepsM3.lean
of this folder) and `K13Ledger` (LedgerM3.lean) together, and that a return of the joined
sub-protocol's decision from a state without a mark of failure gives it. One definition, and
statements with their proofs.
Main names:
  `K13KeepsAll`: **the definition.**
  `withClaim_keepsAll`, `atM3_keepsAll`: **a return of the decision gives it.**
  `K13KeepsAll.ledgerAt`: the index masks' message's ledger behind, in the library's own reader's
    words.

What is not claimed. What the two files leave out: a message's fields `groups` and `spentAsMask`;
which entries are taken. Nothing on any property.

-/
import Johnson.Desc.K13.Honest.KeepsM3
import Johnson.Desc.K13.Honest.LedgerM3
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (dOf)

/-- **What the kind's step leaves of the state, and by how much it moves the ledgers.** -/
def K13KeepsAll (P : Where) (s s' : S) : Prop := K13Keeps s s' ∧ K13Ledger P s s'

/-- From a state without a mark to the state that the kind's step lays, at what the taking returns.
-/
theorem withClaim_keepsAll {P : Where} {s : S} {t : List ℕ × St} (h0 : s.failed = none)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (msg : Array OracleNotice) (row : TensorRow) :
    K13KeepsAll P s (withClaim s t.2.st msg row) :=
  ⟨withClaim_keeps h0 ht msg row, withClaim_ledger ht msg row⟩

variable {Cl : Type}

/-- **A return of the joined sub-protocol's decision, from a state without a mark of failure, gives
`K13KeepsAll`.** -/
theorem atM3_keepsAll {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h0 : s.failed = none)
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') : K13KeepsAll P s s' :=
  ⟨atM3_keepsM3 h0 h, atM3_ledgerM3 h⟩

/-- **The index masks' message's ledger, in the library's own reader's words** (`Walk.Law.ledgerAt`,
Johnson/Top/H0/Walk/FrameLaw.lean): behind the step it is the ledger in front, moved on by the
takes. -/
theorem K13KeepsAll.ledgerAt {P : Where} {s s' : S} (h : K13KeepsAll P s s') :
    Johnson.Desc.First.Walk.Law.ledgerAt s' =
      (Johnson.Desc.First.Walk.Law.ledgerAt s).map (Law.taken^[Batt.masksOf P.lin.kCol]) := by
  have eo : s'.out = s.out := h.1.2.2.2.2.1
  have e := h.2.own
  unfold msgsOf at e
  rw [Array.getElem?_map, Array.getElem?_map] at e
  unfold Johnson.Desc.First.Walk.Law.ledgerAt
  rw [eo]
  cases h1 : s'.st.oracles[s.out.indexMasks]? with
  | none =>
    rw [h1] at e
    cases h2 : s.st.oracles[s.out.indexMasks]? with
    | none => rfl
    | some x =>
      rw [h2] at e
      cases e
  | some x' =>
    rw [h1] at e
    cases h2 : s.st.oracles[s.out.indexMasks]? with
    | none =>
      rw [h2] at e
      cases e
    | some x =>
      rw [h2] at e
      exact congrArg MsgSh.ledger (Option.some.inj e)

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.withClaim_keepsAll
#print axioms VerifiableInference.Desc.K13.Honest.atM3_keepsAll
#print axioms VerifiableInference.Desc.K13.Honest.K13KeepsAll.ledgerAt
