-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/KeepsM3.lean: kind K13, the members' batching: WHAT THE JOINED
SUB-PROTOCOL's STEP LEAVES OF THE FIRST CHAIN's STATE AS IT WAS (`K13Keeps`), and that a return of
its decision from a state without a mark of failure gives it. One definition, and statements with
their proofs.

The state has nine fields (Johnson/Desc/First/State.lean). The step writes three: `here` (the chain
stands at its end, with the claim laid and W's message announced), `rowsOwed` (laid to none) and
`st`, of which it turns the ledger of the index masks' message alone. `K13Keeps s s'` says: s' bears
no mark of failure; the five fields `book`, `roots`, `check`, `out`, `req` are as they were; of the
statement: the codes and the groups are as they were, and each oracle message has the shape, the
mark "sampled", the sample rows and the pad that it had (the library's `SameAll`,
Johnson/Desc/K13/Law/PinDec.lean).
Main names:
  `K13Keeps`: **the definition.**
  `takeMasks_groups`: the taking of mask entries leaves the statement's groups.
  `withClaim_keeps`: it holds from s to `withClaim s t.2.st msg row`, at what the taking returns.
  `atM3_keepsM3`: **a return of the decision gives it**, from a state without a mark.

What is not claimed. An oracle message has seven fields; `SameAll` holds four. That the other three,
`groups`, `ledger` and `spentAsMask`, are as they were: the ledger of the index masks' message moves
on; that no other message's ledger, and no message's `groups` or `spentAsMask`, turns is true by the
text and is not said here. Of the eight clauses the first is absolute (no mark behind), so `K13Keeps
s s` is false at a state with a mark. The clauses are laid for whoever reads these fields behind the
step; by how much the ledgers move is said in LedgerM3.lean of this folder. Nothing on any property.

-/
import Johnson.Desc.K13.Honest.ShapeStep
import Johnson.Desc.K13.Law.PinDec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

/-- **What the kind's step leaves of the state as it was**; and the state behind bears no mark of
failure. -/
def K13Keeps (s s' : S) : Prop :=
  s'.failed = none ∧ s'.book = s.book ∧ s'.roots = s.roots ∧ s'.check = s.check ∧
    s'.out = s.out ∧ s'.req = s.req ∧ SameAll s.st s'.st ∧ s'.st.groups = s.st.groups

/-- The taking of one mask entry leaves the groups. -/
theorem takeMask_groups {d d' : St} {o n : ℕ} (h : takeMaskP d o = some (n, d')) :
    d'.st.groups = d.st.groups := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none =>
      rw [hl] at h
      cases h
    | some l =>
      rw [hl] at h
      have e : d' = _ := (congrArg Prod.snd (Option.some.inj h)).symm
      subst e
      rfl
  · cases h

/-- So does the taking of several. -/
theorem takeMasksInto_groups (o : ℕ) : ∀ (n : ℕ) (d : St) (acc : Array ℕ) (t : List ℕ × St),
    takeMasksInto o n d acc = some t → t.2.st.groups = d.st.groups
  | 0, d, acc, t, h => by
    have e : some (acc.toList, d) = some t := h
    rw [← Option.some.inj e]
  | n + 1, d, acc, t, h => by
    unfold takeMasksInto at h
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at h
      cases h
    | some q =>
      obtain ⟨i, d'⟩ := q
      rw [hm] at h
      exact (takeMasksInto_groups o n d' _ t h).trans (takeMask_groups hm)

/-- The same, as the text calls it. -/
theorem takeMasks_groups {d : St} {o n : ℕ} {t : List ℕ × St} (h : takeMasksP d o n = some t) :
    t.2.st.groups = d.st.groups := takeMasksInto_groups o n d #[] t h

/-- From a state without a mark to the state that the kind's step lays, at what the taking returns.
-/
theorem withClaim_keeps {s : S} {o n : ℕ} {t : List ℕ × St} (h0 : s.failed = none)
    (ht : takeMasksP (dOf s) o n = some t) (msg : Array OracleNotice) (row : TensorRow) :
    K13Keeps s (withClaim s t.2.st msg row) :=
  ⟨h0, rfl, rfl, rfl, rfl, rfl, takeMasks_same ht, takeMasks_groups ht⟩

variable {Cl : Type}

/-- **A return of the joined sub-protocol's decision, from a state without a mark of failure, gives
`K13Keeps`.** -/
theorem atM3_keepsM3 {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h0 : s.failed = none)
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') : K13Keeps s s' := by
  obtain ⟨t, msg, row, ht, rfl⟩ := atM3_return_form h
  exact withClaim_keeps h0 ht msg row

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.takeMask_groups
#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_groups
#print axioms VerifiableInference.Desc.K13.Honest.takeMasks_groups
#print axioms VerifiableInference.Desc.K13.Honest.withClaim_keeps
#print axioms VerifiableInference.Desc.K13.Honest.atM3_keepsM3
