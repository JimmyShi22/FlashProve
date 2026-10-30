-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/LedgerM3.lean: kind K13, the members' batching: BY HOW MUCH THE JOINED
SUB-PROTOCOL's STEP MOVES THE LEDGERS (`K13Ledger`): the sentence that `K13Keeps` (KeepsM3.lean of
this folder) leaves out. One definition, and statements with their proofs.

The step takes 1 + 2 kCol mask entries of the index masks' message. `K13Ledger P s s'` says, of the
list of all oracle messages' shapes and ledgers (`msgsOf`, ShapeStep.lean): behind the step it is
the list in front, with the ledger of the message number `s.out.indexMasks` moved on by so many
takes (the library's `taken`, Johnson/Desc/K13/Law/LedgerWithin.lean, so many times). So every other
message's ledger is as it was.
Main names:
  `K13Ledger`: **the definition.**
  `takenN_left`, `takenN_closed`, `takenN_rows`: behind n takes a ledger has n less left (cut off at
    0), and is shut or open, with the same numbers of rows, as it was.
  `withClaim_ledger`, `atM3_ledgerM3`: **a return of the decision gives it.**
  `K13Ledger.other`, `K13Ledger.own`: what it says of another message, and of that one.

What is not claimed. Which entries are taken (the field `next` behind the takes is the library's
search, so many times). That the ledger had so many left: where the decision returns it had
(`takeMasks_left`, ShapeBack.lean). Nothing on any property.

-/
import Johnson.Desc.K13.Honest.ShapeStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

/-- **By how much the kind's step moves the ledgers.** -/
def K13Ledger (P : Where) (s s' : S) : Prop :=
  msgsOf s'.st = (msgsOf s.st).modify s.out.indexMasks (MsgSh.takes (Batt.masksOf P.lin.kCol))

/-- Behind n takes a ledger has n less left. -/
theorem takenN_left (l : Ledger) : ∀ n : ℕ, (taken^[n] l).left = l.left - n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', show (taken (taken^[n] l)).left = (taken^[n] l).left - 1
      from rfl, takenN_left l n]
    omega

/-- It is shut or open as it was. -/
theorem takenN_closed (l : Ledger) : ∀ n : ℕ, (taken^[n] l).closed = l.closed
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', show (taken (taken^[n] l)).closed = (taken^[n] l).closed
      from rfl, takenN_closed l n]

/-- Its two numbers of rows are as they were. -/
theorem takenN_rows (l : Ledger) : ∀ n : ℕ,
    (taken^[n] l).rows = l.rows ∧ (taken^[n] l).logRows = l.logRows
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact takenN_rows l n

/-- From a state to the state that the kind's step lays, at what the taking returns. -/
theorem withClaim_ledger {P : Where} {s : S} {t : List ℕ × St}
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (msg : Array OracleNotice) (row : TensorRow) :
    K13Ledger P s (withClaim s t.2.st msg row) := takeMasks_msgs ht

variable {Cl : Type}

/-- **A return of the joined sub-protocol's decision gives `K13Ledger`.** -/
theorem atM3_ledgerM3 {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') : K13Ledger P s s' := by
  obtain ⟨t, msg, row, ht, rfl⟩ := atM3_return_form h
  exact withClaim_ledger ht msg row

/-- Another message's shape and ledger are as they were. -/
theorem K13Ledger.other {P : Where} {s s' : S} (h : K13Ledger P s s') {j : ℕ}
    (hj : s.out.indexMasks ≠ j) : (msgsOf s'.st)[j]? = (msgsOf s.st)[j]? := by
  rw [h, Array.getElem?_modify, if_neg hj]

/-- The index masks' message: its shape is as it was; its ledger is moved on by the takes. -/
theorem K13Ledger.own {P : Where} {s s' : S} (h : K13Ledger P s s') :
    (msgsOf s'.st)[s.out.indexMasks]? =
      ((msgsOf s.st)[s.out.indexMasks]?).map (MsgSh.takes (Batt.masksOf P.lin.kCol)) := by
  rw [h, Array.getElem?_modify, if_pos rfl]

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.takenN_left
#print axioms VerifiableInference.Desc.K13.Honest.takenN_closed
#print axioms VerifiableInference.Desc.K13.Honest.takenN_rows
#print axioms VerifiableInference.Desc.K13.Honest.withClaim_ledger
#print axioms VerifiableInference.Desc.K13.Honest.atM3_ledgerM3
#print axioms VerifiableInference.Desc.K13.Honest.K13Ledger.other
#print axioms VerifiableInference.Desc.K13.Honest.K13Ledger.own
