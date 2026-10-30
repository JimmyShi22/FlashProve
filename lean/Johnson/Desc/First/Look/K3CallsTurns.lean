-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallsTurns.lean: the lookup on a link's CALLS: WHAT A YES OF K3.block's
decide TURNS IN THE CARRIED RECORD, AND WHAT IT LEAVES: it turns the open link's ledger and what was
heard of the lookup, and nothing else. Statements and proofs. A tie: no error term.

OBJECT: Desc.K3.block's decide, as K3.theOwn lays it (Johnson/Desc/First/Look/K3Own.lean:78:
  seat := seatCalls claim or seatDigits claim, guests := []).
USER: k3_att_atTable (Johnson/Desc/First/Look/K3AttAtTable.lean).
LETTERS: seat := seatCalls claim; piece, laid, before, p, guests free.
Built on: Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean.

Why. The table of joints' promise behind the lookup's place asks again what it asked in front: no
count of rows waits, the statement and the book of trees are as they were, the chain stands in the
same link; and the door at the table asks that a mark stays. None of this is in the lookup's own
condition behind: it is "the block turns nothing of it".

Main names:
  `SameBut s s'`: the record's nine fields but "here" are the same; the link's context is the same;
    "here" is of the same sort: a layers' link, an attention link, or the head's opened link.
  `putCalls_sameBut`: of what the calls' seat lays, where a ledger is open and nothing was heard.
  `k3_calls_sameBut`: of a yes of decide. `k3_calls_mark_stays`: so a mark stays, and none comes.

Limits. At the calls' seat alone. It speaks of the record; that the oracles' strings in front of the
block's base stay is the rule's (Johnson/Desc/Sound/StringsStay.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3DecideHearsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- All but the open link's own part is the same, and that part is of the same sort. -/
structure SameBut (s s' : Desc.First.S) : Prop where
  st : s'.st = s.st
  book : s'.book = s.book
  roots : s'.roots = s.roots
  rowsOwed : s'.rowsOwed = s.rowsOwed
  failed : s'.failed = s.failed
  check : s'.check = s.check
  out : s'.out = s.out
  req : s'.req = s.req
  link : s'.link? = s.link?
  sort : (∃ a a', s.here = .lay a ∧ s'.here = .lay a') ∨
    (∃ a a', s.here = .att a ∧ s'.here = .att a') ∨
    ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧ a.opened = true ∧ a'.opened = true

theorem putCalls_sameBut {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard)
    (F Gk : Fork) (hF : (Desc.K3.seatCalls claim).fork s = some F)
    (hn : (Desc.K3.seatCalls claim).heard s = none) :
    SameBut s ((Desc.K3.seatCalls claim).put s g Gk) := by
  simp only [Desc.K3.seatCalls] at hF hn ⊢
  cases hh : s.here with
  | between => simp [Desc.First.S.fork?, hh] at hF
  | fin _ => simp [Desc.First.S.fork?, hh] at hF
  | mem _ => simp [Desc.First.S.fork?, hh] at hF
  | lay a =>
    have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh] using hn
    constructor <;>
      simp [Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?, hh, hn']
  | att a =>
    have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh] using hn
    constructor <;>
      simp [Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?, hh, hn']
  | head a =>
    cases ho : a.opened with
    | false => simp [Desc.First.S.fork?, hh, ho] at hF
    | true =>
      have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh, ho] using hn
      constructor <;>
        simp [Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.link?, hh, ho, hn']

/-- **A yes of decide at the calls turns the open link's ledger and what was heard, and nothing
else.** -/
theorem k3_calls_sameBut {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') : SameBut s s' := by
  obtain ⟨F, y, hF, hn, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact putCalls_sameBut claim s y.1 F y.2 hF hn

/-- So a mark stays, and none comes. -/
theorem k3_calls_mark_stays {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') : s'.failed = s.failed :=
  (k3_calls_sameBut claim piece laid before p guests s s' rs cols h).failed

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.putCalls_sameBut
#print axioms VerifiableInference.OnPublicFiles.k3_calls_sameBut
