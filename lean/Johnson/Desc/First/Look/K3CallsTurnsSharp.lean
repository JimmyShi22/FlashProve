-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallsTurnsSharp.lean: the lookup on a link's CALLS: WHICH FIELDS OF THE
OPEN LINK's OWN PART A YES OF K3.block's decide TURNS: the ledger, what the lookup returned, and
"heard": AND NO OTHER. Sharper than SameBut (Johnson/Desc/First/Look/K3CallsTurns.lean), which says
only that the part is of the same sort; at the calls' seat alone. Statements and proofs. A tie: no
error term.

OBJECT: Desc.K3.block's decide at seatCalls claim (as K3.theOwn lays it, or beneath blockVia).
USER: K3CallsKeeps.lean, Johnson/Desc/Kinds/Law/TablesNotYetCalls.lean, K6Reached.lean,
  Johnson/Desc/AtSeats/PadAtRch.lean
  (whoever shows that a public item on the open link's other fields rides past the
  lookup on the calls: "nothing is heard yet at the digits' seat"; "the caller has not been heard").
LETTERS: piece, laid, before, p, guests free.

Main names:
  `TurnsCalls s s'`: the smallness test's record is the same (tl?); "here" is the open link's own
    part with the three fields turned and no other (at the head's link: the ledger, the field x,
    of whose value behind the yes nothing is said, and
    "heard").
  `putCalls_turns`, `k3_calls_turns`.

Limits. At the calls' seat alone: at the digits' seat tl? turns.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- The open link's own part: the ledger, what the lookup returned and "heard" turn, and no other
field. -/
structure TurnsCalls (s s' : Desc.First.S) : Prop where
  tl : s'.tl? = s.tl?
  part : (∃ a F g, s.here = .lay a ∧
      s'.here = .lay { a with F := F, fo := some g, lookHeard := some g }) ∨
    (∃ a F g, s.here = .att a ∧
      s'.here = .att { a with F := F, g := some g, lookHeard := some g }) ∨
    ∃ a F g, s.here = .head a ∧ a.opened = true ∧
      ∃ x', s'.here = .head { a with F := F, x := x', lookHeard := some g }

theorem putCalls_turns {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard)
    (F Gk : Fork) (hF : (Desc.K3.seatCalls claim).fork s = some F)
    (hn : (Desc.K3.seatCalls claim).heard s = none) :
    TurnsCalls s ((Desc.K3.seatCalls claim).put s g Gk) := by
  simp only [Desc.K3.seatCalls] at hF hn ⊢
  cases hh : s.here with
  | between => simp [Desc.First.S.fork?, hh] at hF
  | fin _ => simp [Desc.First.S.fork?, hh] at hF
  | mem _ => simp [Desc.First.S.fork?, hh] at hF
  | lay a =>
    have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh] using hn
    refine ⟨?_, Or.inl ⟨a, Gk, g, by first | rfl | exact hh, ?_⟩⟩ <;>
      simp [Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.tl?, hh, hn']
  | att a =>
    have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh] using hn
    refine ⟨?_, Or.inr (Or.inl ⟨a, Gk, g, by first | rfl | exact hh, ?_⟩)⟩ <;>
      simp [Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.tl?, hh, hn']
  | head a =>
    cases ho : a.opened with
    | false => simp [Desc.First.S.fork?, hh, ho] at hF
    | true =>
      have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh, ho] using hn
      refine ⟨?_, Or.inr (Or.inr ⟨a, Gk, g, by first | rfl | exact hh, ho, ?_⟩)⟩ <;>
        simp [Desc.First.S.putFork, Desc.First.S.hearLook, Desc.First.S.tl?, hh, ho, hn']

/-- **A yes of decide at the calls turns these three fields of the open link's part, and no
other.** -/
theorem k3_calls_turns {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') : TurnsCalls s s' := by
  obtain ⟨F, y, hF, hn, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact putCalls_turns claim s y.1 F y.2 hF hn

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.putCalls_turns
#print axioms VerifiableInference.OnPublicFiles.k3_calls_turns
