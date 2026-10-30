-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3SeatLaw.lean: what the two seats of the kind "lookup" at the first chain's
carried record (Johnson/Desc/First/Look/K3Seat.lean) give back of what is laid. Statements, each a
definition of its own name, with their proofs. No axiom beyond Lean's three usual ones; no Mathlib.

Why. A law on the kind's block that speaks of "what was heard" behind `decide` needs that the seat's
`heard` reads what the seat's `put` has laid. For all records that is false of both seats. Here it
is said under which conditions it is so, and that without them it is not.

Main names:
  `SeatReads seat`: where the seat gives a ledger and nothing is heard yet, `heard` behind `put`
    gives what was laid.
  `seatCalls_reads`, `seatDigits_reads`: both seats have it.
  `calls_noLink`, `calls_twice`, `digits_noLink`: without a condition it fails: shown.

Limits: nothing is said of what else `put` turns, of the ledger, of soundness, or of hiding. That
nothing is heard yet in front of the kind's block is asked by the block's `decide` (K3Lookup.lean, its
second need); at the calls the seat's own mark at a second hearing (`S.hearLook`) stays behind it.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc.First (S)

/-- Where the seat gives a ledger and nothing is heard yet, what is laid is read. -/
def SeatReads {T Cl : Type} (seat : Seat T Cl) : Prop :=
  ∀ (s : T) (g : Model.Forest.Heard) (G : Fork), (seat.fork s).isSome = true → seat.heard s = none →
    seat.heard (seat.put s g G) = some g

theorem seatCalls_reads {Cl : Type} (claim : Aff → Cl) : SeatReads (seatCalls claim) := by
  intro s g G hf hn
  simp only [seatCalls] at hf hn ⊢
  cases hh : s.here with
  | between => simp [S.fork?, hh] at hf
  | fin _ => simp [S.fork?, hh] at hf
  | mem _ => simp [S.fork?, hh] at hf
  | lay a =>
    have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh] using hn
    simp [S.putFork, S.hearLook, S.lookHeard?, hh, hn']
  | att a =>
    have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh] using hn
    simp [S.putFork, S.hearLook, S.lookHeard?, hh, hn']
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at hf
    | true =>
      have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh, ho] using hn
      simp [S.putFork, S.hearLook, S.lookHeard?, hh, ho, hn']

theorem seatDigits_reads {Cl : Type} (claim : Aff → Cl) : SeatReads (seatDigits claim) := by
  intro s g G hf _
  simp only [seatDigits] at hf ⊢
  cases hh : s.here with
  | between => simp [S.fork?, hh] at hf
  | fin _ => simp [S.fork?, hh] at hf
  | mem _ => simp [S.fork?, hh] at hf
  | lay a => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh]
  | att a => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at hf
    | true => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh, ho]

/-- A mark leaves the place as it is. -/
theorem mark_here (s : S) (n : String) : (s.mark n).here = s.here := by
  unfold S.mark
  split <;> rfl

/-- WITHOUT THE FIRST CONDITION, at the calls: between two links nothing is read back. -/
theorem calls_noLink {Cl : Type} (claim : Aff → Cl) (s : S) (g : Model.Forest.Heard) (G : Fork)
    (hh : s.here = .between) : (seatCalls claim).heard ((seatCalls claim).put s g G) = none := by
  have h1 : s.putFork G = s := by simp [S.putFork, hh]
  have h2 : s.hearLook g = s.mark "state-hear-look" := by simp [S.hearLook, hh]
  simp only [seatCalls, h1, h2, S.lookHeard?, mark_here, hh]

/-- WITHOUT THE SECOND CONDITION, at the calls: a second hearing keeps the first. -/
theorem calls_twice {Cl : Type} (claim : Aff → Cl) (s : S) (a : First.LayOwn)
    (g₀ g : Model.Forest.Heard) (G : Fork) (hh : s.here = .lay a) (h₀ : a.lookHeard = some g₀) :
    (seatCalls claim).heard ((seatCalls claim).put s g G) = some g₀ := by
  have h1 : (s.putFork G).here = .lay { a with F := G } := by simp [S.putFork, hh]
  have h2 : (s.putFork G).hearLook g = (s.putFork G).mark "state-look-twice" := by
    simp [S.hearLook, h1, h₀]
  simp only [seatCalls, h2, S.lookHeard?, mark_here, h1, h₀]

/-- WITHOUT THE FIRST CONDITION, at the digits. -/
theorem digits_noLink {Cl : Type} (claim : Aff → Cl) (s : S) (g : Model.Forest.Heard) (G : Fork)
    (hh : s.here = .between) : (seatDigits claim).heard ((seatDigits claim).put s g G) = none := by
  have h1 : s.tl? = none := by simp [S.tl?, hh]
  simp only [seatDigits, h1]
  simp [S.tl?, mark_here, hh]

end VerifiableInference.Desc.K3
