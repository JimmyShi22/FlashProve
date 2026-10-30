-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3SeatFits.lean: the two seats at which the kind "lookup" rides in the proof file's
first chain (Johnson/Desc/First/Look/K3Seat.lean) pay two premises of the laws on the kind:
`SeatFits` (of the law on its runs of claims, Johnson/Top/H/K3RunsLaw.lean) and `SeatKeeps` (of the
law on its decide). Theorems with their proofs, after the pattern of
Johnson/Desc/First/Look/K3SeatLaw.lean.

So these premises are not empty: they hold of `seatCalls claim` and of `seatDigits claim`; SeatFits
for every way `claim` of laying a form as a claim that has a reader `form` with form (claim a) = a.
Limits. Each law stands under "a ledger is open" (putFork drops its value in silence where no link
is open); SeatKeeps also under "nothing is heard yet", as SeatReads there.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3RunsLaw
import Johnson.Desc.First.Look.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)

/-- Where the seat gives a ledger and nothing is heard yet, the ledger that the hearing lays is the
one that is read. -/
def SeatKeeps {T Cl : Type} (seat : Seat T Cl) : Prop :=
  ∀ (s : T) (g : Forest.Heard) (G : Fork), (seat.fork s).isSome = true → seat.heard s = none →
    seat.fork (seat.put s g G) = some G

theorem fork_putFork (s : S) (F G : Fork) (h : s.fork? = some F) :
    (s.putFork G).fork? = some G := by
  cases hh : s.here with
  | between => simp [S.fork?, hh] at h
  | fin _ => simp [S.fork?, hh] at h
  | mem _ => simp [S.fork?, hh] at h
  | lay a => simp [S.putFork, S.fork?, hh]
  | att a => simp [S.putFork, S.fork?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at h
    | true => simp [S.putFork, S.fork?, hh, ho]

theorem lookHeard_putFork (s : S) (G : Fork) : (s.putFork G).lookHeard? = s.lookHeard? := by
  cases hh : s.here with
  | between => simp [S.putFork, hh]
  | fin _ => simp [S.putFork, hh]
  | mem _ => simp [S.putFork, hh]
  | lay a => simp [S.putFork, S.lookHeard?, hh]
  | att a => simp [S.putFork, S.lookHeard?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.putFork, hh, ho]
    | true => simp [S.putFork, S.lookHeard?, hh, ho]

theorem tl_putFork (s : S) (G : Fork) : (s.putFork G).tl? = s.tl? := by
  cases hh : s.here with
  | between => simp [S.putFork, hh]
  | fin _ => simp [S.putFork, hh]
  | mem _ => simp [S.putFork, hh]
  | lay a => simp [S.putFork, S.tl?, hh]
  | att a => simp [S.putFork, S.tl?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.putFork, hh, ho]
    | true => simp [S.putFork, S.tl?, hh, ho]

theorem seatCalls_fits {Cl : Type} (claim : Aff → Cl) (form : Cl → Aff)
    (hc : ∀ a, form (claim a) = a) : SeatFits (seatCalls claim) form :=
  ⟨fun s F G h => fork_putFork s F G h, fun s _ G _ => lookHeard_putFork s G, hc⟩

theorem seatDigits_fits {Cl : Type} (claim : Aff → Cl) (form : Cl → Aff)
    (hc : ∀ a, form (claim a) = a) : SeatFits (seatDigits claim) form :=
  ⟨fun s F G h => fork_putFork s F G h,
    fun s _ G _ => congrArg (fun x : Option HTailF2 => x.bind (·.heard)) (tl_putFork s G), hc⟩

theorem seatCalls_keeps {Cl : Type} (claim : Aff → Cl) : SeatKeeps (seatCalls claim) := by
  intro s g G hf hn
  simp only [seatCalls] at hf hn ⊢
  cases hh : s.here with
  | between => simp [S.fork?, hh] at hf
  | fin _ => simp [S.fork?, hh] at hf
  | mem _ => simp [S.fork?, hh] at hf
  | lay a =>
    have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh] using hn
    simp [S.putFork, S.hearLook, S.fork?, hh, hn']
  | att a =>
    have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh] using hn
    simp [S.putFork, S.hearLook, S.fork?, hh, hn']
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at hf
    | true =>
      have hn' : a.lookHeard = none := by simpa [S.lookHeard?, hh, ho] using hn
      simp [S.putFork, S.hearLook, S.fork?, hh, ho, hn']

theorem seatDigits_keeps {Cl : Type} (claim : Aff → Cl) : SeatKeeps (seatDigits claim) := by
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

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.seatCalls_fits
#print axioms VerifiableInference.OnPublicFiles.seatDigits_fits
#print axioms VerifiableInference.OnPublicFiles.seatCalls_keeps
#print axioms VerifiableInference.OnPublicFiles.seatDigits_keeps
