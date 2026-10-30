-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Seats.lean: the two seats of a proof file's lookups
(Johnson/Desc/First/Look/K3Seat.lean) store what the seated decision gives them: behind `put` the
seat reads what was heard and the ledger back, and the state bears no new mark. With it: the seated
decision's acceptance, at each seat, with what the state holds behind it. Conditional on `countsOk`.
Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("decision", "heard structure", "ledger", "mark", "seat"). The seated
decision is `decideVia` (Johnson/Desc/First/Look/Via/Via.lean).

What is shown.
  `tl_of_fork`: where a sub-proof's ledger is open, the structure of the smallness test is there
    too. (The library has that statement under the same short name:
    Johnson/Top/H/Keep/K3PassOf.lean.)
  `calls_put`, `digits_put`: behind `put`: `heard` reads what was heard, `fork` the ledger; `failed`
    is as it was. (The first clause is what the library's `seatCalls_reads` and `seatDigits_reads`
    say: `SeatReads`, Johnson/Desc/First/Look/K3SeatLaw.lean. The clauses on the ledger and the mark
    are this file's own.)
  `calls_decides`, `digits_decides`: from the seat's hypotheses in front and the return of `hearV`:
    the seated decision accepts, and the state behind it holds what was heard and the ledger.

Hypotheses that remain.
  `hc`: `countsOk` (Honest/K3/Law/Seated.lean). `hp`, `hN`: the place's parameters make the shape h;
    it has more than one call. `hh`: `hearV` returns.
  In front (`hF`, `h0`, `hO`, `hn`): a ledger is open; nothing is heard yet; no rows are owed; the
    count of slots is the place's. These are for a caller that walks the chain to show.
  `calls_put` asks `hF` and `h0`, `digits_put` `hF`; `tl_of_fork` `h`: a ledger is open.

Why. The decision `decideVia` ends in `pure (seat.put ..)`: it accepts whatever `put` does, and the
`put` of the seat on the digits answers a lacking structure with a mark in the state, not with a
rejection. So the decision's acceptance alone does not say that what was heard was stored.

Users. This file is imported by Honest/K3/Law/SeatedAll.lean and
Honest/K3/Law/Thread/MemberBack.lean.

Limits. The statements speak of the state right behind the decision.
An instance: `stateAt_meets`, Honest/K3/Law/SeatedGuards.lean [not in this library; so here read:
not proved in this library] (by proof there).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Seated
import Johnson.Desc.First.Look.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG seatCalls seatDigits)
open VerifiableInference.Desc.K3.Law (hearVia decideVia)
open VerifiableInference.Desc.First.Look (P)

local notation "FS" => VerifiableInference.Desc.First.S

/-- Where a sub-proof's ledger is open, the structure of the smallness test is there too.
Conditional on an open ledger. -/
theorem tl_of_fork (s : FS) {F : Fork} (h : s.fork? = some F) : ∃ tl, s.tl? = some tl := by
  unfold VerifiableInference.Desc.First.S.fork? at h
  unfold VerifiableInference.Desc.First.S.tl?
  cases hh : s.here with
  | lay a => exact ⟨_, rfl⟩
  | att a => exact ⟨_, rfl⟩
  | head a =>
    rw [hh] at h
    by_cases ho : a.opened = true
    · exact ⟨a.tl, by simp [ho]⟩
    · simp [ho] at h
  | between => rw [hh] at h; exact nomatch h
  | fin a => rw [hh] at h; exact nomatch h
  | mem a => rw [hh] at h; exact nomatch h

/-- **The seat on the calls stores what was heard.**
Conditional on an open ledger and nothing heard yet at the seat. An instance: `stateAt_meets`,
Honest/K3/Law/SeatedGuards.lean [not in this library; so here read: not proved in this library] (by
proof there). -/
theorem calls_put {Cl : Type} (claim : Aff → Cl) (s : FS) {F : Fork}
    (g' : OnBytes.Model.Forest.Heard)
    (G : Fork) (hF : (seatCalls claim).fork s = some F)
    (h0 : ((seatCalls claim).heard s).isNone = true) :
    (seatCalls claim).heard ((seatCalls claim).put s g' G) = some g' ∧
      (seatCalls claim).fork ((seatCalls claim).put s g' G) = some G ∧
      ((seatCalls claim).put s g' G).failed = s.failed := by
  have hF' : s.fork? = some F := hF
  have h0' : s.lookHeard?.isNone = true := h0
  show ((s.putFork G).hearLook g').lookHeard? = some g' ∧ ((s.putFork G).hearLook g').fork? =
    some G ∧
    ((s.putFork G).hearLook g').failed = s.failed
  unfold VerifiableInference.Desc.First.S.fork? at hF'
  unfold VerifiableInference.Desc.First.S.lookHeard? at h0'
  cases hh : s.here with
  | lay a =>
    rw [hh] at h0'
    simp only [Option.isNone_iff_eq_none] at h0'
    simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.hearLook,
      VerifiableInference.Desc.First.S.lookHeard?, VerifiableInference.Desc.First.S.fork?, hh, h0']
  | att a =>
    rw [hh] at h0'
    simp only [Option.isNone_iff_eq_none] at h0'
    simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.hearLook,
      VerifiableInference.Desc.First.S.lookHeard?, VerifiableInference.Desc.First.S.fork?, hh, h0']
  | head a =>
    rw [hh] at h0' hF'
    by_cases ho : a.opened = true
    · simp only [ho, if_true, Option.isNone_iff_eq_none] at h0'
      simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.hearLook,
        VerifiableInference.Desc.First.S.lookHeard?, VerifiableInference.Desc.First.S.fork?, hh,
          h0',
        ho]
    · simp [ho] at hF'
  | between => rw [hh] at hF'; exact nomatch hF'
  | fin a => rw [hh] at hF'; exact nomatch hF'
  | mem a => rw [hh] at hF'; exact nomatch hF'

/-- The structure of the smallness test as the seat on the digits writes it. -/
def digitsTl (tl : OnBytes.Model.HTailF2) (F G : Fork) (g' : OnBytes.Model.Forest.Heard) :
    OnBytes.Model.HTailF2 :=
  { tl with
    foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some g' }

/-- **The seat on the digits stores what was heard.**
Conditional on an open ledger. An instance: `stateAt_meets`, Honest/K3/Law/SeatedGuards.lean
[not in this library; so here read: not proved in this library] (by proof there). -/
theorem digits_put {Cl : Type} (claim : Aff → Cl) (s : FS) {F : Fork}
    (g' : OnBytes.Model.Forest.Heard) (G : Fork) (hF : (seatDigits claim).fork s = some F) :
    (seatDigits claim).heard ((seatDigits claim).put s g' G) = some g' ∧
      (seatDigits claim).fork ((seatDigits claim).put s g' G) = some G ∧
      ((seatDigits claim).put s g' G).failed = s.failed := by
  have hF' : s.fork? = some F := hF
  obtain ⟨tl, htl⟩ := tl_of_fork s hF'
  have hput : (seatDigits claim).put s g' G = (s.putTl (digitsTl tl F G g')).putFork G := by
    show (match s.tl?, s.fork? with
      | some tl, some F => _
      | _, _ => _) = _
    rw [htl, hF']
    rfl
  rw [hput]
  show ((s.putTl _).putFork G).tl?.bind (·.heard) = some g' ∧ ((s.putTl _).putFork G).fork? =
    some G ∧
    ((s.putTl _).putFork G).failed = s.failed
  unfold VerifiableInference.Desc.First.S.fork? at hF'
  cases hh : s.here with
  | lay a =>
    simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.putTl,
      VerifiableInference.Desc.First.S.tl?, VerifiableInference.Desc.First.S.fork?, hh, digitsTl]
  | att a =>
    simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.putTl,
      VerifiableInference.Desc.First.S.tl?, VerifiableInference.Desc.First.S.fork?, hh, digitsTl]
  | head a =>
    rw [hh] at hF'
    by_cases ho : a.opened = true
    · simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.putTl,
        VerifiableInference.Desc.First.S.tl?, VerifiableInference.Desc.First.S.fork?, hh, ho,
        digitsTl]
    · simp [ho] at hF'
  | between => rw [hh] at hF'; exact nomatch hF'
  | fin a => rw [hh] at hF'; exact nomatch hF'
  | mem a => rw [hh] at hF'; exact nomatch hF'

/-- **At the seat on the calls: the seated decision accepts, and the state behind it holds what was
heard and the ledger, with no new mark.** Conditional on `countsOk`, on the place's shape, several
calls, the seat's four hypotheses in front and the return of `hearV`. -/
theorem calls_decides {Cl : Type} (claim : Aff → Cl) (p : P) (h : Shape) (s : FS) {F G : Fork}
    {rs : List Fmt.RoundView} {g : HeardV} (hp : p.shape = some h) (hN : 1 < h.NC)
    (hc : countsOk h = true) (hF : (seatCalls claim).fork s = some F)
    (h0 : ((seatCalls claim).heard s).isNone = true)
    (hO : ((seatCalls claim).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧ decideVia (seatCalls claim) p s rs = .ok s' ∧
      (seatCalls claim).heard s' = some g' ∧ (seatCalls claim).fork s' = some G ∧
      s'.failed = s.failed := by
  obtain ⟨g', hg, hv⟩ := hearVia_returns p h hp hN hc hh
  obtain ⟨a, b, c⟩ := calls_put claim s g' G hF h0
  exact ⟨g', _, hg, decideVia_returns _ p s hF h0 hO hn hv, a, b, c⟩

/-- **The same at the seat on the digits.** Conditional as `calls_decides`. -/
theorem digits_decides {Cl : Type} (claim : Aff → Cl) (p : P) (h : Shape) (s : FS) {F G : Fork}
    {rs : List Fmt.RoundView} {g : HeardV} (hp : p.shape = some h) (hN : 1 < h.NC)
    (hc : countsOk h = true) (hF : (seatDigits claim).fork s = some F)
    (h0 : ((seatDigits claim).heard s).isNone = true)
    (hO : ((seatDigits claim).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧ decideVia (seatDigits claim) p s rs = .ok s' ∧
      (seatDigits claim).heard s' = some g' ∧ (seatDigits claim).fork s' = some G ∧
      s'.failed = s.failed := by
  obtain ⟨g', hg, hv⟩ := hearVia_returns p h hp hN hc hh
  obtain ⟨a, b, c⟩ := digits_put claim s g' G hF
  exact ⟨g', _, hg, decideVia_returns _ p s hF h0 hO hn hv, a, b, c⟩

#print axioms ProofFile.Honest.K3.Law.tl_of_fork
#print axioms ProofFile.Honest.K3.Law.calls_put
#print axioms ProofFile.Honest.K3.Law.digits_put
#print axioms ProofFile.Honest.K3.Law.calls_decides
#print axioms ProofFile.Honest.K3.Law.digits_decides

end ProofFile.Honest.K3.Law
