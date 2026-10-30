-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SeatedAll.lean: what is seated at a proof file's lookups, from
the return of `hearV`: a composition of the theorems of Honest/K3/Law/Seated.lean,
Honest/K3/Law/Seats.lean, Honest/K3/Law/SeatedPlanes.lean and Honest/K3/Law/CountsOk.lean. Theorems.

Terms. Honest/K3/GLOSSARY.md ("decision", "run (of claims)", "seat"). The seated decision is
`decideVia`; the seated run of claims on the planes is `planesRun`.

What is shown.
  `calls_accepts`, `digits_accepts`: the seated decision accepts, and the seat holds what was heard
    and the ledger behind it, with no new mark: from the place's shape, several calls, the seat's
    four hypotheses in front, and the return of `hearV`. There is no hypothesis on the counts of
    `toHeard`.
  `planesRun_of_hearV`: the seated run of claims on the planes returns, with three claims: from the
    return of `hearV` at the first ledger; and, at the run's state: the seat's ledger, later than
    the hearing's, with the leaves' own slots still owed; what was heard stored; the debt not yet
    marked as paid; the caller's readers answering; the packing's test. Besides: both ledgers'
    arrays have their size; the first has room for the lookup's slots; `toHeard` has returned what
    is stored.

Hypotheses that remain. Those named above. By name: in `calls_accepts`, `digits_accepts`: `hp`,
`hN`, `hF`, `h0`, `hO`, `hn`, `hh`. In `planesRun_of_hearV`: `hS`, `hroom`, `hh`, `hg'` (at the
first ledger and of what was heard); `hF'`, `hS'`, `hL`, `ho` (the seat's ledger); `hgs` (what was
heard is stored); `hu` (the debt); `hr`, `hb`, `hpn` (the caller's readers answer); `hpo` (the
packing's test). Of these:
  That `hearV` returns on the honest rounds is another statement's.
  That the leaves' own slots are still owed at the run's ledger: Honest/K3/Law/LeavesFree.lean gives
    it at the hearing's own ledger, in the word that the library's theorems carry on.
  The caller's readers are letters.

Users. This file is imported by Honest/K3/Law/SeatedGuards.lean [not in this library],
Honest/K3/Law/Stated.lean and Honest/K3/Law/Thread/ExchangePlanes.lean.

Limits. What stands between the hearing and the run of claims is not walked. At a layers' link the
planes' claims are made in another kind's runs: not reached. Shown in part:
Honest/K3/Law/Thread/Group11.lean [not in this library]. `planes_twin`: where the other kind's text
of these claims returns, and its text of the leaves' late claim returns at what the first keeps, the
seated text `planeClaimsOwn` returns at the other kind's readers, with the same three forms and the
same ledger behind. `rowL_returns` and `group11_returns`: behind the lookup's hearing, the other
kind's hearing and the late claim that its run makes first, the leaves' late claim returns, and so
do the three; conditional on these returns, on the leaves' own slots being still owed at the ledger
from which the other kind hears, on the other kind's text of these claims returning, and on the
other kind holding the structure of the leaves' sumcheck that the lookup heard. What the three are
worth there: `group11_zero` (Honest/K3/Law/Thread/Group11Worth.lean [not in this library]),
conditional on `Left`, on the other kind's readers' law and on what that file's head lists. By the
head of Group11.lean [not in this library], that the other kind's readers answer is for the files of
the other kind to show. Nothing is said on what a claim is worth.
Instances: at a small seat, Honest/K3/Law/SeatedGuards.lean [not in this library] (by evaluation);
of two of the seat's four hypotheses (the ledger is open; nothing is heard), `stateAt_meets` there
(by proof). No instance of all hypotheses together at one of the library's two seats is exhibited in
this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Seats
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedPlanes
import Johnson.Desc.ProofFile.Honest.K3.Law.CountsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG toPsc Seat seatCalls
  seatDigits
  planesRun unpaid Readers)
open VerifiableInference.Desc.K3.Law (hearVia decideVia)
open VerifiableInference.Desc.First.Look (P planesOk)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **At the seat on the calls.** Conditional on: the place's parameters fix the shape; several
calls; a ledger is open; nothing is heard yet; no rows are owed; the count of slots is the place's;
and the return of `hearV`. Instances: at a small seat, Honest/K3/Law/SeatedGuards.lean
[not in this library] (by evaluation); of two of the seat's four hypotheses (the ledger is open;
nothing is heard), `stateAt_meets` there (by proof). No instance of all together at this seat is
exhibited in this file. -/
theorem calls_accepts {Cl : Type} (claim : Aff → Cl) (p : P) (h : Shape) (s : FS) {F G : Fork}
    {rs : List Fmt.RoundView} {g : HeardV} (hp : p.shape = some h) (hN : 1 < h.NC)
    (hF : (seatCalls claim).fork s = some F) (h0 : ((seatCalls claim).heard s).isNone = true)
    (hO : ((seatCalls claim).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧ decideVia (seatCalls claim) p s rs = .ok s' ∧
      (seatCalls claim).heard s' = some g' ∧ (seatCalls claim).fork s' = some G ∧
      s'.failed = s.failed :=
  calls_decides claim p h s hp hN (countsOk_of_shape hp) hF h0 hO hn hh

/-- **At the seat on the digits.**
Conditional on the same seven. Instances: as at the calls. -/
theorem digits_accepts {Cl : Type} (claim : Aff → Cl) (p : P) (h : Shape) (s : FS) {F G : Fork}
    {rs : List Fmt.RoundView} {g : HeardV} (hp : p.shape = some h) (hN : 1 < h.NC)
    (hF : (seatDigits claim).fork s = some F) (h0 : ((seatDigits claim).heard s).isNone = true)
    (hO : ((seatDigits claim).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧ decideVia (seatDigits claim) p s rs = .ok s' ∧
      (seatDigits claim).heard s' = some g' ∧ (seatDigits claim).fork s' = some G ∧
      s'.failed = s.failed :=
  digits_decides claim p h s hp hN (countsOk_of_shape hp) hF h0 hO hn hh

/-- **The seated run of claims on the planes returns.** F, x, g, G: the hearing's. s, F': the state
and the seat's ledger at the run.
Conditional on the return of `hearV`; the leaves' own slots still owed at the run's ledger; the
seat's three in front; the caller's readers' answers; the packing's test. Instances and alterations,
at a small seat: Honest/K3/Law/SeatedGuards.lean [not in this library] (by evaluation). -/
theorem planesRun_of_hearV {S Cl : Type} (seat : Seat S Cl) (h : Shape) (lm : Nat)
    (readers : Readers S) (n : Nat) (s : S) {F G F' : Fork} {x : List Fmt.RoundView} {g : HeardV}
    {g' : OnBytes.Model.Forest.Heard} {r : (Nat → Nat → Option Aff) × (Nat → Option Aff)}
    (hS : Sized F) (hroom : F.next + (faceOf h).slots ≤ F.ns)
    (hh : hearV (faceOf h) F x = some (g, G)) (hg' : toHeard h (toHeardG g) = some g')
    (hF' : seat.fork s = some F') (hgs : seat.heard s = some g') (hS' : Sized F') (hL : Later G F')
    (ho : OnBytes.PscRun.SlotsOwed F' (F.next + firstSlot (faceOf h) .leaves)
      (Stage.own (faceOf h) .leaves))
    (hu : unpaid F' g'.owedPlanes = true) (hr : readers s = some r) (hpo : planesOk h lm = true)
    (hb : ∀ e col, col < planeColsOf h lm → (r.1 e col).isSome = true)
    (hpn : ∀ col, col < planeColsOf h lm → (r.2 col).isSome = true) :
    ∃ (fs : Array Aff) (G' : Fork), planesRun seat lm readers n s =
      .ok (fs.toList.map seat.claim, seat.mark s (G'.paid g'.owedPlanes)) ∧ fs.size = 3 ∧
      Later F' G' := by
  obtain ⟨pt, form, hk, hs⟩ := keys_of_hearV h hh
  have hsh : g'.shape = h ∧ g'.leaves = toPsc g.leaves := by
    unfold toHeard at hg'
    have hk' : (toHeardG g).keys = [(pt, form)] := hk
    rw [hk'] at hg'
    simp only at hg'
    split at hg'
    · obtain rfl := Option.some.inj hg'
      exact ⟨rfl, rfl⟩
    · exact nomatch hg'
  obtain ⟨G', hl, hrow⟩ := leavesRowOwn_returns (faceOf h) hS hroom hh hS' hL ho
  obtain ⟨fs, hfs, h3⟩ := planesRun_returns seat lm readers n s (G := G') hF' hgs hu hr
    (by rw [hsh.1]; exact hpo) (by rw [hsh.1]; exact hb) (by rw [hsh.1]; exact hpn)
    (fun kept => by rw [hsh.2]; exact hrow oneE kept [])
  exact ⟨fs, G', hfs, h3, hl⟩

#print axioms ProofFile.Honest.K3.Law.calls_accepts
#print axioms ProofFile.Honest.K3.Law.digits_accepts
#print axioms ProofFile.Honest.K3.Law.planesRun_of_hearV

end ProofFile.Honest.K3.Law
