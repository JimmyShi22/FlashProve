-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the shared sending's theorem rowsExact at the 25 written places of K2.
/-
Johnson/M1/K2Places.lean: at the closed list of the code switch's places (`placesW`), the public
test of the shared sending and the count of tails, by evaluation in Lean's kernel; and from them the
statement `rowsExact` at each of the 25 sendings. No property of the protocol is claimed here.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.SendSim.At.RowsExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open ProofFile.Honest.K2 (SwitchPlace sendingPar rideOf switchSent switchFresh)
open ProofFile.Honest.K2.Law (placesW)
open OnBytes.SendSim.At (budAt asked shownR)
open Johnson.Prover.Send (shapeAt)

local instance csSome (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- A place's sending, as the shared sending's public letter. -/
def parOf (p : SwitchPlace) : K1.Par := sendingPar p.sizes.codes (switchSent p.sizes p.others)

/-- Which message of a place's sending is the next fold's fresh mask. -/
def placeRide (p : SwitchPlace) : Nat → Option Ride :=
  rideOf (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)

/-- The shared sending's public test at a place. -/
def fitsAt (p : SwitchPlace) : Bool := sendFits (parOf p) (placeRide p)

/-- Every message of P has at least n tail entries in each code that it names. -/
def tailsAt (n : Nat) (P : K1.Par) : Bool :=
  (List.range P.sent.size).all fun k =>
    ((shapeAt P k).mainRows == 0 ||
      decide (n ≤ (P.codes.base.getD (shapeAt P k).code default).r)) &&
    ((shapeAt P k).maskRows == 0 ||
      decide (n ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).r))

set_option maxRecDepth 1000000 in
/-- There are 25 places. -/
theorem places_length : placesW.length = 25 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The shared sending's public test accepts at every place. -/
theorem fits_all : placesW.all fitsAt = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At every place every message has at least 219 tail entries in each code that it names. -/
theorem tails_all : placesW.all (fun p => tailsAt 219 (parOf p)) = true := by decide +kernel

/-- If every list asked has at most n positions and every message has at least n tail entries, the
bound on queried positions holds. -/
theorem budAt_of_len (P : K1.Par) (asks : List (List (List Nat))) (n : Nat)
    (ht : tailsAt n P = true) (hl : ∀ τ, (asked asks τ).length ≤ n) : budAt P asks := by
  intro k τ hk _
  have hk' : k ∈ List.range P.sent.size := List.mem_range.2 hk
  have h := List.all_eq_true.1 ht k hk'
  have h2 := Bool.and_eq_true_iff.1 h
  have card : ∀ m : Nat, ((asked asks τ).map (· % m)).toFinset.card ≤ n := fun m =>
    (List.toFinset_card_le _).trans (by rw [List.length_map]; exact hl τ)
  refine ⟨fun hm => (card _).trans ?_, fun hm => (card _).trans ?_⟩
  · rcases Bool.or_eq_true_iff.1 h2.1 with h3 | h3
    · exact absurd (by simpa using h3) hm
    · exact of_decide_eq_true h3
  · rcases Bool.or_eq_true_iff.1 h2.2 with h3 | h3
    · exact absurd (by simpa using h3) hm
    · exact of_decide_eq_true h3

set_option maxRecDepth 1000000 in
/-- One more position than 219 is over the count at every place: the count has no slack. -/
theorem tails_tight : placesW.all (fun p => !tailsAt 220 (parOf p)) = true := by decide +kernel

theorem fits_of_mem {p : SwitchPlace} (hp : p ∈ placesW) : fitsAt p = true :=
  List.all_eq_true.1 fits_all p hp

theorem tails_of_mem {p : SwitchPlace} (hp : p ∈ placesW) : tailsAt 219 (parOf p) = true :=
  List.all_eq_true.1 tails_all p hp

/-- `rowsExact` with the bound read off the lengths of the lists. -/
theorem rowsExact_of_len (P : K1.Par) (ride : Nat → Option Ride) (first n : Nat)
    (data data' : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (hf : sendFits P ride = true) (ht : tailsAt n P = true)
    (hs : seedsFit P ds = true) (hn : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0)
    (hl : ∀ τ, (asked asks τ).length ≤ n) :
    (Prob.unif (Cs (dueR P ride))).map (shownR P first ride data ds asks) =
      (Prob.unif (Cs (dueR P ride))).map (shownR P first ride data' ds asks) :=
  OnBytes.SendSim.At.rowsExact P first ride data data' ds asks hf hs hn
    (budAt_of_len P asks n ht hl)

/-- **The shared sending's law at each of K2's places**: over uniform coins, what the sending shows
has one law at any two data, for lists of at most 219 positions, at seeds that fit with no factor 0.
-/
theorem k2_rowsExact {p : SwitchPlace} (hp : p ∈ placesW) (first : Nat)
    (data data' : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (hs : seedsFit (parOf p) ds = true)
    (hn : ∀ s ∈ seedsAt (parOf p) ds, readE s.2 ≠ 0)
    (hl : ∀ τ, (asked asks τ).length ≤ 219) :
    (Prob.unif (Cs (dueR (parOf p) (placeRide p)))).map
        (shownR (parOf p) first (placeRide p) data ds asks) =
      (Prob.unif (Cs (dueR (parOf p) (placeRide p)))).map
        (shownR (parOf p) first (placeRide p) data' ds asks) :=
  rowsExact_of_len (parOf p) (placeRide p) first 219 data data' ds asks (fits_of_mem hp)
    (tails_of_mem hp) hs hn hl

end Johnson.M1

#print axioms Johnson.M1.k2_rowsExact
