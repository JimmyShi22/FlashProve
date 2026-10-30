-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/M1/LotsForm.lean: the rule's door on the book, at K1's senders on the first chain: the
test lotsOkB (Johnson/SendSim/Seat/LotsGuard.lean), from a form that walks the owner's own spenders,
and the two senders' addresses. The kernel's facts at the written entries rawAheadW: LotsW.lean;
the opening's: LotsThinClosed.lean.

  ownerSp, okFast          the owner's spenders; the test over them
  lotsOkB_of_okFast        a part that spends nothing of the owner's coins asks nothing

Limits: written values. That the term's book has these entries, and that lotAt at the term returns
these numbers, is for the theorems that call this file.
-/
import AtFullSide.K14.RawEntriesKit
import Johnson.SendSim.Seat.LotsGuard
import Johnson.SendSim.At.FastBook

set_option autoImplicit false

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K14 AtFullSide.K14
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open P2Law.ProofPlan (WP)
open VerifiableInference.Desc (Place)

/-- Any book with these entries. -/
def aheadBook : ProverCoinCounts := ⟨[], [], [], rawAheadW, []⟩

/-- The parts that spend something of o's coins. -/
def ownerSp (Bk : ProverCoinCounts) (o : Addr) : List Addr := (spendsOf Bk o).map fun e : Ahead => e.spender

/-- The second half of lotsOkB at a sender's numbers, at one spender. -/
def apartAt (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts)
    (ord : List Place) (o p : Addr) : Bool :=
  spentApartB Bk ord o p && (apartRunsB (runsF (Bk.spentBy o p)) (runsF (Bk.knownBy ord o p)) &&
    apartRunsB (sendGuardE P ride (runsE (Bk.spentBy o p))) (runsE (Bk.knownBy ord o p)))

/-- The test over the owner's own spenders. -/
def okFast (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts)
    (ord : List Place) (o : Addr) : Bool :=
  withinB P ride Bk o && (ownerSp Bk o).all (fun p => spenderFitsB P ride Bk o p) &&
    (ownerSp Bk o).all (fun p => apartAt P ride Bk ord o p)

theorem spentBy_nil_of_notSp {Bk : ProverCoinCounts} {o p : Addr} (hp : p ∉ ownerSp Bk o) :
    Bk.spentBy o p = [] := by
  rw [spentBy_eq]
  refine List.filter_eq_nil_iff.2 fun e he hb => hp (List.mem_map.2 ⟨e, he, ?_⟩)
  simpa using hb

/-- **The door's test from the form over the owner's spenders.** -/
theorem lotsOkB_of_okFast {Z : ProofFile.Pub} {G : ProofFile.Ground} {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    {P : VerifiableInference.Desc.K1.Par} {ride : Nat → Option Ride}
    (ha : lotPlacesApartB Z G = true) (hl : lotAt Z G o = some (P, ride))
    (h : okFast P ride Bk ord o = true) : lotsOkB Z G Bk ord o = true := by
  simp only [okFast, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hfits : ownerFitsB P ride Bk o = true := by
    unfold ownerFitsB
    rw [h1, Bool.true_and]
    refine List.all_eq_true.2 fun p _ => ?_
    by_cases hp : p ∈ ownerSp Bk o
    · exact List.all_eq_true.1 h2 p hp
    · unfold spenderFitsB
      rw [spentBy_nil_of_notSp hp]
      rfl
  unfold lotsOkB lotsOwnerFitsB
  rw [ha, hl]
  simp only [Bool.true_and, Bool.and_eq_true]
  refine ⟨hfits, List.all_eq_true.2 fun p _ => ?_⟩
  by_cases hp : p ∈ ownerSp Bk o
  · have h4 := List.all_eq_true.1 h3 p hp
    unfold lotsGuardE
    rw [hl]
    simp only [Bool.or_eq_true]
    exact Or.inr h4
  · rw [spentBy_nil_of_notSp hp]
    rfl

/-- The opening's address. -/
def oOpen : Addr := ⟨⟨1, some 0, 1, .K1⟩, 0⟩

/-- W's address. -/
def oW : Addr := ⟨⟨1, none, 4, .K1⟩, 0⟩

end AtFullSide.M1

#print axioms AtFullSide.M1.lotsOkB_of_okFast
