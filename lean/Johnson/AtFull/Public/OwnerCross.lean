-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/OwnerCross.lean: THE HEAD's EXAMPLE: publicOfO AT THE STORED FULL-SIZE FILES:
  TWO CLOSED FACTS IN owners_W's OWN FORM
(Owners.lean), each asked whole of Lean's kernel, each with a bent twin. No free letter.
  sameReadsB · sameReads_of   "the same reads" as a test with code, and its law: a yes gives the
    equation.
  ownerB w       behind Layer.Pub.of and plansG, ownerOf returns an owner O with sameReadsB
    (AtFull.Head.ownerReads O) w.reads.
  ownerReads_W   FOR THE LEDGER's p19: ownerB AtFull.Head.ownerW = true: so, by sameReads_of,
    Head.planH2 reads of that owner just what the
                 written stand-in holds: ownerReads O = ownerW.reads: the premise hO of
                   planH2_returns
                 (Johnson/AtFull/Head/PlanAtFull.lean), of which no member was known in Lean.
  ownerReads_bent   a negative test: against the stand-in with one symbol array more the comparison
    says no.
  cross_W        THE LEDGER's p20, AT ITS OWN TERMS (AOf | seenGOf: Ledger.lean): behind plansG, the
    twelve groups' twins and
                 attentionOwners, crossPlans returns at ⟨HW.tl, HW.Fp, HW.Tp⟩, HW the closed term
                   that planH2 returns (PlanAtFull.lean).
  cross_bent     a negative test: with the number of comparisons raised by one crossPlans refuses.
Limits. Facts at the twins (Twins.lean) and at the written values: that these are publicOfO's own is
  the join's to show. That planH2 returns
HW is planH2_returns (PlanAtFull.lean). The recursion limit is raised in this file (maxRecDepth
  1000000), as in Owners.lean.
Nothing on soundness.
-/
import Johnson.AtFull.Public.Owners
import Johnson.AtFull.Public.Ledger
import Johnson.AtFull.Head.PlanAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace OnBytes.Road.K4.Trial.AttK7Owners
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road.K4.Trial.AttL2 (AOf seenGOf)

/-- What ownerReads gives. -/
abbrev Reads : Type :=
  Option Nat × Option (Nat × Nat × Nat × Nat × Option ShP) × Nat × Except String PlaceF

/-- "The same reads", as a test with code (Except bears no decidable equality where it is declared).
  -/
def sameReadsB (a b : Reads) : Bool :=
  decide (a.1 = b.1) && decide (a.2.1 = b.2.1) && decide (a.2.2.1 = b.2.2.1) &&
    match a.2.2.2, b.2.2.2 with
    | .ok x, .ok y => decide (x = y)
    | .error x, .error y => decide (x = y)
    | _, _ => false

theorem sameReads_of {a b : Reads} (h : sameReadsB a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4⟩ := a
  obtain ⟨b1, b2, b3, b4⟩ := b
  unfold sameReadsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h4⟩ := h
  cases a4 with
  | ok x =>
    cases b4 with
    | ok y => rw [of_decide_eq_true h4]
    | error y => cases h4
  | error x =>
    cases b4 with
    | ok y => cases h4
    | error y => rw [of_decide_eq_true h4]

/-- The owner's reads are w's. -/
def ownerB (w : AtFull.Head.OwnerW) : Bool :=
  withPubC fun L => onOk (Layer.plansG L) fun G =>
    onOk (Verify.ownerOf L.y G) fun O => sameReadsB (AtFull.Head.ownerReads O) w.reads

theorem ownerReads_W : ownerB AtFull.Head.ownerW = true := by decide +kernel

theorem ownerReads_bent :
    ownerB { AtFull.Head.ownerW with count := AtFull.Head.ownerW.count + 1 } = false := by
  decide +kernel

/-- crossPlans at the ledger's own terms, the number of comparisons raised by e. -/
def crossB (e : Nat) : Bool :=
  withPubC fun L => onOk (Layer.plansG L) fun G =>
    onOk (Attention.readLines PW.polCallsA) fun l =>
      onOk ((List.range L.y.NGr).mapM (Attention.groupS ttR PW L.y L.sc (mqOf L.y) l)) fun ps =>
        onOk (Verify.attentionOwners L.y.h.p4 L.y.NGr
            (G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ : Verify.SubPlan))
            (ps.toArray.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩)) fun seenA =>
          (Verify.crossPlans (G.size - 1 + (AOf ps.toArray seenA).size + 1 + e) L.y.NGr L.y.h.p4
            (Layer.tailsOf L.y) (seenGOf G) seenA
            ⟨AtFull.Head.HW.tl, AtFull.Head.HW.Fp, AtFull.Head.HW.Tp⟩).toOption.isSome

theorem cross_W : crossB 0 = true := by decide +kernel

theorem cross_bent : crossB 1 = false := by decide +kernel

end OnBytes.Road.K4.Trial.AttK7Owners

#print axioms OnBytes.Road.K4.Trial.AttK7Owners.sameReads_of
#print axioms OnBytes.Road.K4.Trial.AttK7Owners.ownerReads_W
#print axioms OnBytes.Road.K4.Trial.AttK7Owners.ownerReads_bent
#print axioms OnBytes.Road.K4.Trial.AttK7Owners.cross_W
#print axioms OnBytes.Road.K4.Trial.AttK7Owners.cross_bent
