-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/DrawSlots.lean: WHAT K9's DRAW LEAVES OF THE SLOTS' MARKS AND OF THE HEAD's OWN
FIELDS. For a kind whose run of claims needs, at its call inside the batching, slots that are still free (the fold:
Honest/K9/GatherLeaves.lean [not in this library]: its premise "Q holds at the gatherer's state").
Statements and proofs ON THE VERIFIER's
TEXT; no prover is in this file, and no goal is stated.

  `drawn_slots`     the ledger behind the draw (`drawnPart`, Honest/K9/LedgerOf.lean) has the ledger in front's number
                    of slots, next slot, shown values, factors and marks: by `rfl`
  `draw_head`       a yes of the draw at a state that stands in the head's segment: the state behind stands there too,
                    with every field of the head's own as it was but the link's context and the ledger; and the ledger
                    is `drawnPart`'s
  `open_drawn`      so what a sumcheck's row asks of the ledger (`D6.Ret.Open`, OnBytes/K/Kc/Returns/FlReturns6.lean)
                    holds behind the draw where it held in front
  `head_slots_behind_draw`   the same as equations, for whoever states a predicate of their own: the merge's data, the
                    number of slots, the next slot, the shown values, the factors and the marks are as they were
  **`waits_behind_draw`**   "the head's state holds the merge's data as its decision laid them, and the merge's
                    sumcheck's slots are there and free, and every slot of its starting form is filled"
                    (written out here:
                    four clauses) PASSES THE DRAW
No member: the five are called by one another alone.
WHAT IS NOT CLAIMED. That it holds in front of the draw. That the runs in front of the merge's leave it. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K9.BatYes
import Johnson.Desc.First.Batch.BlindK3
import OnBytes.K.Kc.Returns.FlReturns6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (atS Where drawAlone)

/-- The draw turns nothing under the slots. -/
theorem drawn_slots (p : Where) (a : VerifiableInference.Desc.K9.Part) (x : E) :
    (drawnPart p a x).F.ns = a.F.ns ∧ (drawnPart p a x).F.next = a.F.next ∧
      (drawnPart p a x).F.vp = a.F.vp ∧ (drawnPart p a x).F.mf = a.F.mf ∧
      (drawnPart p a x).F.gotF = a.F.gotF := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A yes of the draw at a state in the head's segment.** -/
theorem draw_head (p : Where) (s t : S) (x : E) (h0 : HeadOwn) (hs : s.here = .head h0)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t) :
    ∃ a, atS.get? s = some a ∧ a.F = h0.F ∧
      t.here = .head { h0 with L := (drawnPart p a x).L, F := (drawnPart p a x).F } := by
  obtain ⟨a, ha⟩ := draw_open p s t x h
  have hf : s.fork? = some a.F := VerifiableInference.Desc.K9.get_fork s a ha
  have ho : h0.opened = true ∧ h0.F = a.F := by
    unfold S.fork? at hf
    rw [hs] at hf
    have hf' : (if h0.opened = true then some h0.F else none) = some a.F := hf
    by_cases ho : h0.opened = true
    · rw [if_pos ho] at hf'
      exact ⟨ho, Option.some.inj hf'⟩
    · rw [if_neg ho] at hf'
      exact nomatch hf'
  refine ⟨a, ha, ho.2.symm, ?_⟩
  rw [draw_is p s t x a ha h]
  simp [atS, S.putLink, S.putFork, hs, ho.1]

/-- What a sumcheck's row asks of the ledger passes the draw. -/
theorem open_drawn (p : Where) (a : VerifiableInference.Desc.K9.Part) (x : E) (q : Psc)
    (h : D6.Ret.Open q a.F) : D6.Ret.Open q (drawnPart p a x).F :=
  h.keep h.sized rfl fun _ _ _ => Iff.rfl

/-- The head's state behind the draw, for whoever states a predicate of their own: the merge's data and all that lies
under the slots are as they were. -/
theorem head_slots_behind_draw (p : Where) (s t : S) (x : E) (h0 : HeadOwn) (hs : s.here = .head h0)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t) :
    ∃ h1 : HeadOwn, t.here = .head h1 ∧ h1.wo = h0.wo ∧ h1.F.ns = h0.F.ns ∧ h1.F.next = h0.F.next ∧
      h1.F.vp = h0.F.vp ∧ h1.F.mf = h0.F.mf ∧ h1.F.gotF = h0.F.gotF := by
  obtain ⟨a, _, hF, ht⟩ := draw_head p s t x h0 hs h
  refine ⟨_, ht, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← hF] <;> rfl

/-- **Part 1's Q passes the draw**: its four clauses. -/
theorem waits_behind_draw (p : Where) (s t : S) (x : E)
    (hq : ∃ a wo, s.here = .head a ∧ a.wo = some wo ∧ D6.Ret.Open wo.p a.F ∧
      ∀ y ∈ wo.p.start.slots.toList, OnBytes.PscRun.Filled a.F y.1)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t) :
    ∃ a wo, t.here = .head a ∧ a.wo = some wo ∧ D6.Ret.Open wo.p a.F ∧
      ∀ y ∈ wo.p.start.slots.toList, OnBytes.PscRun.Filled a.F y.1 := by
  obtain ⟨h0, wo, hs, hw, ho, hfl⟩ := hq
  obtain ⟨a, _, hF, ht⟩ := draw_head p s t x h0 hs h
  rw [← hF] at ho hfl
  exact ⟨_, wo, ht, hw, open_drawn p a x wo.p ho, hfl⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.drawn_slots
#print axioms ProofFile.Honest.K9.draw_head
#print axioms ProofFile.Honest.K9.open_drawn
#print axioms ProofFile.Honest.K9.head_slots_behind_draw
#print axioms ProofFile.Honest.K9.waits_behind_draw
