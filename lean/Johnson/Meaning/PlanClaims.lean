--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Meaning/PlanClaims.lean: where the plan's number of claims is laid into a sub-proof's record
at a layers' and at an attention segment, and which number it is: the step without a round behind
the lookup on the digits (Johnson/Desc/First/Look/K3Whole.lean: quietDigits, quietAt) lays nLin of
the public record's own plan; and the rows of that plan's batching round are nLin and the indices of
the smallness test's equations at the plan's number of reads.

  quietDigits_yes   where quietDigits used claims s returns t: s.fork? = some F, F.next = used, and
                    t = s.putFork { F with planClaimsF := claims }.
  quietDigits_fork · quietDigits_tl   so t.fork? = some { F with planClaimsF := claims }, and
                    t.tl? = s.tl? (the landed S.fork_putFork, StateLedger.lean, and tl_putFork,
                    Johnson/Top/H/K3SeatFits.lean, called).
  quietAt_layers · quietAt_attention   where attention is covered (X.p4) and the number is not the
                    head's: quietAt X (2 g) true = some (quietDigits hp.used hp.nLin) at
                    X.G[g]? = some hp; quietAt X (2 g + 1) true =
                    some (quietDigits a.nMsg a.nLin) at X.A[g]? = some a.
  rows_layers · rows_attention   where publicOf returns X: hp.nBatched = hp.nLin +
                    hp.tl.equationsF (Layer.readsCount X.layers.y X.layers.rd g) ·
                    a.own.rows = a.nLin + a.seam.tl.equationsF (tableReads a.S (Counts.of a.S)): the
                    landed Fo.Pub.public_G_rows | public_A_rows, called, laid side by side with the
                    two above.

What is not claimed. The head's segment (there the merge's kind lays the number). That the number
laid stays until the batching's door. That the block behind the lookup on the digits in a
description is quietAt's. Nothing on soundness.
-/
import Johnson.Desc.First.Look.K3Whole
import Johnson.Desc.First.StateLedger
import Johnson.Top.H.K3SeatFits
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false

namespace Meaning.K8

open OnBytes OnBytes.Model
open VerifiableInference.Desc (K3.quietDigits K3.quietAt K3.isHead)
open VerifiableInference.Desc.First (S)

/-- **What the step behind the lookup on the digits has tested and lays.** -/
theorem quietDigits_yes {used claims : Nat} {s t : S} (h : K3.quietDigits used claims s = .ok t) :
    ∃ F, s.fork? = some F ∧ F.next = used ∧ t = s.putFork { F with planClaimsF := claims } := by
  unfold K3.quietDigits at h
  cases e1 : s.fork? with
  | none => rw [e1] at h; cases h
  | some F =>
    rw [e1] at h
    have h : ((VerifiableInference.Desc.named "K3 quiet: the planned slots are taken"
        (VerifiableInference.Desc.First.Look.slotsTaken used claims F)).bind
          fun G => (pure (s.putFork G) : Except String S)) = .ok t := h
    by_cases e2 : (F.next == used) = true
    · have e3 : VerifiableInference.Desc.First.Look.slotsTaken used claims F =
          some { F with planClaimsF := claims } := by
        unfold VerifiableInference.Desc.First.Look.slotsTaken
        rw [if_pos e2]
      rw [e3] at h
      exact ⟨F, rfl, by simpa using e2, (Except.ok.inj h).symm⟩
    · have e3 : VerifiableInference.Desc.First.Look.slotsTaken used claims F = none := by
        unfold VerifiableInference.Desc.First.Look.slotsTaken
        rw [if_neg e2]
      rw [e3] at h
      cases h

theorem quietDigits_fork {used claims : Nat} {s t : S} (h : K3.quietDigits used claims s = .ok t) :
    ∃ F, s.fork? = some F ∧ t.fork? = some { F with planClaimsF := claims } := by
  obtain ⟨F, e1, -, rfl⟩ := quietDigits_yes h
  exact ⟨F, e1, S.fork_putFork s F _ e1⟩

theorem quietDigits_tl {used claims : Nat} {s t : S} (h : K3.quietDigits used claims s = .ok t) :
    t.tl? = s.tl? := by
  obtain ⟨F, -, -, rfl⟩ := quietDigits_yes h
  exact VerifiableInference.OnPublicFiles.tl_putFork s _

/-- **At a layers' segment the number laid is the plan's nLin.** -/
theorem quietAt_layers {X : Verify.Public} (hq : X.p4 = true) {g : Nat} (hg : g ≠ X.NGr)
    {hp : Layer.HPlan2} (h : X.G[g]? = some hp) :
    K3.quietAt X (2 * g) true = some (K3.quietDigits hp.used hp.nLin) := by
  unfold K3.quietAt K3.isHead
  rw [hq]
  have e1 : (2 * g == 2 * X.NGr) = false := beq_false_of_ne (by omega)
  have e2 : (2 * g % 2 == 0) = true := by simp
  have e3 : 2 * g / 2 = g := by omega
  simp only [if_true, e1, e2, e3, h, Bool.false_eq_true, if_false, Option.map_some]

/-- **At an attention segment the number laid is the plan's nLin.** -/
theorem quietAt_attention {X : Verify.Public} (hq : X.p4 = true) {g : Nat} {a : Attention.Plan}
    (h : X.A[g]? = some a) :
    K3.quietAt X (2 * g + 1) true = some (K3.quietDigits a.nMsg a.nLin) := by
  unfold K3.quietAt K3.isHead
  rw [hq]
  have e1 : (2 * g + 1 == 2 * X.NGr) = false := beq_false_of_ne (by omega)
  have e2 : ((2 * g + 1) % 2 == 0) = false := by
    have : (2 * g + 1) % 2 = 1 := by omega
    rw [this]
    rfl
  have e3 : (2 * g + 1) / 2 = g := by omega
  simp only [if_true, e1, e2, e3, h, Bool.false_eq_true, if_false, Option.map_some]

/-- The rows of a layers' plan's batching round. -/
theorem rows_layers {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL lay = .ok X) {g : Nat} {hp : Layer.HPlan2}
    (hg : X.G[g]? = some hp) :
    hp.nBatched = hp.nLin + hp.tl.equationsF (Layer.readsCount X.layers.y X.layers.rd g) :=
  Fo.Pub.public_G_rows h g hp hg

/-- The rows of an attention plan's batching round. -/
theorem rows_attention {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL lay = .ok X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) :
    a.own.rows = a.nLin +
      a.seam.tl.equationsF (Attention.tableReads a.S (Attention.Counts.of a.S)) :=
  Fo.Pub.public_A_rows h g a hg

end Meaning.K8

#print axioms Meaning.K8.quietDigits_yes
#print axioms Meaning.K8.quietAt_layers
#print axioms Meaning.K8.quietAt_attention
#print axioms Meaning.K8.rows_layers
#print axioms Meaning.K8.rows_attention
