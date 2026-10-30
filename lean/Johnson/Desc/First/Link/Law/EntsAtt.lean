-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EntsAtt.lean: THE TWO CLAUSES "entsFirst" AND "entsSecond" OF WHAT IS
FIXED IN FRONT OF AN ATTENTION SEGMENT's BATCHING, FROM ONE TEST WITH CODE ON THE STATE.
Statements and proofs: calls.

The make (EntsAtBatch.lean: every entry that a form of the run names stands at virtual row 0 of the
array of the third vector) is `plain_named_first`, `plain_named_second`
(Johnson/Desc/First/Att/Door/Law/PlainThereTie.lean): they speak at `firstAt` and `secondAt`, the
very terms of which `fsFirst` and `fsSecond` are made (Att/Claims/K5Still.lean), under the
test `plainThereB c.iU3 c.nW s` (Johnson/Desc/First/Att/Door/PlainThereB.lean).

  `make_first`, `make_second`: the make of what `fsFirst`, `fsSecond` give at `fixed9 φ s`.
  `entsFirst_of_plain`, `entsSecond_of_plain`: **plainThereB c.iU3 c.nW s = true; what rd reads
    back is what s has heard; the static clause at what is fixed; the fixed structure names
    c.iU3 for the third vector; the third vector is planned with at least one entry ⊢ the clause.**
Limits. The five premises stay. `plainThereB` is shown of no state here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.EntsAtBatch
import Johnson.Desc.First.Att.Door.Law.PlainThereTie
import Johnson.Desc.First.Att.Claims.K5Still
import Johnson.Desc.First.Batch.BlindK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)
open H2K5.Door (plainThereB plain_named_first plain_named_second)
open K5Law

variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α)
  (rd : α → Option (Forest.Heard × Heard)) (c : ParC)

/-- The snapshot's ledger is the state's. -/
theorem snap_fork {s : S} {v : Pub9} (h : (fixed9 φ s).2 = some v) : s.fork? = some v.F := by
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 (show (atS.get? s).map pubOf = some v from h)
  exact K9.get_fork s p hp

theorem make_first {s : S} (hp : plainThereB c.iU3 c.nW s = true)
    (hrd : ∀ g h, rd (φ s) = some (g, h) → s.heard5? = some h) {l : List Aff}
    (e : fsFirst rd c (fixed9 φ s) = some l) : EntsMake c.iU3 l := by
  unfold fsFirst at e
  obtain ⟨gh, e1, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨v, e2, e⟩ := Option.bind_eq_some_iff.1 e
  intro f hf x hx
  obtain ⟨a, b, _⟩ := plain_named_first hp (snap_fork φ e2) (hrd gh.1 gh.2 e1) e f hf x hx
  exact ⟨b, a⟩

theorem make_second {s : S} (hp : plainThereB c.iU3 c.nW s = true)
    (hrd : ∀ g h, rd (φ s) = some (g, h) → s.heard5? = some h) {l : List Aff}
    (e : fsSecond rd c (fixed9 φ s) = some l) : EntsMake c.iU3 l := by
  unfold fsSecond at e
  obtain ⟨gh, e1, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨v, e2, e⟩ := Option.bind_eq_some_iff.1 e
  intro f hf x hx
  obtain ⟨a, b, _⟩ := plain_named_second hp (snap_fork φ e2) (hrd gh.1 gh.2 e1) e f hf x hx
  exact ⟨b, a⟩

/-- **THE CLAUSE entsFirst.** -/
theorem entsFirst_of_plain {nU : Array ℕ} {s : S} (hp : plainThereB c.iU3 c.nW s = true)
    (hrd : ∀ g h, rd (φ s) = some (g, h) → s.heard5? = some h)
    (hs : ∀ tlb v, (π (fixed9 φ s).1).1 = some tlb → (fixed9 φ s).2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π (fixed9 φ s).1).1 = some tlb → tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ l, fsFirst rd c (fixed9 φ s) = some l → EntsAt π nU (fixed9 φ s) l :=
  fun _ e => ents_of_static π hs hU h0 (make_first φ rd c hp hrd e)

/-- **THE CLAUSE entsSecond.** -/
theorem entsSecond_of_plain {nU : Array ℕ} {s : S} (hp : plainThereB c.iU3 c.nW s = true)
    (hrd : ∀ g h, rd (φ s) = some (g, h) → s.heard5? = some h)
    (hs : ∀ tlb v, (π (fixed9 φ s).1).1 = some tlb → (fixed9 φ s).2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π (fixed9 φ s).1).1 = some tlb → tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ l, fsSecond rd c (fixed9 φ s) = some l → EntsAt π nU (fixed9 φ s) l :=
  fun _ e => ents_of_static π hs hU h0 (make_second φ rd c hp hrd e)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.snap_fork
#print axioms VerifiableInference.Desc.LinkJoin.make_first
#print axioms VerifiableInference.Desc.LinkJoin.make_second
#print axioms VerifiableInference.Desc.LinkJoin.entsFirst_of_plain
#print axioms VerifiableInference.Desc.LinkJoin.entsSecond_of_plain
#print axioms H2K5.Door.plain_named_first
#print axioms H2K5.Door.plain_named_second
