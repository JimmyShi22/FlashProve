-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EntsHead.lean: THE TWO CLAUSES "entsK6" AND "entsJoin" OF WHAT IS FIXED
IN FRONT OF THE HEAD's BATCHING, FROM THE HEAD's FILES' MAKE. Statements and proofs: calls.

The make (EntsAtBatch.lean: every entry that a form of the run names stands at virtual row 0 of the
array of the third vector) is `fsK6_row0`, `fsJoin_row0`
(Johnson/Desc/Kinds/Law/K6RunsRow0.lean): in the letters of `fsK6` and `fsJoin` themselves.

  `make_of_row0`: `Row0 iU3 K3` of every form of l gives `EntsMake iU3 l`.
  `entsK6_of`: **at every name**: the plan's two (hok, hsz); the clause k6 (`K6Ready`) at q;
    `TabsBelow` at q; the static clause at q; the fixed structure names iU3 for the third vector;
      the third vector is planned with at least one entry ⊢ ∀ l, fsK6 h iU3 p kap name q = some l →
      `EntsAt π nU q l`.
  `entsJoin_of`: **the like of fsJoin**, with one premise more: hbare: the form in which the key
    side of the lookup on the calls ends names no entry.
Limits. ALL THESE PREMISES STAY: `K6Ready`, `TabsBelow` and hbare are shown of no state here. No
soundness statement.
-/
import Johnson.Desc.First.Link.Law.EntsAtBatch
import Johnson.Desc.Kinds.Law.K6RunsRow0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

theorem make_of_row0 {iU3 K3 : ℕ} {l : List Aff} (h : ∀ f ∈ l, Row0 iU3 K3 f) :
    EntsMake iU3 l := fun f hf x hx => ⟨(h f hf x hx).2.1, (h f hf x hx).1⟩

variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))
  (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) (kap : α → Option Seen)

/-- **THE CLAUSE entsK6, AT EVERY NAME.** -/
theorem entsK6_of {nU : Array ℕ} {q : α × Option Pub9} (hok : p.ok = true)
    (hsz : p.sizes = sizesOf h)
    (hk : ∀ y w, kap q.1 = some y → q.2 = some w → K6Ready h iU3 p y w.F)
    (hT : ∀ y w, kap q.1 = some y → q.2 = some w → ∃ K3, TabsBelow iU3 y w.F K3)
    (hs : ∀ tlb v, (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π q.1).1 = some tlb → tlb.ix.U.getD 2 none = some iU3)
    (h0 : 0 < nU.getD 2 0) (name : String) :
    ∀ l, fsK6 h iU3 p kap name q = some l → EntsAt π nU q l := by
  intro l e
  cases hz : kap q.1 with
  | none =>
    unfold fsK6 at e
    rw [hz] at e
    exact nomatch e
  | some z =>
    cases hu : q.2 with
    | none =>
      unfold fsK6 at e
      rw [hz, hu] at e
      exact nomatch e
    | some u =>
      obtain ⟨K3, hT'⟩ := hT z u hz hu
      exact ents_of_static π hs hU h0
        (make_of_row0 (fsK6_row0 h iU3 p kap hok hsz q z u hz hu K3 (hk z u hz hu) hT' name l e))

/-- **THE CLAUSE entsJoin.** -/
theorem entsJoin_of {nU : Array ℕ} {q : α × Option Pub9} (hok : p.ok = true)
    (hsz : p.sizes = sizesOf h)
    (hk : ∀ y w, kap q.1 = some y → q.2 = some w → K6Ready h iU3 p y w.F)
    (hT : ∀ y w, kap q.1 = some y → q.2 = some w → ∃ K3, TabsBelow iU3 y w.F K3)
    (hb : ∀ y g, kap q.1 = some y → y.lookHeard = some g → g.cEnd.ents = #[])
    (hs : ∀ tlb v, (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π q.1).1 = some tlb → tlb.ix.U.getD 2 none = some iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ l, fsJoin h iU3 p kap q = some l → EntsAt π nU q l := by
  intro l e
  cases hz : kap q.1 with
  | none =>
    unfold fsJoin at e
    rw [hz] at e
    exact nomatch e
  | some z =>
    cases hu : q.2 with
    | none =>
      unfold fsJoin at e
      rw [hz, hu] at e
      exact nomatch e
    | some u =>
      obtain ⟨K3, hT'⟩ := hT z u hz hu
      exact ents_of_static π hs hU h0
        (make_of_row0 (fsJoin_row0 h iU3 p kap hok hsz q z u hz hu K3 (hk z u hz hu) hT'
          (fun g hg => hb z g hz hg) l e))

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.make_of_row0
#print axioms VerifiableInference.Desc.LinkJoin.entsK6_of
#print axioms VerifiableInference.Desc.LinkJoin.entsJoin_of
