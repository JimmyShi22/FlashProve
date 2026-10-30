-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/KeepsReadings.lean: WHAT THE BATCHING's CLAUSE OF "KEEPS" (`K9Keeps`, Honest/K9/Keeps.lean) LEAVES, FOR
ANY READING OF THE VERIFIER's STATE AT ONCE: under the library's hypothesis `AtMgA`, at each of the 25 seated links, a reading
g that rests under the four writings of the runs (`FieldRests g`) and under the laying of the batching's own part has the
same value behind as in front. And one instance that the first chain's invariant asks: in a feed-forward segment the
state stays in that segment and what the segment's own rounds returned stays.

  **`bat_keeps_reading`**   `K9Keeps p ‹the link's gatherer› s s'` ⊢ g s' = g s
  `layOwnOf`, `rests_layOwnOf`, `set_layOwnOf`   the reading "in a feed-forward segment, and what its own rounds returned"
  **`own_over_batching`**   g < 12: `k9KeepsAt cF Zp ‹the batching's place› s s'` ⊢ ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧
                          a'.own = a.own

Limits. That the clause holds of any pair of states is not shown here (Honest/K9/KeepsAtPlace.lean: behind every yes of the
seated block's step). The full size and the hash function `secondHashFunction` alone. This file proves no property of a prover or a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.BatAtHead
import Johnson.Desc.ProofFile.Honest.K9.KeepsAtPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (FieldRests)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Every reading that rests is the same behind the batching as in front.** -/
theorem bat_keeps_reading (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) {γ : Type} (g : S → γ) (R : FieldRests g)
    (hset : ∀ e q, g (Desc.K9.atS.set e q) = g e) {s s' : S}
    (K : K9Keeps p (claimsInBy Lk.each Lk.hear Lk.order) s s') : g s' = g s :=
  K.left (fun u v => g v = g u) (fun _ => rfl) (fun _ _ _ a b => b.trans a) (fun u _ q _ _ => hset u q)
    fun o ho run hr n u z hz => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
      exact rests_at_head h hl Sd g R j o run hj hr n u z hz

/-- In a feed-forward segment: what the segment's own rounds returned. Elsewhere nothing. -/
def layOwnOf (s : S) : Option (Option Layer.Own) :=
  match s.here with
  | .lay a => some a.own
  | _ => none

theorem rests_layOwnOf : FieldRests layOwnOf where
  tl s tl := by
    unfold layOwnOf S.putTl
    cases h : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [h, ho]
    | _ => simp [h]
  fork s G := by
    unfold layOwnOf S.putFork
    cases h : s.here with
    | head a => by_cases ho : a.opened = true <;> simp [h, ho]
    | _ => simp [h]
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold layOwnOf
    simp [h1]
  head s a G h := by
    unfold layOwnOf
    simp [h]

theorem set_layOwnOf (s : S) (q : Desc.K9.Part) : layOwnOf (Desc.K9.atS.set s q) = layOwnOf s := by
  show layOwnOf { (s.putLink q.L).putFork q.F with st := q.d.st, rowsOwed := q.owed } = layOwnOf s
  unfold layOwnOf S.putFork S.putLink
  cases h : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [h, ho]
  | _ => simp [h]

/-- **What a feed-forward segment's own rounds returned stays over the batching.** -/
theorem own_over_batching (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) {s s' : S}
    (K : k9KeepsAt cF Zp (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place s s') :
    ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  intro a ha
  have e := bat_keeps_reading h hl Sd layOwnOf rests_layOwnOf set_layOwnOf (bat_of_k9KeepsAt Sd K)
  unfold layOwnOf at e
  rw [ha] at e
  cases hs : s'.here with
  | lay a' =>
    rw [hs] at e
    exact ⟨a', rfl, Option.some.inj e⟩
  | _ => rw [hs] at e; exact nomatch e

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.bat_keeps_reading
#print axioms ProofFile.Honest.K9.rests_layOwnOf
#print axioms ProofFile.Honest.K9.set_layOwnOf
#print axioms ProofFile.Honest.K9.own_over_batching
