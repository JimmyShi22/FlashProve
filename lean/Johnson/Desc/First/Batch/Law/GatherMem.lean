-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/GatherMem.lean
(kind K9's soundness lemma): THEOREMS: WHAT A YES OF THE GATHERING SAYS OF EACH SINGLE RUN. General
in the state, the lens and the other kinds' letters, as Law/Gather.lean is.
  gather_mem    each run of the list said yes, at a state that goes on from what is fixed, is good
                and has a part with a coefficient for each slot; and whatever is later than the
                gathering's end is later than the state behind that run. (Law/Gather.lean's
                gather_fold says what the runs' claims add up to; not where each run stood.)
  later_add     whatever is later than the state behind the adding is later than the state in front
                of it.
By induction on the list, with gather_fold for the runs behind.
Not claimed: any premise at a real run. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.Gather

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where RunOf Window)

variable {T P K : Type} [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K)
  (Fx : P → T → Prop)

/-- **Each run of a gathering that says yes.** -/
theorem gather_mem (p : Where) (H : FitsM X O Fx p) (ws : T → List Window)
    (cut : List (Nat × String)) (q : P) :
    ∀ (rl : List (TermedRun T P K)), (∀ r ∈ rl, RunOk ρ X O Fx r.run.2 r.tm r.len) →
      ∀ (x out : List Claim × T) (a : K9.Part), Fx q x.2 → O.good x.2 → X.get? x.2 = some a →
      a.F.LS.size = a.F.ns → (rl.map (·.run)).foldlM (gstep ws cut) x = .ok out →
      ∀ r ∈ rl, ∃ front e ae c e₁, Fx q e ∧ O.good e ∧ X.get? e = some ae ∧
        ae.F.LS.size = ae.F.ns ∧ r.run.2 front e = .ok (c, e₁) ∧
        ∀ t, laterK X O out.2 t → laterK X O e₁ t
  | [], _, _, _, _, _, _, _, _, _, _, hr => absurd hr List.not_mem_nil
  | r0 :: l, hr, x, out, a, hf, hg, ha, hs, h, r, hmem => by
    rw [List.map_cons, List.foldlM_cons] at h
    obtain ⟨x', hx', h'⟩ := ok_bind h
    obtain ⟨c, e, hc, rfl⟩ := gstep_ok hx'
    obtain ⟨a₁, ha₁, k, _, g1, _, f1, _, _⟩ :=
      hr r0 List.mem_cons_self q x.1.length x.2 a c e hf hg ha hs hc
    obtain ⟨_, _, _, _, k5, k6⟩ := core_parts k
    have hs1 : a₁.F.LS.size = a₁.F.ns := by rw [k5, k6]; exact hs
    rcases List.mem_cons.1 hmem with e0 | hmem
    · obtain ⟨_, a₂, _, ha₂, k', _, _, m2, _, _, _⟩ :=
        gather_fold ρ X O Fx p H ws cut q l (fun z hz => hr z (List.mem_cons_of_mem _ hz))
          (x.1 ++ c, e) out a₁ f1 g1 ha₁ hs1 h'
      obtain ⟨_, j2, _, j4, _, _⟩ := core_parts k'
      rw [e0]
      refine ⟨x.1.length, x.2, a, c, e, hf, hg, ha, hs, hc, fun t ht =>
        ⟨?_, H.moreTrans _ _ _ m2 ht.2.1, ?_⟩⟩
      · rw [← ht.1]
        simp only [planOf, ha₁, ha₂, Option.map_some, j4]
      · rw [← ht.2.2]
        simp only [thetaOf, ha₁, ha₂, Option.map_some, j2]
    · exact gather_mem p H ws cut q l (fun z hz => hr z (List.mem_cons_of_mem _ hz)) (x.1 ++ c, e)
        out a₁ f1 g1 ha₁ hs1 h' r hmem

include ρ in
/-- **Later than behind the adding is later than in front of it.** -/
theorem later_add (p : Where) (H : FitsM X O Fx p) (q : P) (e₁ : T) (a₁ : K9.Part) (G : Fork)
    (c : List Claim) (f1 : Fx q e₁) (g1 : O.good e₁) (ha₁ : X.get? e₁ = some a₁)
    (hs1 : a₁.F.LS.size = a₁.F.ns) (hG : addAll a₁.F c = some G) (t : T)
    (ht : laterK X O (X.set e₁ { a₁ with F := G }) t) : laterK X O e₁ t := by
  obtain ⟨b, hb, hF⟩ := H.lens e₁ { a₁ with F := G } (by simp [ha₁])
  have hF' : b.F = G := hF
  obtain ⟨_, m2, _⟩ := H.atAdd q e₁ a₁ G c f1 g1 ha₁ hG
  have hGe := (addAll_total ρ ⟨fun _ => 0, fun _ _ _ => 0⟩ c a₁.F G hs1 hG).2
  have gθ : G.theta = a₁.F.theta := by rw [hGe.1]
  have gp : G.planClaimsF = a₁.F.planClaimsF := by rw [hGe.1]
  refine ⟨?_, H.moreTrans _ _ _ m2 ht.2.1, ?_⟩
  · rw [← ht.1]
    simp only [planOf, ha₁, hb, Option.map_some, hF', gp]
  · rw [← ht.2.2]
    simp only [thetaOf, ha₁, hb, Option.map_some, hF', gθ]

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.gather_mem
#print axioms VerifiableInference.Desc.K9L.later_add
