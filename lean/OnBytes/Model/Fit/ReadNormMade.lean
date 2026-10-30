-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/ReadNormMade.lean: the plans of a key's and of a proof's chains as read back are
the plans as made with every number modulo 2^64, where the made plans' names fit and none is
"configuration"; so, under that condition, the tests on the first and the shared chain's plans hold
of what the program computes from the three configuration files.

OnBytes/Model/ReadBackMade.lean (key_read_made, proof_read_made) says "read = made" where the made
plans fit the format's words. With OnBytes/Params/Fit/ReadNorm.lean and ReadPrefix.lean no number
needs a bound, nor the number of entries: what is asked is that the entries' names fit and that no
entry has the name of the configuration's item.

Main definition: Spelt (a made plan's names fit, and none is the configuration's item's).
Main theorems: key_read_norm, proof_read_norm, endsSeal_norm, planTests_planned_norm.

What is not claimed: Spelt of any made plan: a premise. planTests_planned_norm asks it of all six
made plans and uses it of four (the two second chains' plans are idle there). Nothing on
soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Model.Fit.PlanTestsPlanned
import OnBytes.Params.Fit.ReadPrefix

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

/-- The names of the plan's entries fit, and none is the name of the configuration's item. -/
def Spelt (P : Planned) : Prop :=
  (∀ e ∈ P.plan.entries, nameFit e.name = true) ∧
    ∀ e ∈ P.plan.entries, e.name ≠ configName

section
variable {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}

/-- A key's three plans as read back are the plans as made, reduced. -/
theorem key_read_norm (h : configure l x cfg bits = .ok made) {k : KeyChains}
    (hk : KeyChains.read made.keyOneTime made.keyShared made.keySecond = some k)
    (hf : ∀ P ∈ made.key, Spelt P) {P1 P2 P3 : Planned} (hm : made.key = [P1, P2, P3]) :
    k.oneTime.given.plan = normP P1.plan ∧ k.shared.given.plan = normP P2.plan ∧
      k.second.given.plan = normP P3.plan := by
  obtain ⟨Q1, Q2, Q3, _, _, _, hq, _, e1, e2, e3, _, _, _, _⟩ := configure_bytes h
  rw [hm] at hq hf
  obtain ⟨rfl, rfl, rfl⟩ : P1 = Q1 ∧ P2 = Q2 ∧ P3 = Q3 := by
    simpa using hq
  obtain ⟨r1, r2, r3, _, _⟩ := KeyChains.read_three hk
  have g1 := OneTime.read_given r1
  have g2 := Shared.read_given r2
  have g3 := Second.read_given r3
  rw [e1] at g1
  rw [e2] at g2
  rw [e3] at g3
  have f1 := hf P1 (by simp)
  have f2 := hf P2 (by simp)
  have f3 := hf P3 (by simp)
  exact ⟨Given.read_whole f1.1 f1.2 g1, Given.read_whole f2.1 f2.2 g2,
    Given.read_whole f3.1 f3.2 g3⟩

/-- The same for a proof's three plans. -/
theorem proof_read_norm (h : configure l x cfg bits = .ok made) {k : ProofChains}
    (hk : ProofChains.read made.first made.shared made.second = some k)
    (hf : ∀ P ∈ made.proof, Spelt P) {F S2 S3 : Planned} (hm : made.proof = [F, S2, S3]) :
    k.first.given.plan = normP F.plan ∧ k.shared.given.plan = normP S2.plan ∧
      k.second.given.plan = normP S3.plan := by
  obtain ⟨_, _, _, Q1, Q2, Q3, _, hq, _, _, _, _, e1, e2, e3⟩ := configure_bytes h
  rw [hm] at hq hf
  obtain ⟨rfl, rfl, rfl⟩ : F = Q1 ∧ S2 = Q2 ∧ S3 = Q3 := by
    simpa using hq
  obtain ⟨r1, r2, r3, _, _⟩ := ProofChains.read_three hk
  have g1 := First.read_given r1
  have g2 := Shared.read_given r2
  have g3 := Second.read_given r3
  rw [e1] at g1
  rw [e2] at g2
  rw [e3] at g3
  have f1 := hf F (by simp)
  have f2 := hf S2 (by simp)
  have f3 := hf S3 (by simp)
  exact ⟨Given.read_whole f1.1 f1.2 g1, Given.read_whole f2.1 f2.2 g2,
    Given.read_whole f3.1 f3.2 g3⟩

end

/-- "The last entry asks for no work" goes over to the reduced plan. -/
theorem endsSeal_norm {P : Plan} (h : EndsSeal P.rounds) : EndsSeal (normP P).rounds := by
  unfold EndsSeal at h ⊢
  rw [rounds_norm, List.getLast?_map]
  cases hl : P.rounds.getLast? with
  | none =>
    rw [hl] at h
    cases h
  | some e =>
    rw [hl] at h
    have w : e.work = 0 := Option.some.inj h
    show some ((normE e).work) = some 0
    show some (e.work % 2 ^ 64) = some 0
    rw [w]

theorem length_norm (P : Plan) : (normP P).rounds.length = P.rounds.length := by
  rw [rounds_norm, List.length_map]

end OnBytes.Params

namespace OnBytes.Model.Verify

open OnBytes.Params

/-- **From the program's yes on the three configuration files**, where the made plans' names fit
and none is the name of the configuration's item. -/
theorem planTests_planned_norm {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p)
    (hf : ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, Spelt P) :
    (2 ≤ p.chains.key.oneTime.given.rounds.length ∧
        EndsSeal p.chains.key.oneTime.given.rounds ∧
        EndsSeal p.chains.key.shared.given.rounds) ∧
      (2 ≤ p.chains.proof.first.given.rounds.length ∧
        EndsSeal p.chains.proof.first.given.rounds ∧
        EndsSeal p.chains.proof.shared.given.rounds) := by
  obtain ⟨l, x, hm, hK, hP⟩ := planned_made h
  obtain ⟨_, _, K1, K2, K3, ek, _⟩ := configure_plans hm
  obtain ⟨F, S2, S3, ep, _⟩ := configure_proofPlans hm
  obtain ⟨a1, a2, _⟩ := key_read_norm hm hK
    (fun P hPm => hf P (List.mem_append_left _ hPm)) ek
  obtain ⟨b1, b2, _⟩ := proof_read_norm hm hP
    (fun P hPm => hf P (List.mem_append_right _ hPm)) ep
  obtain ⟨⟨t1, t2, t3⟩, t4, t5, t6⟩ := planTests_made hm ek ep
  unfold Given.rounds
  rw [a1, a2, b1, b2, length_norm, length_norm]
  exact ⟨⟨t1, endsSeal_norm t2, endsSeal_norm t3⟩, t4, endsSeal_norm t5, endsSeal_norm t6⟩

end OnBytes.Model.Verify
