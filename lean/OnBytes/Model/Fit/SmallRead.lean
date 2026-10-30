-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/SmallRead.lean: if every entry of the six plans that the planner makes for a key
and a proof is Small, so is every entry of the six plans as the program reads them back.

OnBytes/Model/Fit/ReadNormMade.lean says that the six plans as read back are the plans as made
with every number modulo 2^64, where the made plans' names are in order.
OnBytes/Params/Fit/FitBlocks.lean says that Small goes over to the reduced entry, and what Small
gives in the format's own terms. This file lays the two together, at what Verify.planned returns.

Main definitions: Six (a condition on entries holds of all entries of the six plans as read back);
Fits (in the format's terms: positions are drawn below 2^64; the blocks that a round's draws can
take, and one more, are fewer than 2^48; at most two roots).
Main theorems: small_read, fits_read.

What is not claimed: that the made plans' entries are Small: a premise. Nothing on the entry's
chain. Nothing on soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Model.Fit.PlanTestsSmall
import OnBytes.Params.Fit.FitBlocks

set_option autoImplicit false

namespace OnBytes.Model.Verify

open OnBytes.Params

/-- Q holds of every entry of the six plans as read back. -/
def Six (Q : Fmt.Entry → Prop) (p : Planned) : Prop :=
  ((∀ e ∈ p.chains.key.oneTime.given.plan.entries, Q e) ∧
      (∀ e ∈ p.chains.key.shared.given.plan.entries, Q e) ∧
      ∀ e ∈ p.chains.key.second.given.plan.entries, Q e) ∧
    (∀ e ∈ p.chains.proof.first.given.plan.entries, Q e) ∧
    (∀ e ∈ p.chains.proof.shared.given.plan.entries, Q e) ∧
    ∀ e ∈ p.chains.proof.second.given.plan.entries, Q e

/-- What Small gives in the format's terms. -/
def Fits (e : Fmt.Entry) : Prop :=
  e.logN ≤ 64 ∧ Fmt.blocksFor (Fmt.wordsAtMost e .sealed) + 1 < 2 ^ 48 ∧ e.roots ≤ 2

theorem fits_of_small {e : Fmt.Entry} (h : Small e) : Fits e :=
  ⟨(small_blocks h).1, (small_blocks h).2, h.2.1⟩

theorem Six.mono {Q Q' : Fmt.Entry → Prop} {p : Planned} (hq : ∀ e, Q e → Q' e)
    (h : Six Q p) : Six Q' p :=
  ⟨⟨fun e he => hq e (h.1.1 e he), fun e he => hq e (h.1.2.1 e he),
      fun e he => hq e (h.1.2.2 e he)⟩,
    fun e he => hq e (h.2.1 e he), fun e he => hq e (h.2.2.1 e he),
    fun e he => hq e (h.2.2.2 e he)⟩

/-- The entries of a made plan whose rounds are Small. -/
theorem small_entries {P : Params.Planned} (h : ∀ r ∈ P.rounds, Small r.entry) :
    ∀ e ∈ P.plan.entries, Small e := by
  intro e he
  have he' : e ∈ P.rounds.map (·.entry) := he
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he'
  exact h r hr

/-- **Small of the made plans gives Small of the plans as read back.** -/
theorem small_read {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p)
    (hs : ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, ∀ r ∈ P.rounds, Small r.entry) :
    Six Small p := by
  obtain ⟨l, x, hm, hK, hP⟩ := planned_made h
  obtain ⟨_, _, K1, K2, K3, ek, _⟩ := configure_plans hm
  obtain ⟨F, S2, S3, ep, _⟩ := configure_proofPlans hm
  have hk : ∀ P ∈ p.chains.made.key, ∀ r ∈ P.rounds, Small r.entry :=
    fun P hPm => hs P (List.mem_append_left _ hPm)
  have hp : ∀ P ∈ p.chains.made.proof, ∀ r ∈ P.rounds, Small r.entry :=
    fun P hPm => hs P (List.mem_append_right _ hPm)
  obtain ⟨a1, a2, a3⟩ := key_read_norm hm hK (fun P hPm => spelt_of_small (hk P hPm)) ek
  obtain ⟨b1, b2, b3⟩ := proof_read_norm hm hP (fun P hPm => spelt_of_small (hp P hPm)) ep
  rw [ek] at hk
  rw [ep] at hp
  unfold Six
  rw [a1, a2, a3, b1, b2, b3]
  exact ⟨⟨small_plan (small_entries (hk K1 (by simp))),
      small_plan (small_entries (hk K2 (by simp))),
      small_plan (small_entries (hk K3 (by simp)))⟩,
    small_plan (small_entries (hp F (by simp))),
    small_plan (small_entries (hp S2 (by simp))),
    small_plan (small_entries (hp S3 (by simp)))⟩

/-- The same in the format's terms. -/
theorem fits_read {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p)
    (hs : ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, ∀ r ∈ P.rounds, Small r.entry) :
    Six Fits p :=
  (small_read h hs).mono fun _ => fits_of_small

/-- A plan's rounds are among its entries. -/
theorem mem_rounds {P : Fmt.Plan} {e : Fmt.Entry} (h : e ∈ P.rounds) : e ∈ P.entries :=
  (List.mem_filter.1 h).1

end OnBytes.Model.Verify
