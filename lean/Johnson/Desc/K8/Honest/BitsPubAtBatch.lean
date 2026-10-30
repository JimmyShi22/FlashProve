-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/BitsPubAtBatch.lean: THE SMALLNESS TEST: THE TWO PUBLIC SENTENCES OF
`BitsPub` (Johnson/Desc/K8/Honest/PlanesShape.lean: the digits' lookup has two calls; one bit
numbers them) AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF A SEGMENT's
BATCHING, IN THE GOALS' SCOPE. Two of the four fields of one of the eight sentences of
`FrontLeftOver` (Johnson/Desc/K8/Honest/AllFrontAtBatch.lean). Lemmas; none of the library's goals.

  `two_calls_of_tests`   Fo.ZTests tl tl' F (OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsRun.lean) ⊢
                   tl.f9.NC = 2 and tl.f9.cK = 1: its first test has the first; its sixth says 2 ^
                   cK = NC
  **`two_calls_at_batch`**   at the state's own data
  `bitsPub_of_sizes`   so there BitsPub tl g from its two other fields, on what the lookup heard
By: `tests_at_built` (Johnson/P1K8R/StaticAtBuilt.lean) · DgP.tailOK_of_test
(OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean) · `arraysView`, `planned_arrays`
(Johnson/Desc/K8/Honest/ArraysAtBatch.lean) · LinkJoin.planned_at_batch
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean).
Limits. The two other fields of BitsPub (the sizes of the two points zb0 and zb1 that the lookup has
heard) ARE PAID BY NOBODY HERE. IN SCOPE ALONE: the full size's 25 segments; under an opening of the
description; the first chain; the family of states from the description's own first state. Nothing
says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ArraysAtBatch
import Johnson.P1K8R.StaticAtBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- Two calls, and one bit to number them. -/
theorem two_calls_of_tests {tl tl' : HTailF2} {F : Fork} (T : _root_.Fo.ZTests tl tl' F) :
    tl.f9.NC = 2 ∧ tl.f9.cK = 1 := by
  have h1 : tl.f9.NC = 2 := (DgP.tailOK_of_test T.t1).nc
  have h6 := T.t6
  rw [h1] at h6
  refine ⟨h1, ?_⟩
  have h2 : 2 ^ tl.f9.cK = 2 ^ 1 := h6
  exact Nat.pow_right_injective (Nat.le_refl 2) h2

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING.** -/
theorem two_calls_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : tl.f9.NC = 2 ∧ tl.f9.cK = 1 := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have g := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_arrays hS hR O hx e3 (z, s) h') tl ht
  simp only [arraysView, Prod.mk.injEq] at g
  obtain ⟨-, -, -, -, -, -, g7, -⟩ := g
  rw [g7]
  exact two_calls_of_tests (_root_.P1K8.tests_at_built hS O hl e3)

/-- So `BitsPub` there, from its two other fields. -/
theorem bitsPub_of_sizes (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) {g : Forest.Heard}
    (h0 : g.zb0.size = 5 + (tl.f9.kT + tl.f9.cK)) (h1 : g.zb1.size = 5 + (tl.f9.kT + tl.f9.cK)) :
    BitsPub tl g :=
  ⟨(two_calls_at_batch hS hR O hl e3 h ht).1, (two_calls_at_batch hS hR O hl e3 h ht).2, h0, h1⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.two_calls_of_tests
#print axioms VerifiableInference.Desc.First.K8.Honest.two_calls_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.bitsPub_of_sizes
