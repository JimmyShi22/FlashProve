-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/ClaimLaid.lean: the proofs of `ClaimLaidRaw` and `NoneWaitsOfShape`
(Johnson/Desc/K11/Front/ClaimLaidStatement.lean), to the letter. Lemmas; none of the library's
goals.

How. The first: one step back from 346 (`P4.reach_last`, `P4.step_yes`, Johnson/P4R/Back341N.lean);
number 345 is the lookup on the digits with its quiet step, as `P4.digits_345`
(Johnson/P4R/WaK6At346.lean) finds it; a yes of it ends in a yes of the quiet step
(`stated_yes_head`, Johnson/Desc/Kinds/Law/DigitsKeptAtDecide.lean); and the state behind that step
is written out by `quietHead_form` (Johnson/Desc/Kinds/Law/QuietHeadGives.lean): the state in front
with the claim laid. The second: the place behind border 346 (`k11_hp`,
Johnson/Desc/Sound/MgAt/K11Places.lean); a count may not wait there: by evaluation.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Front.ClaimLaidStatement
import Johnson.P4R.WaK6At346
import Johnson.Desc.Sound.MgAt.K11Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Front
open VerifiableInference.Desc.Sound (linksFull psFull)
open VerifiableInference.Desc.Sound.MgAt (mergeAt k11_hp)
open VerifiableInference.Desc.First (S shapeAt mayWait)
open VerifiableInference.Desc.Kinds.Head.Law (stated_yes_head quietHead_form)

/-- **A claim is laid.** -/
theorem claimLaidRaw : ClaimLaidRaw := by
  intro Z D r Zp Np cF xP Bs z sF h hB hr
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨s345, B5, _, hB5, y5⟩ := P4.reach_last hr
  obtain ⟨rs, gs, hd⟩ := P4.step_yes y5
  obtain ⟨Lk, b, b', h1, h2, hb', hla⟩ := IM.k3_of h.scope h.reads O 24 (by decide) true
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope h.scope h.reads O (by decide) _] at h3
  obtain rfl : b = B5 := Option.some.inj (h3.symm.trans hB5)
  obtain ⟨e4, eN, -⟩ := Meaning.scope_plans h.scope h.reads O.public
  have hH : VerifiableInference.Desc.K3.isHead Bs'.G₀.W 24 = true := by
    unfold VerifiableInference.Desc.K3.isHead
    rw [e4, eN]
    rfl
  have hpc : (IM.k3Place 24 true).piece =
      VerifiableInference.Desc.K3.pieceAt Bs'.G₀.W 24 true := by
    unfold VerifiableInference.Desc.K3.pieceAt
    rw [hH]
    rfl
  obtain ⟨_, _, _, _, _, m, _, hq⟩ := stated_yes_head _ _ _ _ _ _ b' hb'
    (IM.plan_alone O h.laid.planOk h1 h2 hla) 24 rfl hpc hH s345 sF rs gs
    ((IM.k3_yes hla s345 sF rs gs).1 hd).1
  obtain ⟨a, cov, x, t, claim, _, hop, hc, hx, ht, hcl, rfl⟩ := quietHead_form Bs'.G₀.W hq
  exact ⟨_, cov, x, t, claim, rfl, hop, hc, hx, ht, rfl, hcl⟩

/-- **Nothing waits.** -/
theorem noneWaitsOfShape : NoneWaitsOfShape := by
  intro s hs
  have hp : psFull[346]? = some mergeAt := k11_hp
  rw [hp] at hs
  unfold shapeAt at hs
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hs
  rcases hs.1.2 with h | h
  · exact h
  · have e : mayWait linksFull mergeAt = false := by decide +kernel
    rw [e] at h
    cases h

end Johnson.Desc.First.ForkMerge.Front

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Front.claimLaidRaw
#print axioms Johnson.Desc.First.ForkMerge.Front.noneWaitsOfShape
