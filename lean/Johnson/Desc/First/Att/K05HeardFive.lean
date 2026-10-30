-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05HeardFive.lean: the lengths of what was heard, from Said
(Att/K5SaidAll.lean), in the place's numbers.

Main names:
  `chal_len`: a sumcheck's challenges are as many as its variables.
  `heard_six`: the six sumchecks behind the units: the number of challenges as an equation; and the
    drawn point's length.
  `heard_five`: five inequalities that follow, at geoOf S, as a plain conjunction.

Premises: the shape's Norm; 1 ≤ lnT; P.D = dimOf S; kap = 4; Said at recOf P rows.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5SaidAll
import Johnson.Desc.First.Att.LeftP
import Johnson.Desc.First.Att.GeoOf
import OnBytes.Tie.Pv.Att.OwnAtFits
import Johnson.Road.Lane5AttNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes.Tie.Pv.Att (PscH recOf)
open OnBytes.Road.L5 (dimOf)
open VerifiableInference.Desc.Part

/-- A sumcheck's challenges are as many as its variables. -/
theorem chal_len {C : Aff} {vs : List MaskedSum.Var} {e : MaskedSum.Ends} {pre : List E} {H : PscH}
    {hh : MaskedSum.Heard} {G : Fork} (h : SumAt C (.sum vs e) pre H hh G) : (chal hh).size = vs.length := by
  obtain ⟨vs', e', _, _, _, e1, sd, _⟩ := h
  cases e1
  have hl : H.rs.length = vs.length := by simpa using congrArg List.length sd.lens
  unfold chal
  rw [sd.r, List.dropLast_concat, List.size_toArray, List.length_map, hl]

variable {S : Attention.Shape} {K M X : Type} [Field K] [Fintype K]

/-- The six sumchecks behind the units, and the drawn point. -/
theorem heard_six (N : OnBytes.Road.L5.Norm S) (hl : 1 ≤ S.lnT) (P : OwnPar K M X) (hD : P.D = dimOf S) (hk : P.kap = 4)
    (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (b2 : Said (recOf P rows) h G L) :
    (chal h.division).size = S.cf.lgk + S.cf.lt ∧ (chal h.below).size = S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB ∧
      (chal h.on).size = S.cf.lgk + S.lnT + S.cf.lB ∧ (chal h.atIndex).size = S.cf.lt + S.cf.lgk + S.cf.ldh ∧
      (chal h.key).size = 2 * S.cf.lt + S.cf.lgk ∧ (chal h.cells).size = S.cf.lt + S.cf.lgk + 4 ∧
      h.point.size = 2 * S.cf.lgk + 2 * S.cf.lt + 4 := by
  have hlt := N.lt
  have kE := chal_len b2.sE
  have kM := chal_len b2.sM
  have kO := chal_len b2.sVD
  have kF := chal_len b2.sF
  have kK := chal_len b2.sD
  have kH := chal_len b2.sH
  rw [List.length_replicate] at kE kM kO kF kH
  simp only [List.length_map, List.length_append, List.length_replicate] at kK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kE]
    show AttSeg.Step.s8.g P.D = _
    rw [hD]
    show S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) = S.cf.lgk + S.cf.lt
    omega
  · rw [kM]
    show AttSeg.Step.s11.g P.D = _
    rw [hD]
    show S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB = S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB
    omega
  · rw [kO]
    show AttSeg.Step.s12.g P.D = _
    rw [hD]
    show S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB = S.cf.lgk + S.lnT + S.cf.lB
    omega
  · rw [kF]
    show AttSeg.Step.s16.g P.D = _
    rw [hD]
    show (S.lnT - 1 + 1 + S.cf.lB) + S.cf.lgk + S.cf.ldh = S.cf.lt + S.cf.lgk + S.cf.ldh
    omega
  · rw [kK]
    show P.D.lT + P.D.lg + P.D.lT = _
    rw [hD]
    show (S.lnT - 1 + 1 + S.cf.lB) + S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) = 2 * S.cf.lt + S.cf.lgk
    omega
  · rw [kH]
    show P.D.lT + P.D.lg + P.kap = _
    rw [hk, hD]
    show (S.lnT - 1 + 1 + S.cf.lB) + S.cf.lgk + 4 = S.cf.lt + S.cf.lgk + 4
    omega
  · rw [b2.point, List.size_toArray, b2.lPt]
    show 2 * P.D.lg + 2 * P.D.lT + 4 = _
    rw [hD]
    show 2 * S.cf.lgk + 2 * (S.lnT - 1 + 1 + S.cf.lB) + 4 = 2 * S.cf.lgk + 2 * S.cf.lt + 4
    omega

/-- The five inequalities of HeardLens7, at the shape's place. -/
theorem heard_five (N : OnBytes.Road.L5.Norm S) (hl : 1 ≤ S.lnT) (P : OwnPar K M X) (hD : P.D = dimOf S) (hk : P.kap = 4)
    (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (b2 : Said (recOf P rows) h G L) :
    (geoOf S).lgk + (geoOf S).lt ≤ h.point.size ∧ 2 * (geoOf S).lt + (geoOf S).lgk ≤ (chal h.key).size ∧
      (geoOf S).lt ≤ (chal h.cells).size ∧
      (geoOf S).lgk + 2 * (geoOf S).lnT - 1 + (geoOf S).lB ≤ (chal h.below).size ∧
      (geoOf S).lgk + (geoOf S).lnT + (geoOf S).lB ≤ (chal h.on).size := by
  obtain ⟨_, a2, a3, _, a5, a6, a7⟩ := heard_six N hl P hD hk rows b2
  rw [a2, a3, a5, a6, a7]
  show S.cf.lgk + S.cf.lt ≤ _ ∧ 2 * S.cf.lt + S.cf.lgk ≤ _ ∧ S.cf.lt ≤ _ ∧ S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB ≤ _ ∧
    S.cf.lgk + S.lnT + S.cf.lB ≤ _
  omega

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.heard_six
#print axioms VerifiableInference.Desc.First.Att.P.heard_five
