-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/ClaimFits.lean: the proof of `ClaimFitsRaw`
(Johnson/Desc/K11/Front/ClaimFitsStatement.lean), to the letter. A lemma; none of the library's
goals.

How: calls. The claim that lies at 346 is what `weightsClaim` returns (`claimLaidRaw`,
ClaimLaid.lean of this folder). At the reference parameters that return is `headClaim`
(`weightsClaim_head`, Johnson/Top/H0/K11Caller/HeadClaim.lean), which passes `verify-on-bytes`'s
test on a claim's sizes (`headClaim_shape`, Johnson/Top/H0/K11Caller/AtFull.lean) where the vector
on the vocabulary has the vocabulary's size and the point on the channels has 13 coordinates or
more; and `claimFits` says yes just where that test returns (`claimFits_eq`,
Johnson/Top/H0/MergeLaw/Fits.lean). The vector's size: `avFold_value`
(Johnson/Road/HeadWeight.lean). The point's: what the head heard at 346 is what the output head's
yes laid (`backToHeadRaw`, Filled.lean of this folder; `Came.x_behind`,
Johnson/Desc/Kinds/Law/WeightTwinAt.lean), and its size is had as
Johnson/Desc/Kinds/Law/WtJoint.lean has it (`rs_size`, `zt_size_at`, `lPd_ref`). The closed facts on
the public data: Johnson/Desc/Sound/K11Tests/WeightsFactsInScope.lean.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Front.ClaimFitsStatement
import Johnson.Desc.K11.Front.ClaimLaid
import Johnson.Desc.K11.Front.Filled
import Johnson.Desc.Kinds.Law.WtJoint
import Johnson.Top.H0.K11Caller.AtFull
import Johnson.Top.H0.MergeLaw.Fits
import Johnson.Desc.Sound.K11Tests.WeightsFactsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Front
open OnBytes.Road.Hd (avOf avFold_value)
open VerifiableInference.Desc.Kinds.Norm (lt lPd)
open Inst.Model.Head (nV nD)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.First.K11Caller (headClaim weightsClaim_head headClaim_shape ewAt)
open VerifiableInference.Desc.First.MergeLaw (claimFits_eq)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

/-- **The claim fits the layout.** -/
theorem claimFitsRaw : ClaimFitsRaw := by
  intro Z D r Zp Np cF xP Bs z sF a claim h hB hr ha hcl
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨a', cov, x, t, claim', ha', _, _, hx, _, hcl', hwc⟩ :=
    claimLaidRaw Z D r Zp Np cF xP Bs' z sF h hB hr
  obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
  obtain rfl : claim' = claim := Option.some.inj (hcl'.symm.trans hcl)
  obtain ⟨s, s', rv, gs, hd, hW, hk⟩ := backToHeadRaw Z D r Zp Np cF xP Bs' z sF h hB hr
  obtain ⟨g, H, F1, a0, gk, Q, p1, p2, _, _, e⟩ := Came.x_behind _ _ _ _ hd
  obtain ⟨p, p', hp, hp', ex, _⟩ := hk
  obtain rfl : p' = a' := Here.head.inj (hp'.symm.trans ha)
  rw [e] at hp
  obtain rfl := Here.head.inj hp
  obtain rfl : heardOf gk H = x := Option.some.inj (ex.symm.trans hx)
  -- the closed facts on the public data
  have hplan := LT28.K11Tests.plan_fact h.scope h.reads O.public
  obtain ⟨shW, hz, hw⟩ := LT28.K11Tests.sized_fact h.scope h.reads O.public
  have hlam := LT28.K11Tests.lam_fact h.scope h.reads O.public
  have hV2 := LT28.K11Tests.vocab_fact h.scope h.reads O.public
  have hd5 := LT28.K11Tests.dim_fact h.scope h.reads O.public
  have hd' : VerifiableInference.Desc.Kinds.Norm.d = nD := by
    obtain ⟨_, _, _, _, _, rfl⟩ := Came.given_ok _ _ _ _ p1
    exact hd5
  have hs : 13 ≤ (runAt Bs'.G₀.W cov (heardOf gk H) t).x.rs.size := by
    have e1 := (Came.rs_size hW p2 (Came.zt_size_at Bs'.G₀.W p1 hplan)).trans (Came.lPd_ref hd')
    show 13 ≤ ((H.2.2.logits.r.extract lt (lt + lPd)).reverse).size
    rw [Array.size_reverse]
    exact Nat.le_of_eq e1.symm
  obtain ⟨q, sg, _, _, ecl, _⟩ := weightsClaim_head hz hw hwc hlam
  have hA : (avOf (runAt Bs'.G₀.W cov (heardOf gk H) t)
      (ewAt (runAt Bs'.G₀.W cov (heardOf gk H) t) q sg)).size = nV := by
    unfold avOf
    rw [(avFold_value OnBytes.Model.Reading.gl _ _ _ _ _ (v := 0)
      (by simp only [Array.size_map, Array.size_range]
          show 0 < Bs'.G₀.W.hS.V
          rw [hV2]
          decide) _).1]
    simp only [Array.size_map, Array.size_range]
    exact hV2
  show claimFits Bs'.G₀.W.layers.wsLay claim' = true
  rw [claimFits_eq, ecl, headClaim_shape hz hw _ _ hA hs]
  rfl

end Johnson.Desc.First.ForkMerge.Front

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Front.claimFitsRaw
