-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensPaid/ScopeFacts.lean (kind K9): what the test `lensEqB` (Johnson/Desc/K9/Honest/LensEq.lean)
leans on beside the planners' own sums, each drawn from the goals' scope by a lemma of the library; and the test's
equation at the output head's segment. Lemmas; no definition.

  `tsc_in_scope`    the list of the calls of the second token sumcheck is not empty: by `ts_of_lines`
                   (Johnson/Road/FormsKeysPansTS.lean) at `pub34_public`'s clauses
                   (Johnson/Goal/Meaning/Pub34Scope.lean)
  `xl_in_scope`, `p3_in_scope`   the layers' shape has five limbs and routed experts: `Switches`
  **`lens_head`**    at segment 24 the three readings of the test return, and the equation holds: the plan's number by
                   `planH2_nLin`, the reads by the library's `reads_head_eq`, five limbs by `FullH.XL`

Limits. In the goals' scope alone. `reads_head_eq` rests on a closed fact that Lean's kernel evaluates at written values
(`readsHead_written`, Johnson/Desc/First/Link/Law/K9ReadsHeadPaid.lean). `lens_head` is also a short name of the
library's, in another namespace, for another sentence (Johnson/Desc/First/Link/Law/LensAtFront.lean). Out of it the
equation can fail: by reading, at four limbs the plan counts fewer claims than the test adds up. No property of the
protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.K9.Honest.LensPaid.PlanNLin
import Johnson.Desc.First.Link.K9LensAsk
import Johnson.Desc.First.Link.Law.K9ReadsHeadPaid
import Johnson.Road.FormsKeysPansTS
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (K9Asks.pairsAt)
open VerifiableInference.Desc.K9Asks hiding pairsAt

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- In scope the list of the calls of the second token sumcheck is not empty. -/
theorem tsc_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) : X.layers.rd.tscCalls.isEmpty = false := by
  obtain ⟨hy, Sw, -, hrd, -, -, hN, -⟩ := _root_.Meaning.P34.pub34_public hS hR hpub
  have h := OnBytes.Road.ts_of_lines hy Sw.p3 hN hrd
  cases e : X.layers.rd.tscCalls with
  | nil =>
    rw [e] at h
    simp at h
  | cons a l => rfl

/-- In scope the layers' shape has five limbs. -/
theorem xl_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) : X.layers.y.h.xl = 5 := by
  obtain ⟨-, Sw, -⟩ := _root_.Meaning.P34.pub34_public hS hR hpub
  have ey : X.layers.y.h = Verify.layerShape X.P := (_root_.Meaning.scope_plans hS hR hpub).2.2.1
  rw [ey]
  exact Sw.xl

/-- In scope the layers' shape has routed experts. -/
theorem p3_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) : X.layers.y.h.p3 = true := by
  obtain ⟨-, Sw, -⟩ := _root_.Meaning.P34.pub34_public hS hR hpub
  have ey : X.layers.y.h = Verify.layerShape X.P := (_root_.Meaning.scope_plans hS hR hpub).2.2.1
  rw [ey]
  exact Sw.p3

/-- **The test's equation at the output head's segment.** -/
theorem lens_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hpub : Verify.publicOf Pb.pol Pb.KL lay = .ok X) :
    ∃ a ps n, ownLenB X 24 = some a ∧ K9Asks.pairsAt X 24 = some ps ∧ claimsAt X 24 = some n ∧
      a + (4 + (X.H.tl.NM + readsB X.H.tl.NM X.H.tl.mats ps)) + Forest.lins X.H.tl.f9 = n := by
  obtain ⟨ps, h1, h2⟩ := reads_head_eq hS hR hpub
  obtain ⟨H0, k1, k2⟩ := Fo.Pub.public_H hpub
  have hn : X.H.nLin =
      Head.claimsH X.hS X.HLy X.H.tl (Head.readsH X.hS X.HLy (Verify.borderOf X.layers.y)) := by
    rw [k2]
    exact planH2_nLin _ _ _ _ _ _ _ H0 k1
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have Bc := (OnBytes.Road.Hd.eleven_of_core hpub C (OnBytes.Road.Hd.npOf X.hS)).1
  have xl : X.hS.XL = 5 := Bc.full.XL
  refine ⟨_, ps, _, by unfold ownLenB; rw [if_pos rfl], by unfold K9Asks.pairsAt; rw [if_pos rfl]; exact h1,
    by unfold claimsAt; rw [if_pos rfl], ?_⟩
  rw [hn, h2]
  unfold Head.claimsH HTailF2.lins HTailF2.linsF
  rw [xl]
  have e1 : ledNO 5 = 4 := rfl
  have e2 : ledNS 5 = 9 := rfl
  have e3 : ledLines 5 = 8 := rfl
  rw [e1, e2, e3]
  omega

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.tsc_in_scope
#print axioms ProofFile.Honest.K9.xl_in_scope
#print axioms ProofFile.Honest.K9.p3_in_scope
#print axioms ProofFile.Honest.K9.lens_head
