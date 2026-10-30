-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/AsksAtWrap.lean: the smallness test: what the laws on the values ask
of the state in front of a segment's batching, each as one end, at every state that WrapEnd admits (a
state that the first chain's blocks, with the test on words in front, reach at that batching). Under
the goals' scope, the files read, an opening of the description and its test on its plan. Every field
is a call of a law of the library. Its user is AtFullSide/K8/TailAtSorts.lean.

  layAsks_at_wrap   LayAsks at a layers' segment
  attAsks_at_wrap   AttAsks at an attention segment, with the third vector's array and the segment's
                    own state
  headWants_at_wrap HeadWants at the head's segment, with the third vector's array

Limits. Nothing says that WrapEnd admits any state. The full size alone, the first chain alone, at
OnBytes.secondHashFunction. These are laws on the verifier's reached states; no prover stands in them.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.P1K8R.StillAtAll
import Johnson.P1K8R.BehindAtReach
import Johnson.P1K8R.BehindAtRch
import Johnson.P1K8R.LeftAtBatch
import Johnson.P1K8R.NamedAtBatch
import Johnson.P1K8R.HereAtBatch
import Johnson.P1K8R.HeadDigitsAtBatch
import Johnson.Desc.K8.Honest.AllFrontAtHeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open _root_.P1K8

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **What the layers' sentence asks of the state in front of the batching.** -/
theorem layAsks_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {p4 : OnBytes.Desc.First.K4.Par}
    (hp : LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4) {s : S} (w : WrapEnd Z c (2 * g) s)
    {tl : HTailF2} (ht : s.tl? = some tl) : LayAsks p4 ((tl.ix.U.getD 2 none).getD 0) s := by
  have St := stillAtZ_all hS hR O hOk (l := 2 * g) (by omega) w
  obtain ⟨zp, r⟩ := w
  have n24 : ¬ 2 * g = 24 := by omega
  have h' := reach_raw r
  have h9 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 9) (zp, s) := by
    have k := h'
    rw [if_neg n24] at k
    exact k
  have h28 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (zp, s) := by
    rw [show 28 * g + 9 = 14 * (2 * g) + 9 by omega]
    exact h9
  obtain ⟨t1, h1, hu⟩ := u2_at_batch hS hR O (l := 2 * g) (by omega) h'
  obtain rfl : tl = t1 := Option.some.inj (ht.symm.trans h1)
  obtain ⟨k, hk, kb⟩ := callsRows_layers hS hR O hOk hg h28
  obtain ⟨d, hd, db⟩ := digitsRows_at_batch hS hR O hOk (l := 2 * g) (by omega) h9
  refine ⟨fun q hq => ?_, fun q hq => ?_, ?_⟩
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kb
  · obtain rfl : d = q := Option.some.inj (hd.symm.trans hq)
    exact db
  · rw [hu]
    exact fun o ho => St.layers g p4 o rfl hg hp ho

/-- **What the attention's sentence asks.** -/
theorem attAsks_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Ap : Attention.Plan} (hA : Bs.G₀.W.A[g]? = some Ap) {s : S}
    (w : WrapEnd Z c (2 * g + 1) s) {tl : HTailF2} (ht : s.tl? = some tl) :
    AttAsks s ∧ tl.ix.U.getD 2 none = some Ap.iU3 ∧
      ∃ a : AttOwn, s.here = .att a ∧ Att.P.U3At Ap (Att.P.plannedK Ap) a.F := by
  have St := stillAtZ_all hS hR O hOk (l := 2 * g + 1) (by omega) w
  obtain ⟨zp, r⟩ := w
  have n24 : ¬ 2 * g + 1 = 24 := by omega
  have h' := reach_raw r
  have h9 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (zp, s) := by
    have k := h'
    rw [if_neg n24] at k
    exact k
  obtain ⟨t1, h1, hu⟩ := u2_at_batch hS hR O (l := 2 * g + 1) (by omega) h'
  obtain rfl : tl = t1 := Option.some.inj (ht.symm.trans h1)
  obtain ⟨k, hk, kb⟩ := callsRows_att hS hR O hOk hg h9
  obtain ⟨k', hk', kc, kl⟩ := callsLeft_att hS hR O hOk hg h9
  obtain rfl : k = k' := Option.some.inj (hk.symm.trans hk')
  obtain ⟨d, hd, db⟩ := digitsRows_at_batch hS hR O hOk (l := 2 * g + 1) (by omega) h9
  obtain ⟨h5, e5, p5⟩ := St.five g Ap rfl hA
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, ⟨h5, e5, p5⟩⟩, ?_,
    here_at_batch hS hR O hg hA h9 e5⟩
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kb
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kc
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kl
  · obtain rfl : d = q := Option.some.inj (hd.symm.trans hq)
    exact db
  · rw [(P1K2.att_u3 O.public hA).1]
    exact hu

/-- **What the head's sentence asks.** -/
theorem headWants_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {s : S} (w : WrapEnd Z c 24 s) {tl : HTailF2} (ht : s.tl? = some tl) :
    HeadWants Bs.G₀.W.hS 0 (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) s ∧
      tl.ix.U.getD 2 none = some 0 := by
  obtain ⟨zp, r⟩ := w
  have r7 : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (zp, s) := r
  have h7 : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (zp, s) := reach_raw r7
  obtain ⟨t1, h1, hu⟩ := u2_at_batch hS hR O (l := 24) (by omega) (reach_raw r)
  obtain rfl : tl = t1 := Option.some.inj (ht.symm.trans h1)
  obtain ⟨k, hk, kb⟩ := callsRows_head hS hR O hOk h7
  obtain ⟨k', hk', kc, kl⟩ := callsLeft_head hS hR O hOk h7
  obtain rfl : k = k' := Option.some.inj (hk.symm.trans hk')
  obtain ⟨d, hd, -, -, db⟩ := digitsHeard_head hS hR O hOk h7 (sized_at_head_wrap hS hR O hOk r7)
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, parOk_atW hS hR O hOk,
    k6_at_rch hS hR O hOk (Str := Unit) ((zp, s), ()) r7,
    head_at_rch hS hR O hOk (Str := Unit) ((zp, s), ()) r7, mergeBare_at_batch hS hR O h7⟩, hu⟩
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kb
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kc
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kl
  · obtain rfl : d = q := Option.some.inj (hd.symm.trans hq)
    exact db

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.layAsks_at_wrap
#print axioms ProofFile.Honest.K8.attAsks_at_wrap
#print axioms ProofFile.Honest.K8.headWants_at_wrap
