-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupShapeAndUsedSlots.lean: the kind "lookup" (K3): two small
public tests that `Accepted` asks at a site hold at every site of `lookSites Zp`, conditional on the
library's hypothesis `P5J.AtMgA` alone. Theorems; no definition; nothing is evaluated.

What is shown.
  `lookupShapeIsTheLayersShape`: the test on seven numbers: on the calls of a layers' link the site's
    shape is the layout's record `Zp.p.X.y.fo`. Idle at the other sites.
  `usedSlotsOfLayersPlan`: the plan of a layers' group in a public record has `used = ns`; on public
    data alone.
  `usedSlotsAtLayersDigits`, `usedSlotsAtAttentionDigits`: on the digits of a layers' and of an
    attention link: first slot + hidden values = the plan's slots in use; on public data alone.
  `lookupUsedSlotsAreTheLedgersCount`: the test on the slots in use: the same at every site on the
    digits whose caller is not the head. Idle at the other sites.

Hypotheses that remain. `atHead`: `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`. `siteIsListed`: the site stands in
`lookSites Zp`. In the two laws on public data: `publicRecord`: `Verify.publicOf pol KL layout = .ok W`.

How the proof goes. The first: `shape_layers_at` and `sameShape_self` (Johnson/AtFull/Shape/LookFree.lean).
The second: `public_G` and `planG_used` (Honest/K9/PlanUsed.lean): the plan's maker lays both numbers
from one. The others: `digits_lay`, `digits_att`, `Spec.slots_elems`, with `site_facts` for the site's
link, caller and group and `H2K5.Door.scope_all` for the two public numbers.

Limits. Public data alone: no state, no trace, no thread. What the numbers are is not said. That a
site stands at each link is not this file's. The witness that `P5J.AtMgA` holds is not this file's.
-/
import Johnson.AtFull.Shape.LookFree
import Johnson.Desc.ProofFile.Honest.K9.PlanUsed
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Windows
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.WindowsLay
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CallerAtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First.Look (P placeAt sameShape)
open ProofFile.Honest.K3 (Site lookSites usedAt callerOf)
open ProofFile.Honest.K3.Law (site_facts)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- The plan of a layers' group in a public record has as many slots in use as it has slots.
Conditional on the record's being what `Verify.publicOf` returns. -/
theorem usedSlotsOfLayersPlan {pol KL : ByteArray} {layout : Option ByteArray} {W : Verify.Public}
    (publicRecord : Verify.publicOf pol KL layout = .ok W) {g : Nat} {hp : Layer.HPlan2}
    (groupPlan : W.G[g]? = some hp) : hp.used = hp.ns :=
  ProofFile.Honest.K9.planG_used _ _ _ _ (Fo.Pub.public_G publicRecord g hp groupPlan)

/-- On the digits of a layers' link: the first slot and the face's hidden values end at the plan's
slots in use. Conditional on the record and on the place's parameters at an even link that is not
the head's, with two links to a group. -/
theorem usedSlotsAtLayersDigits {pol KL : ByteArray} {layout : Option ByteArray} {W : Verify.Public}
    (publicRecord : Verify.publicOf pol KL layout = .ok W) {i : Nat} {p : P} {sh : Forest.Shape}
    (placeParameters : placeAt W i true = some p) (placeShape : p.shape = some sh)
    (notTheHeadsLink : i ≠ (if W.p4 then 2 else 1) * W.NGr) (evenLink : i % (if W.p4 then 2 else 1) = 0) :
    W.G[i / (if W.p4 then 2 else 1)]?.map (·.used) = some (p.first + (faceOf sh).slots) := by
  obtain ⟨hp, groupPlan, e1, e2⟩ := ProofFile.Honest.K3.Good.Live.digits_lay publicRecord placeParameters notTheHeadsLink evenLink
  obtain rfl : hp.tl.f9 = sh := Option.some.inj (e1.symm.trans placeShape)
  rw [groupPlan, Option.map_some, usedSlotsOfLayersPlan publicRecord groupPlan, ProofFile.Honest.K3.Law.Spec.slots_elems, e2]

/-- On the digits of an attention link: the same, in the attention plan's number. Conditional on the
record, on two links to a group and on the group's plan. -/
theorem usedSlotsAtAttentionDigits {pol KL : ByteArray} {layout : Option ByteArray}
    {W : Verify.Public} (publicRecord : Verify.publicOf pol KL layout = .ok W) (twoLinksToAGroup : W.p4 = true) {g : Nat}
    {a : Attention.Plan} (attentionPlan : W.A[g]? = some a) {p : P} {sh : Forest.Shape}
    (placeParameters : placeAt W (2 * g + 1) true = some p) (placeShape : p.shape = some sh) :
    W.A[g]?.map (·.nMsg) = some (p.first + (faceOf sh).slots) := by
  obtain ⟨e1, -, e3⟩ := ProofFile.Honest.K3.Good.Live.digits_att publicRecord twoLinksToAGroup attentionPlan placeParameters
  obtain rfl : a.seam.tl.f9 = sh := Option.some.inj (e1.symm.trans placeShape)
  rw [attentionPlan, Option.map_some, ProofFile.Honest.K3.Law.Spec.slots_elems, e3]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The test on seven numbers accepts at every site.** Conditional on `P5J.AtMgA`. -/
theorem lookupShapeIsTheLayersShape (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (siteIsListed : s ∈ lookSites Zp) :
    (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true := by
  cases hd : s.digits with
  | true => rfl
  | false =>
    by_cases hc : s.caller = .layers
    · rw [Johnson.AtFull.Shape.shape_layers_at atHead s siteIsListed hd hc, Johnson.AtFull.Shape.sameShape_self]
      simp
    · have : (s.caller != .layers) = true := by
        cases e : s.caller <;> simp_all
      rw [this]
      simp

/-- **The test on the slots in use accepts at every site.** Conditional on `P5J.AtMgA`. -/
theorem lookupUsedSlotsAreTheLedgersCount (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (siteIsListed : s ∈ lookSites Zp) :
    (!s.digits || s.caller == .head ||
      usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true := by
  cases hd : s.digits with
  | false => rfl
  | true =>
    have publicRecord : Verify.publicOf _ _ _ = .ok Zp.p.X := atHead.toAtMg.pubOne
    have hs' := siteIsListed
    unfold lookSites at hs'
    obtain ⟨y, -, hy⟩ := List.mem_filterMap.1 hs'
    obtain ⟨f1, f2, f3, f4, -, f6, f7, f8⟩ := site_facts _ _ y s hy
    obtain ⟨p4, ng, -⟩ := H2K5.Door.scope_all atHead
    have p4' : Zp.p.X.p4 = true := p4
    have ng' : Zp.p.X.NGr = 12 := ng
    rw [← f3, ← f4, hd] at f1
    rw [← f3, p4', ng'] at f7 f8
    have key : s.caller = .head ∨
        usedAt Zp.p.X s = some (s.p.first + s.at_.face.slots) := by
      by_cases e24 : s.link = 24
      · left
        rw [f7, e24]
        simp [callerOf]
      · right
        rw [f6]
        by_cases em : s.link % 2 = 0
        · have hc : s.caller = .layers := by
            rw [f7]
            simp [callerOf, e24, em]
          have hgr : s.group = s.link / 2 := by
            rw [f8]
            simp [callerOf, e24, em]
          have e := usedSlotsAtLayersDigits publicRecord f1 f2
            (by simpa [p4', ng'] using e24) (by simpa [p4'] using em)
          simp only [p4', if_true] at e
          unfold usedAt
          rw [hc, hgr]
          exact e
        · have hc : s.caller = .attention := by
            rw [f7]
            simp [callerOf, e24, em]
          have hgr : s.group = s.link / 2 := by
            rw [f8]
            simp [callerOf, e24, em]
          have hlink : 2 * (s.link / 2) + 1 = s.link := by omega
          have hlook := f1
          unfold placeAt at hlook
          obtain ⟨xx, hx, -⟩ := Option.map_eq_some_iff.1 hlook
          unfold VerifiableInference.Desc.First.Look.lookAt at hx
          dsimp only at hx
          rw [if_neg (by simpa [p4', ng'] using e24), if_neg (by simpa [p4'] using em)] at hx
          simp only [p4', if_true] at hx
          obtain ⟨a, attentionPlan, -⟩ := Option.bind_eq_some_iff.1 hx
          have e := usedSlotsAtAttentionDigits publicRecord p4' attentionPlan (by rw [hlink]; exact f1) f2
          unfold usedAt
          rw [hc, hgr]
          exact e
    rcases key with k | k
    · simp [k]
    · simp [k]

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.usedSlotsOfLayersPlan
#print axioms ProofFile.Honest.K3.Term.usedSlotsAtLayersDigits
#print axioms ProofFile.Honest.K3.Term.usedSlotsAtAttentionDigits
#print axioms ProofFile.Honest.K3.Term.lookupShapeIsTheLayersShape
#print axioms ProofFile.Honest.K3.Term.lookupUsedSlotsAreTheLedgersCount
