-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/TargetReached.lean: `FrontCore.restMain` · `keptAnswers` ·
`groupCode` · `copiesCode` (Returns/SentFront.lean) AT THE FRONT OF A SWITCH, AT A STATE THAT IS
REACHED IN FRONT OF IT, AT ALL THREE SORTS OF PLACE, IN THE GOALS' SCOPE, WITH NO TEST ON THE PUBLIC
PART. The first two stand in Returns/PinPublic.lean under three tests; the last two are among what
Returns/LinkRest.lean and Returns/CallJoin.lean leave. Statements with their proofs: calls.

  `link_target_reached`, `head_target_reached`, `fin_target_reached` the four clauses at `frontAt s
                    L Q`, `headFrontOf s a Q.target`, `finFrontOf t a Q`, each in `FrontCore`'s own
                    letters, the code being the frame's shape's main code; FOR ALL Q that are the
                    state's own (the frame's group at its segment; at the third place `a.G = some
                    Q`)

By: `front_target_fit` (Returns/TargetPlan.lean) · the library's `recAll_reached`
(Johnson/IMR/AtReach.lean): the frame's shape is the plan's and passes the test that the frame's
start puts · `reqOk_shape` (OnBytes/Params/Fit/TreesSized.lean): which holds the shape's own test ·
`sw_link`, `sw_head`, `sw_finish` (Johnson/P1K2R/HstReached.lean): the frame's groups are the
shape's; the segment's number · `front_len` (Johnson/IMR/FinPin.lean) · `finishFrontQ_fr`,
`finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean) · `reach_raw`
(Johnson/Top/H0/Walk/Reach.lean). Near relatives, not called: `front_pin_link`, `front_pin_head`
(Johnson/IMR/FrontPin.lean), `front_pin_fin` (Johnson/IMR/FinPin.lean): at a front that the place
reads the target is the plan's.

Limits. The look-ups, the quiet front's yes and `here` at the third place are premises; there "the
shape has 25 segments" too. "Reached" is: over the list of the wrapped sub-protocols. THE PREMISES
IN FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. This file's imports are heavy. Nothing on
any property.

-/
import Johnson.Desc.K2.Honest.Returns.TargetPlan
import Johnson.Desc.K2.Honest.Returns.LinkReached
import Johnson.Top.H0.Tw.K2C.FinFront
import OnBytes.Params.Fit.TreesSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (finishFrontQ finishFrontQ_fr finishFrontQ_rest headFrontOf
  finFrontOf)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P1K2 (Prep Nums numsAt prepOf sw_link sw_head sw_finish)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **At the switch into a later group.** -/
theorem link_target_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) {Q : ReqGroup}
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    (frontAt s L Q).T.rest.part = .main ∧
      (∀ k ∈ (frontAt s L Q).T.kept.toList, k.shape.answers ≠ 0) ∧
      (frontAt s L Q).T.shape.code = s.check.frame.shape.code ∧
      ∀ k ∈ (frontAt s L Q).T.kept.toList, k.shape.code = s.check.frame.shape.code := by
  have Q0 := (sw_link hS hR O hF hpl h23 hP hn hr).1
  have hlen : 14 * (m + 1) + 2 ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.K2.front_len hS hR O]
    omega
  have RA := Meaning.K2.recAll_reached hS hR O (reach_raw hr) (by omega) hlen
  have hok : reqShapeOk s.check.frame.shape = true := by
    rw [Q0.shape]
    exact Params.reqOk_shape RA.ok
  exact front_target_fit hok (l := s.check.frame.link) (by rw [← Q0.groups]; exact hQ)
    (by rw [Q0.link]; omega) rfl rfl

/-- **At the output head's switch.** -/
theorem head_target_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) (a : HeadOwn)
    {Q : ReqGroup} (group : s.check.frame.groups[s.check.frame.link]? = some Q) :
    (headFrontOf s a Q.target).T.rest.part = .main ∧
      (∀ k ∈ (headFrontOf s a Q.target).T.kept.toList, k.shape.answers ≠ 0) ∧
      (headFrontOf s a Q.target).T.shape.code = s.check.frame.shape.code ∧
      ∀ k ∈ (headFrontOf s a Q.target).T.kept.toList, k.shape.code = s.check.frame.shape.code := by
  have Q0 := (sw_head hS hR O hF hpl default "" hP hn hr).1
  have hlen : 339 ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.K2.front_len hS hR O]
    omega
  have RA := Meaning.K2.recAll_reached hS hR O (reach_raw hr) (by omega) hlen
  have hok : reqShapeOk s.check.frame.shape = true := by
    rw [Q0.shape]
    exact Params.reqOk_shape RA.ok
  exact front_target_fit hok (l := s.check.frame.link) (by rw [← Q0.groups]; exact group)
    (by rw [Q0.link]; omega) rfl rfl

/-- **Behind the quiet front of the place behind the last segment.** -/
theorem fin_target_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (hq : finishFrontQ s = .ok t)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q) :
    (finFrontOf t a Q).T.rest.part = .main ∧
      (∀ k ∈ (finFrontOf t a Q).T.kept.toList, k.shape.answers ≠ 0) ∧
      (finFrontOf t a Q).T.shape.code = t.check.frame.shape.code ∧
      ∀ k ∈ (finFrontOf t a Q).T.kept.toList, k.shape.code = t.check.frame.shape.code := by
  have Q0 := (sw_finish hS hR O hF hpl h25 default "" hP hn hr hq).1
  have hlen : 353 ≤ (Meaning.K2.frontOf c).length :=
    le_of_eq (Meaning.K2.front_len hS hR O).symm
  have RA := Meaning.K2.recAll_reached hS hR O (reach_raw hr) (by omega) hlen
  have hok : reqShapeOk s.check.frame.shape = true := by
    rw [Q0.shape]
    exact Params.reqOk_shape RA.ok
  obtain ⟨a', G, ha', hG, hgr, -, -, hlk, hfg, -⟩ := finishFrontQ_fr hq
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.fin a' = .fin a := ha'.symm.trans here
    cases e
    rfl
  obtain rfl : G = Q := Option.some.inj (hG.symm.trans laid)
  exact front_target_fit hok (l := a'.fr.link) (by rw [← Q0.groups, ← hfg]; exact hgr)
    (by rw [hlk, Q0.link]; omega) rfl (by rw [(finishFrontQ_rest hq).2.2.2.2.1])

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_target_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_target_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_target_reached
