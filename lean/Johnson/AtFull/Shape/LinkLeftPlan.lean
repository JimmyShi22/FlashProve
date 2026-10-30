-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LinkLeftPlan.lean: THE CODE SWITCH AT THE FIRST PLACE OF LINKS 1 TO 23: THREE
CLAUSES OF THE LAW "THE KIND's OWN DECISION SAYS YES" (LinkPlain,
Johnson/Desc/K2/Honest/Returns/LinkSent.lean) THAT READ NOTHING OF THE STATE BUT ITS CODES, THE
FRAME's SHAPE, ITS GROUPS AND ITS LINK's NUMBER: plain · own · plan: AT EVERY STATE THAT IS REACHED
THERE, WHOEVER PLAYS. Under the head P5J.AtMgA.

How. At such a state the codes and the frame's shape are the public part's, its groups are that
shape's, and it stands at the link (atSwitch_reached, AtSwitchReached.lean; no mark:
IM.noMark_reach, Johnson/IMR/NoMarkReach.lean). Under the head the public part's codes and shape are
the written ones (written_of_head, Johnson/Road/K4/K4HeadWritten.lean; shape_one,
Johnson/Road/K4/K4PlanTied.lean). So each of the three is a closed sentence on the written values
and a number below 24.

  `ownOneB`, `twoB sh G l`: plain and own as one test on a shape, its groups and a link's number.
    `two_says`: what its yes says at a state whose frame has that shape, these groups and that
    number, in the letters of the front's term (frontAt, Johnson/Desc/K2/Honest/Returns/Link.lean).
  `planB cs sh G l`, `plan_says`: the like for plan: the shared sending's own test on its plan
    (K1.planOkOwn, Johnson/Desc/K1/Own.lean) at the notices that the front's term lays; it reads the
    codes and the notices alone.
  `twoB_full`, `planB_full`: yes at the written values at each l from 1 to 23. `twoB_can_fail`: no
    at link 24. `planB_can_fail`: no at link 1 with no codes.
  `noMark_at_switch`: a state reached at 14 l + 2 bears no mark.
  **`link_two_reached`**, **`link_plan_reached`**: under the head, m < 23, at every state reached at
    14 (m + 1) + 2 (THE RAW FAMILY), at the frame's own segment L and group Q: the three.

THE DEVICE. The four closed facts are closed by "decide +kernel" under a raised maxRecDepth.

Limits. THREE CLAUSES, OF THE 67 THAT LinkPlain's PREMISES COME TO WHEN LAID OPEN, BY ITS AUTHORS'
COUNT. Of a reached state: that anything is reached is not said. The links' places alone; the full
size alone. That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed`
accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named
sets of public files, in a side library. At the format's second hash function. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.AtSwitchReached
import Johnson.Desc.K2.Honest.Returns.LinkSent
import Johnson.Road.K4.K4HeadWritten
import Johnson.IMR.NoMarkReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest.Returns (frontAt)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- The clause "own" at one message and its notice. -/
def ownOneB (sh : Params.ReqShape) (m : Params.ReqMessage) (n : OracleNotice) : Bool :=
  n.shape.answers != 0 && (n.shape.mainRows == 0 || n.shape.code == sh.code) &&
    (n.shape.maskRows == 0 || n.shape.maskCode == sh.maskCode) &&
    (!decide (0 < m.life) || decide (0 < n.shape.mainRows))

/-- **The two as one test.** G: the shape's groups. -/
def twoB (sh : Params.ReqShape) (G : Array ReqGroup) (l : Nat) : Bool :=
  let f : ReqFrame := { shape := sh, groups := G, link := l }
  let own := f.atMoment 0
  let others := ReqFrame.notices own ++ #[foldMaskNotice (f.foldShape l {})]
  (sh.link[l]?).all (fun L => L.plain == 0) &&
    (List.range own.length).all fun j =>
      match own[j]?, others[j]? with
      | some m, some n => ownOneB sh m n
      | some _, none => false
      | none, _ => true

/-- **What its yes says.** -/
theorem two_says {s : S} {L : Params.ReqLink} (Q : ReqGroup)
    (h : twoB s.check.frame.shape s.check.frame.groups s.check.frame.link = true)
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L) :
    L.plain = 0 ∧
      ∀ (j : Nat) (m : Params.ReqMessage), (frontAt s L Q).own[j]? = some m →
        ∃ n, (frontAt s L Q).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
          (n.shape.mainRows = 0 ∨ n.shape.code = s.check.frame.shape.code) ∧
          (n.shape.maskRows = 0 ∨ n.shape.maskCode = s.check.frame.shape.maskCode) ∧
          (0 < m.life → 0 < n.shape.mainRows) := by
  unfold twoB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [hL] at h1
  refine ⟨beq_iff_eq.1 h1, fun j m hm => ?_⟩
  have hm' : (s.check.frame.atMoment 0)[j]? = some m := hm
  have hj : j < (s.check.frame.atMoment 0).length := (List.getElem?_eq_some_iff.1 hm').1
  have h3 := List.all_eq_true.1 h2 j (List.mem_range.2 hj)
  have h4 : (match (s.check.frame.atMoment 0)[j]?, (frontAt s L Q).others[j]? with
      | some m, some n => ownOneB s.check.frame.shape m n
      | some _, none => false
      | none, _ => true) = true := h3
  rw [hm'] at h4
  cases hn : (frontAt s L Q).others[j]? with
  | none =>
    rw [hn] at h4
    cases h4
  | some n =>
    rw [hn] at h4
    have h5 : ownOneB s.check.frame.shape m n = true := h4
    unfold ownOneB at h5
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq, ne_eq] at h5
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h5
    exact ⟨n, rfl, a1, a2, a3, fun k => a4.resolve_left (fun c => c k)⟩

/-- **The clause "plan" as a test** on the codes, a shape, its groups and a link's number: the
shared sending's own test on its plan, at the notices that the front's term lays. -/
def planB (cs : Codes) (sh : Params.ReqShape) (G : Array ReqGroup) (l : Nat) : Bool :=
  let f : ReqFrame := { shape := sh, groups := G, link := l }
  (G[l]?).all fun Q =>
    VerifiableInference.Desc.K1.planOkOwn
      { place := default, codes := cs, gp := ⟨0, 0⟩, work := 0
        parts := [("", _root_.Tw.K2.switchNotices Q.target
          (ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape l {})]))] }

/-- What its yes says. -/
theorem plan_says (p : VerifiableInference.Desc.First.K2.P2) {s : S} (L : Params.ReqLink)
    {Q : ReqGroup}
    (h : planB s.st.codes s.check.frame.shape s.check.frame.groups s.check.frame.link = true)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    VerifiableInference.Desc.K1.planOkOwn
      (VerifiableInference.Desc.K2.Honest.Returns.sendingAt p (frontAt s L Q)) = true := by
  unfold planB at h
  rw [hQ] at h
  exact h

set_option maxRecDepth 1000000 in
/-- Lean's kernel says yes at the written codes and shape at each link from 1 to 23. -/
theorem planB_full : ((List.range 24).all fun l =>
    l == 0 || planB proofSizedFull.codes proofSizedFull.request
      (reqGroups proofSizedFull.request) l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: at no codes. -/
theorem planB_can_fail :
    planB {} proofSizedFull.request (reqGroups proofSizedFull.request) 1 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Lean's kernel says yes at the written shape at each link from 1 to 23.** -/
theorem twoB_full : ((List.range 24).all fun l =>
    l == 0 || twoB proofSizedFull.request (reqGroups proofSizedFull.request) l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test can fail**: at link 24. -/
theorem twoB_can_fail :
    twoB proofSizedFull.request (reqGroups proofSizedFull.request) 24 = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- A state that is reached in front of a link's first place bears no mark. -/
theorem noMark_at_switch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat}
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + 2) (p, s)) :
    s.failed = none := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine IM.noMark_reach h.scope h.reads O hr (by omega) fun l' _ => ?_
  unfold IM.nAt
  split <;> omega

/-- **THE TWO AT EVERY STATE REACHED IN FRONT OF THE SWITCH INTO A LATER GROUP.** -/
theorem link_two_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (m + 1) + 2) (p, s)) {L : Params.ReqLink}
    (Q : ReqGroup) (hL : s.check.frame.shape.link[s.check.frame.link]? = some L) :
    L.plain = 0 ∧
      ∀ (j : Nat) (mm : Params.ReqMessage), (frontAt s L Q).own[j]? = some mm →
        ∃ n, (frontAt s L Q).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
          (n.shape.mainRows = 0 ∨ n.shape.code = s.check.frame.shape.code) ∧
          (n.shape.maskRows = 0 ∨ n.shape.maskCode = s.check.frame.shape.maskCode) ∧
          (0 < mm.life → 0 < n.shape.mainRows) := by
  have A := atSwitch_reached h (by omega : m + 1 < 25) hr (noMark_at_switch h hr)
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have esh : s.check.frame.shape = proofSizedFull.request :=
    A.shape.trans (W.shape.trans OnBytes.Road.K4.shape_one)
  refine two_says Q ?_ hL
  rw [A.groups, A.link, ← A.shape, esh]
  have k := List.all_eq_true.1 twoB_full (m + 1) (List.mem_range.2 (by omega))
  rw [Bool.or_eq_true] at k
  rcases k with k | k
  · exact absurd (beq_iff_eq.1 k) (by omega)
  · exact k

/-- **THE CLAUSE "plan" THERE.** -/
theorem link_plan_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (m + 1) + 2) (p, s))
    (q : VerifiableInference.Desc.First.K2.P2) (L : Params.ReqLink) {Q : ReqGroup}
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q) :
    VerifiableInference.Desc.K1.planOkOwn
      (VerifiableInference.Desc.K2.Honest.Returns.sendingAt q (frontAt s L Q)) = true := by
  have A := atSwitch_reached h (by omega : m + 1 < 25) hr (noMark_at_switch h hr)
  have W := OnBytes.Road.K4.written_of_head h.toAtMg
  have esh : s.check.frame.shape = proofSizedFull.request :=
    A.shape.trans (W.shape.trans OnBytes.Road.K4.shape_one)
  refine plan_says q L ?_ hQ
  rw [A.groups, A.link, ← A.shape, esh, A.codes, W.codes]
  have k := List.all_eq_true.1 planB_full (m + 1) (List.mem_range.2 (by omega))
  rw [Bool.or_eq_true] at k
  rcases k with k | k
  · exact absurd (beq_iff_eq.1 k) (by omega)
  · exact k

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.plan_says
#print axioms Johnson.AtFull.Shape.planB_full
#print axioms Johnson.AtFull.Shape.planB_can_fail
#print axioms Johnson.AtFull.Shape.link_plan_reached
#print axioms Johnson.AtFull.Shape.two_says
#print axioms Johnson.AtFull.Shape.twoB_full
#print axioms Johnson.AtFull.Shape.twoB_can_fail
#print axioms Johnson.AtFull.Shape.noMark_at_switch
#print axioms Johnson.AtFull.Shape.link_two_reached
