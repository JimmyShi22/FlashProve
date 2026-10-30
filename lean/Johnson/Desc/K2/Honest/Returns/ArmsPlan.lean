-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ArmsPlan.lean: TWO CLAUSES OF THE CALL OF THE SWITCH THAT
Returns/LinkReached.lean PAYS AT THE LINKS, AT THE TWO OTHER SORTS OF PLACE (NUMBERS 339 AND 353),
AT A REACHED STATE, IN THE GOALS' SCOPE, WITH NO TEST ON THE PUBLIC PART: `FrontCore.keptPos` (each
kept copy has a main row) AND `CallCore.oldCode` (the carried rows' main code is the frame's
shape's, so the code that stands there in the statement's list is the old main code). Statements
with their proofs: calls.

  `k7_fr`, `head_fr_reached` behind the place that hears the reply, and so at every state reached at
                    339: the head's own frame has the walk's segment number. THE LIBRARY's
                    `h1_headFr` (Johnson/IMR/ListsEnds.lean) and `h1_fr` (Johnson/IMR/FrameAll.lean)
                    say it at segment 24's block; `behind_k7_reached` (Returns/ArmsReached.lean)
                    asks it at every segment's: their lines stand here again
  `kept_pos_list` the library's `kept_pos` at the test that the frame's start puts, and at a group
                    by its number
  `head_keptPos_reached`, `fin_keptPos_reached` `keptPos` at `headFrontOf s a Q.target` |
                    `finFrontOf t a Q`
  `head_oldCode_reached`, `fin_oldCode_reached` `oldCode` there, FOR ALL c₀ that stand in the
                    statement's list of main codes at the frame's shape's code

By, all the library's: `recAll_reached` (Johnson/IMR/AtReach.lean), `RecAll.walk`
(Johnson/Goal/Meaning/RecAll.lean): the record's public part is the plan's, in every copy of the
frame · `rows_of_pub` (Johnson/IMR/FrontPin.lean) · `kept_pos`
(Johnson/Goal/Meaning/KeptRowsPos.lean) · `sw_head`, `sw_finish` (Johnson/P1K2R/HstReached.lean) ·
`front_len` (Johnson/IMR/FinPin.lean) · `headFrontQ_fr` (Johnson/Top/H0/Tw/K2C/HeadLink.lean) ·
`finishFrontQ_fr`, `finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean) · `andThen_yes`
(Johnson/IMR/FoldTools.lean) · `guarded_yes` (Johnson/Desc/Sound/SeatGuardLaws.lean) ·
`reply_record` (Johnson/Desc/Kinds/Law/ReplyPins.lean) · `reach_raw`
(Johnson/Top/H0/Walk/Reach.lean). This folder's: `behind_k7_reached` (Returns/ArmsReached.lean) ·
`finishFrontQ_rows` (Returns/ClosedArms.lean). Near relatives, not called: `front_pin_head`
(Johnson/IMR/FrontPin.lean), `front_pin_fin` (Johnson/IMR/FinPin.lean): from the fold's return, at a
front that the place reads: its carried rows' two codes are the first chain's shape's, they have two
masks, its target and its other notices are the plan's: `oldCode` reads off them too.

Limits. `here`, the frame's group's look-up, the quiet front's yes and `a.G = some Q` are premises;
at 353 "the shape has 25 segments" too. "Reached" is: over the list of the wrapped sub-protocols.
THE PREMISES IN FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. This file's imports are
heavy. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.ArmsReached
import Johnson.Desc.K2.Honest.Returns.ClosedArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription guarded_yes)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (headFrontQ finishFrontQ headFrontQ_fr finishFrontQ_fr
  finishFrontQ_rest headFrontOf finFrontOf)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (andThen_yes kept_pos rows_of_pub)
open P1K2 (Prep Nums numsAt prepOf sw_head sw_finish)
open ProofFile (Cl)

/-- Behind the place that hears the reply the head's own frame has the walk's segment number. -/
theorem k7_fr {X : OnBytes.Model.Verify.Public} {l : Nat} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k7Block X l).decide s rs gs = .ok t) :
    ∀ a, t.here = .head a → a.fr.link = t.check.frame.link := by
  obtain ⟨m, a1, a2⟩ := andThen_yes h
  have hq : headFrontQ X.H.tl s = .ok m := ((guarded_yes _ (fun _ => false) _ rfl s _ _ m).1 a1).1
  obtain ⟨a', ha', -, f2, -⟩ := headFrontQ_fr hq
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Kinds.Head.Law.Came.reply_record l X.hS.V a2
  intro a ha
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.head a' = .head a := ha'.symm.trans ha
    cases e
    rfl
  exact f2

/-- The library's `kept_pos` at the test that the frame's start puts, and at a group by its
number. -/
theorem kept_pos_list {codes : Codes} {sh : Params.ReqShape} (h : reqOk codes sh = true) {l : Nat}
    {G : ReqGroup} (hG : (reqGroups sh)[l]? = some G) :
    ∀ k ∈ G.target.kept.toList, 0 < k.shape.mainRows := by
  unfold reqOk at h
  simp only [Bool.and_eq_true] at h
  exact kept_pos h.1 G (Array.mem_toList_iff.2 (Array.mem_of_getElem? hG))

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

theorem head_fr_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) :
    ∀ a, s.here = .head a → a.fr.link = s.check.frame.link :=
  behind_k7_reached (fun s => ∀ a, s.here = .head a → a.fr.link = s.check.frame.link)
    (fun _ _ _ _ _ _ h => k7_fr h) hS hR O s (reach_raw hr)

/-- **`FrontCore.keptPos` at the head's front.** -/
theorem head_keptPos_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) (a : HeadOwn)
    {Q : ReqGroup} (group : s.check.frame.groups[s.check.frame.link]? = some Q) :
    ∀ k ∈ (headFrontOf s a Q.target).T.kept.toList, 0 < k.shape.mainRows := by
  have Q0 := (sw_head hS hR O hF hpl default "" hP hn hr).1
  have hlen : 339 ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.K2.front_len hS hR O]
    omega
  have RA := Meaning.K2.recAll_reached hS hR O (reach_raw hr) (by omega) hlen
  have hok : reqOk s.st.codes s.check.frame.shape = true := by
    rw [RA.codes, Q0.shape]
    exact RA.ok
  exact kept_pos_list hok (l := s.check.frame.link) (by rw [← Q0.groups]; exact group)

/-- **`CallCore.oldCode` at the head's front.** -/
theorem head_oldCode_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) (T : SwitchTarget) {c₀ : Code}
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀) :
    (headFrontOf s a T).st.codes.base[(headFrontOf s a T).f.rows.code]? = some c₀ := by
  have Q0 := (sw_head hS hR O hF hpl default "" hP hn hr).1
  have hlen : 339 ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.K2.front_len hS hR O]
    omega
  have RA := Meaning.K2.recAll_reached hS hR O (reach_raw hr) (by omega) hlen
  have hmem : a.fr ∈ Meaning.K2.framesIn s := by
    unfold Meaning.K2.framesIn
    rw [here]
    simp
  have hne : a.fr.link ≠ 0 := by
    rw [head_fr_reached hS hR O hr a here, Q0.link]
    omega
  show s.st.codes.base[a.fr.rows.code]? = some c₀
  rw [(rows_of_pub (RA.frames _ hmem) hne).1, ← RA.walk.shape]
  exact hc

/-- **`FrontCore.keptPos` at the front behind the last segment.** -/
theorem fin_keptPos_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (hq : finishFrontQ s = .ok t)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q) :
    ∀ k ∈ (finFrontOf t a Q).T.kept.toList, 0 < k.shape.mainRows := by
  have Q0 := (sw_finish hS hR O hF hpl h25 default "" hP hn hr hq).1
  have hlen : 353 ≤ (Meaning.K2.frontOf c).length :=
    le_of_eq (Meaning.K2.front_len hS hR O).symm
  have RA := Meaning.K2.recAll_reached hS hR O (reach_raw hr) (by omega) hlen
  have hok : reqOk s.st.codes s.check.frame.shape = true := by
    rw [RA.codes, Q0.shape]
    exact RA.ok
  obtain ⟨a', G, ha', hG, hgr, -, -, -, hfg, -⟩ := finishFrontQ_fr hq
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.fin a' = .fin a := ha'.symm.trans here
    cases e
    rfl
  obtain rfl : G = Q := Option.some.inj (hG.symm.trans laid)
  exact kept_pos_list hok (l := a'.fr.link) (by rw [← Q0.groups, ← hfg]; exact hgr)

/-- **`CallCore.oldCode` at the front behind the last segment.** -/
theorem fin_oldCode_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (hq : finishFrontQ s = .ok t)
    {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup) {c₀ : Code}
    (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀) :
    (finFrontOf t a Q).st.codes.base[(finFrontOf t a Q).f.rows.code]? = some c₀ := by
  have Q0 := (sw_finish hS hR O hF hpl h25 default "" hP hn hr hq).1
  have hlen : 353 ≤ (Meaning.K2.frontOf c).length :=
    le_of_eq (Meaning.K2.front_len hS hR O).symm
  have RA := Meaning.K2.recAll_reached hS hR O (reach_raw hr) (by omega) hlen
  obtain ⟨a', ha', hrows⟩ := finishFrontQ_rows hq
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.fin a' = .fin a := ha'.symm.trans here
    cases e
    rfl
  have hne : s.check.frame.link ≠ 0 := by
    rw [Q0.link]
    omega
  show t.st.codes.base[a'.fr.rows.code]? = some c₀
  rw [hrows, (rows_of_pub RA.walk hne).1, ← RA.walk.shape, ← (finishFrontQ_rest hq).2.2.2.2.1]
  exact hc

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.k7_fr
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_fr_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.kept_pos_list
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_keptPos_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_oldCode_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_keptPos_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_oldCode_reached
