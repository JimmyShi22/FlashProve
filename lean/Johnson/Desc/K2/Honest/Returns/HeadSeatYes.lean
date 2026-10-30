-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/HeadSeatYes.lean: AT THE OUTPUT HEAD's SWITCH (the number 339 of the
first chain's flat list): UNDER THE HEAD `P5J.AtMg` AND THE OPENING IN ITS LETTERS, AT EVERY STATE
REACHED THERE: THE SUB-PROTOCOL THAT THE PROOF FILE's DESCRIPTION SEATS SAYS YES AT TWO ROUNDS AND
COLUMNS AT WHICH THIS FOLDER's LAW GIVES THE CODE SWITCH's OWN YES (`head_behind_at_head`,
Returns/HeadAtReached.lean: its premises he, hrf and `HeadRest` stay premises here). So the named
premise of Returns/HeadAfter.lean, `BehindReturns`, is paid there. A join, with one closed test by
Lean's kernel on the written shape. Statements with their proofs.

  `headGroup_k7Block`, `headGroup_reached` behind a yes of the sub-protocol at 338, so at every
                    state reached at 339: the group at the number in the head's own frame is the
                    fresh one, with the shape's main code AND its mask's code
  `ownAtB` the clause on a link's own first messages as a test on a shape, its groups and a link's
                    number: over `ownOneB`
  `twoB_is` the test `twoB` on the links 1 to 23 is "no plain scalar" and `ownAtB`: by unfolding
  `ownAt_says` what its yes says, at the head's front
  `ownAtB_written` LEAN's KERNEL SAYS YES at the written shape at link 24 (`decide +kernel`)
  `ownAtB_one` there the link has one own message of moment 0: so the yes is not for nothing
                    (`decide +kernel`)
  `ownAtB_can_fail` CONTROLS: it says no at the written shape with its main code, or its mask's
                    code, raised by one (`decide +kernel`)
  `own_at_head` under the head, at a state reached at 339: the clause on the own messages, at the
                    fresh group's codes
  `head_seat_yes` THE TOP: the head · the opening ⊢ at `head_seat_decides`' own letters b, nm, HP,
                    Pp, n, its clauses beside (so that the name nm is pinned by the two-way clause):
                    for every s reached at 339, all r₁ r₂ gs, and the a, Q, c₀ that the state's
                    look-ups return: he · hrf · `HeadRest` ⊢ ∃ t, b.decide s [r₁, r₂] gs = ok t

By, this folder's: `head_seat_reached` (Returns/HeadAfter.lean) · `head_behind_returns`
(Returns/HeadBehindPaid.lean) · `head_behind_at_head`, `HeadRest` (Returns/HeadAtReached.lean) ·
`HeadBehind.plain` (Returns/ArmsBehind.lean), `head_returns_sent` (Returns/ArmsSent.lean) ·
`head_group` (Returns/ArmsBehind.lean), `behind_k7_reached` (Returns/ArmsReached.lean) ·
`tests_at_head` (Returns/UnderHead.lean). The library's: `place_rest`
(Johnson/Desc/Kinds/Law/ReplyRest.lean), `guarded_front` (Johnson/Top/H0/Tw/K2C/HeadFreshAt.lean) ·
`sw_head` (Johnson/P1K2R/HstReached.lean), `SwState` (Johnson/Top/H0/Tw/K2C/DebtsState.lean) ·
`written_of_head` (Johnson/Road/K4/K4HeadWritten.lean), `shape_one`
(Johnson/Road/K4/K4PlanTied.lean) · `freshGroup` (Johnson/Top/H0/Tw/K2C/FrontGroup.lean). NOT OURS,
LINED FOR A SEALED LIBRARY AND IN NONE YET, IMPORTED: `ownOneB`, `twoB`
(Johnson/AtFull/Shape/LinkLeftPlan.lean): the same clause at the links 1 to 23, as one test with "no
plain scalar", which fails at link 24 (that file's own control); `ownAt_says` GOES BY ITS
`two_says`' PROOF, at the head's front. NEAR RELATIVES, NOT CALLED: `code_reached`, `HeadCode`
(Returns/ArmsReached.lean, Returns/ArmsBehind.lean): the main code alone · `HeadFresh`
(Johnson/Top/H0/Tw/K2C/HandsEnds.lean), `headFresh_front`, `fresh_behind`
(Johnson/Top/H0/Tw/K2C/HeadFreshAt.lean): the group is there, with no rows, members or kept messages
and not in its test: no codes · `headFrontQ_groups` (Johnson/Top/H0/Tw/K2C/FrontGroup.lean): the
fresh group with both codes, at the groups' size · inside a proof in
Johnson/Top/H0/Tw/K2C/HandsEnds.lean the fresh group stands at the like term behind the finish's
quiet front.

Limits. he, hrf AND `HeadRest` ARE PREMISES ON THE TWO ROUNDS AND THE COLUMNS: NOBODY PAYS THEM HERE
(`headLast_of_seven`, `head_behind_seven` in Returns/ArmsProver.lean pay he and bring `HeadRest`
down to seven clauses, under `P5J.AtMgA`; files under Johnson/Desc/ProofFile/Honest/K2/ go on from
there: not joined here): SO THIS IS NOT "BEHIND EVERY YES". THE STATE's THREE LOOK-UPS (a, Q, c₀)
STAND AS PREMISES: where one failed the top would say nothing of that state; that they return at
every state reached at 339 has been typed elsewhere (`head_looks_reached`,
Johnson/AtFull/Shape/HeadLooksReached.lean, in no sealed library and on no line;
`code_look_reached`, Returns/ArmsPaid.lean): not imported. THE HEAD IS SHOWN MET BY NOBODY HERE;
that a state is reached is not said. THREE CLOSED FACTS BY LEAN's KERNEL, replayed by no independent
checker, under a raised recursion depth. At the decision, not at the step. 339 alone. "Reached" is:
over the list of the wrapped sub-protocols. The full size alone; the format's second hash function alone.
Over files of this folder, and one that is not ours, that are lined for a sealed library and not yet
in one. This file's imports are heavy. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.HeadBehindPaid
import Johnson.Desc.K2.Honest.Returns.HeadAtReached
import Johnson.Road.K4.K4HeadWritten
import Johnson.AtFull.Shape.LinkLeftPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes OnBytes.Model
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K2 (P2 decideWith rounds par9 flat headFrontOf freshGroup
  guarded_front HeadPar headOpenQ)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.AtFull.Shape (ownOneB twoB)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

/-- Behind a yes of the sub-protocol that enters the head's segment and hears the reply: the group
at the number in the head's own frame is the fresh one. -/
theorem headGroup_k7Block {X : Verify.Public} {l : Nat} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k7Block X l).decide s rs gs = .ok t) :
    ∀ a, t.here = .head a → t.st.groups[a.fr.group]? =
      some (freshGroup t.check.frame.shape.code t.check.frame.shape.maskCode) := by
  obtain ⟨s₀, h0, a1, -, -, -, -, a6, a7, -⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.place_rest X l "H:1" _ X.H.tl
      (fun _ _ _ _ e => guarded_front e) s rs gs t h
  intro a ha
  rw [a7] at ha
  rw [a1, a6]
  exact head_group h0 ha

/-- **The clause on a link's own messages of moment 0, as a test.** G: the shape's groups. -/
def ownAtB (sh : Params.ReqShape) (G : Array ReqGroup) (l : Nat) : Bool :=
  let f : ReqFrame := { shape := sh, groups := G, link := l }
  let own := f.atMoment 0
  let others := ReqFrame.notices own ++ #[foldMaskNotice (f.foldShape l {})]
  (List.range own.length).all fun j =>
    match own[j]?, others[j]? with
    | some m, some n => ownOneB sh m n
    | some _, none => false
    | none, _ => true

/-- The test on the links 1 to 23 is "no plain scalar" and this one. -/
theorem twoB_is (sh : Params.ReqShape) (G : Array ReqGroup) (l : Nat) :
    twoB sh G l = ((sh.link[l]?).all (fun L => L.plain == 0) && ownAtB sh G l) := rfl

/-- **What its yes says, at the head's front.** -/
theorem ownAt_says {s : S} (a : HeadOwn) (T : SwitchTarget)
    (h : ownAtB s.check.frame.shape s.check.frame.groups s.check.frame.link = true) :
    ∀ (j : Nat) (m : Params.ReqMessage), (headFrontOf s a T).own[j]? = some m →
      ∃ n, (headFrontOf s a T).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
        (n.shape.mainRows = 0 ∨ n.shape.code = s.check.frame.shape.code) ∧
        (n.shape.maskRows = 0 ∨ n.shape.maskCode = s.check.frame.shape.maskCode) ∧
        (0 < m.life → 0 < n.shape.mainRows) := by
  intro j m hm
  unfold ownAtB at h
  have hm' : (s.check.frame.atMoment 0)[j]? = some m := hm
  have hj : j < (s.check.frame.atMoment 0).length := (List.getElem?_eq_some_iff.1 hm').1
  have h3 := List.all_eq_true.1 h j (List.mem_range.2 hj)
  have h4 : (match (s.check.frame.atMoment 0)[j]?, (headFrontOf s a T).others[j]? with
      | some m, some n => ownOneB s.check.frame.shape m n
      | some _, none => false
      | none, _ => true) = true := h3
  rw [hm'] at h4
  cases hn : (headFrontOf s a T).others[j]? with
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

set_option maxRecDepth 1000000 in
/-- **Lean's kernel says yes at the written shape at link 24.** -/
theorem ownAtB_written :
    ownAtB proofSizedFull.request (reqGroups proofSizedFull.request) 24 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- There the link has one own message of moment 0. -/
theorem ownAtB_one :
    (({ shape := proofSizedFull.request, groups := reqGroups proofSizedFull.request,
        link := 24 } : ReqFrame).atMoment 0).length = 1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test can fail**: at the written shape with one of its two codes raised by one. -/
theorem ownAtB_can_fail :
    ownAtB { proofSizedFull.request with code := proofSizedFull.request.code + 1 }
        (reqGroups proofSizedFull.request) 24 = false ∧
      ownAtB { proofSizedFull.request with maskCode := proofSizedFull.request.maskCode + 1 }
        (reqGroups proofSizedFull.request) 24 = false := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}

/-- So at every state reached at 339. -/
theorem headGroup_reached (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s)) :
    ∀ a, s.here = .head a → s.st.groups[a.fr.group]? =
      some (freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode) :=
  behind_k7_reached (fun t => ∀ a, t.here = .head a → t.st.groups[a.fr.group]? =
      some (freshGroup t.check.frame.shape.code t.check.frame.shape.maskCode))
    (fun _ _ _ _ _ _ e => headGroup_k7Block e) h.scope h.reads O s (reach_raw hr)

/-- **The clause on the own messages, under the head, at a state reached at 339.** -/
theorem own_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s)) (a : HeadOwn)
    (T : SwitchTarget) :
    ∀ (j : Nat) (m : Params.ReqMessage), (headFrontOf s a T).own[j]? = some m →
      ∃ k, (headFrontOf s a T).others[j]? = some k ∧ k.shape.answers ≠ 0 ∧
        (k.shape.mainRows = 0 ∨ k.shape.code = s.check.frame.shape.code) ∧
        (k.shape.maskRows = 0 ∨ k.shape.maskCode = s.check.frame.shape.maskCode) ∧
        (0 < m.life → 0 < k.shape.mainRows) := by
  have Q := (P1K2.sw_head h.scope h.reads O h.laid.value h.laid.planOk default "" hP hn hr).1
  have Wr := OnBytes.Road.K4.written_of_head h
  have esh : s.check.frame.shape = proofSizedFull.request :=
    Q.shape.trans (Wr.shape.trans OnBytes.Road.K4.shape_one)
  refine ownAt_says a T ?_
  rw [Q.groups, Q.link, esh]
  exact ownAtB_written

/-- **At a reached state the seated decision says yes, at rounds and columns at which this folder's
law gives the kind's own yes.** -/
theorem head_seat_yes (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∃ (b : Block S Cl) (nm : String) (HP : HeadPar) (Pp : Prep) (n : Nums),
      cF.blocksInOrder[339]? = some b ∧ P1K2.pureLetters Bs.G₀ 24 = some HP ∧
      prepOf Zp Bs.G₀ = some Pp ∧ numsAt Pp (some 24) = some n ∧
      (∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), rs.length = 2 →
        gs.length = n.read.length →
        (b.decide s rs gs = .ok t ↔ ∃ u,
          decideWith sendByL8 (k2P Zp headPlaceAt nm .head n) s rs gs = .ok u ∧
            (headOpenQ HP u).bind (P1K2.guards s) = .ok t)) ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s) →
        ∀ (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (a : HeadOwn) (Q : ReqGroup)
          (c₀ : Code), s.here = .head a →
          s.check.frame.groups[s.check.frame.link]? = some Q →
          s.st.codes.base[s.check.frame.shape.code]? = some c₀ →
          planOk1 none n.sent (par9 (k2P Zp headPlaceAt nm .head n)).eSeed = true →
          roundsFit (rounds (k2P Zp headPlaceAt nm .head n)) [r₁, r₂] = true →
          HeadRest (k2P Zp headPlaceAt nm .head n) s r₁ r₂ gs a Q c₀ →
          ∃ t, b.decide s [r₁, r₂] gs = .ok t := by
  obtain ⟨-, hcut, -⟩ := tests_at_head h O
  obtain ⟨b, nm, HP, Pp, n, hb, hHP, hP, hn, hd, hseat⟩ :=
    head_seat_reached h.scope h.reads O h.laid.value h.laid.planOk hcut
  refine ⟨b, nm, HP, Pp, n, hb, hHP, hP, hn, hd,
    fun z s hr r₁ r₂ gs a Q c₀ here group hc he hrf E => ?_⟩
  have HB := head_behind_at_head h O hP hn hr headPlaceAt nm r₁ r₂ gs he hrf here group hc E
  obtain ⟨G, HPl⟩ := HB.plain
  obtain ⟨u, hu⟩ := head_returns_sent HPl
  have eG : G = freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode :=
    Option.some.inj (HPl.call.front.group.symm.trans (headGroup_reached h O hr a here))
  have hB : BehindReturns u := by
    refine head_behind_returns HPl ?_ hu
    rw [eG]
    exact own_at_head h O hP hn hr a Q.target
  exact hseat z s hr [r₁, r₂] gs u rfl HPl.groups hu hB

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.headGroup_k7Block
#print axioms VerifiableInference.Desc.K2.Honest.Returns.headGroup_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.twoB_is
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ownAt_says
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ownAtB_written
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ownAtB_one
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ownAtB_can_fail
#print axioms VerifiableInference.Desc.K2.Honest.Returns.own_at_head
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_seat_yes
