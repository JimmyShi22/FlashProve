-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/LinkReached.lean: AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH
INTO A LATER GROUP, IN THE GOALS' SCOPE, THIRTEEN CLAUSES OF THE LAW "THE KIND's OWN DECISION SAYS
YES AT A SEGMENT's FIRST PLACE" (`LinkPlain`, Returns/LinkSent.lean) HOLD: THE LIBRARY PAYS THEM. SO
THE TEXT's OWN FRONT RETURNS THERE UNDER ONE PREMISE MORE (paid in Returns/FirstReached.lean). And:
in front of the output head's switch the state stands in the head's segment. Statements with their
proofs: calls, one proof of the library's typed again with one clause more, one small lemma.

  `laid_three` behind the step "laid", at each of the 25 segments, at the fold's return: the state
                    stands between the segments · A FIRST CALL IS DUE · the frame stands at that
                    segment. THE LIBRARY's `laid_at` (Johnson/IMR/FrontPin.lean) HAS THE FIRST AND
                    THE THIRD; ITS PROOF DRAWS ALL THREE FROM `layFront_ok`
                    (Johnson/Top/H0/Walk/FrameLaw.lean) AND DROPS THE SECOND: THAT PROOF IS TYPED
                    AGAIN HERE, LINE FOR LINE, WITH THE SECOND KEPT; at the first segment alone the
                    library has all three (`behind_laid`, Johnson/IMR/ListsEnds.lean)
  `codes_of_reqOk` the public test on a request's shape and the codes says yes only where the
                    shape's two codes are in the list: by unfolding
  `link_walk_reached` the three of `laid_three` at a reached state
  `link_fields_reached` THE THIRTEEN, each in its structure's own letters, at the plan's own
                    numbers: here · due · later · link · group · code · maskCode · shorter · number
                    · step · oldCode (`LinkPlain`) · masks (`ReadFits`) · keptPos (`FrontCore`)
  `link_front_reached` so the text's front returns there, if the frame's next call is a first one:
                    of the seven premises of `firstFront_returns` (Returns/Front.lean) six are paid
  `link_draws_first` and with rounds that fit, and the first entry's test AT THE PLAN's OWN LIST OF
                    ANNOUNCED MESSAGES (no front, no state: a sentence on the plan alone): the
                    text's front returns, and the five on the draws hold at it
                    (`link_draws_reached`, Returns/DrawReached.lean)
  `head_draws_plan`, `finish_draws_plan` `head_draws_reached` and `finish_draws_reached` with the
                    entry's test at the plan's own list likewise
  `head_here_reached` in front of the output head's switch (number 339): the state stands in the
                    head's segment

By, all the library's: `reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean) · `sw_link`
(Johnson/P1K2R/HstReached.lean: the frame's shape, groups and segment; the codes) ·
`recAll_reached`, `bookHas_reached` (Johnson/IMR/AtReach.lean) · `front_len`
(Johnson/IMR/FinPin.lean) · `rows_of_pub` (Johnson/IMR/FrontPin.lean) · `count_at`
(Johnson/IMR/GroupCount.lean) · `numsAt_grp` (Johnson/Top/H0/Tw/K2C/GroupAtNums.lean) ·
`reqGroups_size` (Johnson/IMR/MsgsPlaces.lean) · `mask_le_main`
(Johnson/Goal/Meaning/MaskShort.lean) · `kept_pos_ok` (Johnson/Goal/Meaning/KeptRowsPos.lean) ·
`sw_head`, `sw_finish` · `frame_of` (Johnson/IMR/FrameSeat.lean) · `fold_back`, `fold_next`
(Johnson/IMR/FoldTools.lean) · `unheard_reached` (Johnson/Top/H0/Tw/K2C/HeadUnheardReached.lean); a
second payer of its end, not called: `h1_headFr` (Johnson/IMR/ListsEnds.lean).

Limits. "REACHED" IS: OVER THE LIST OF THE WRAPPED SUB-PROTOCOLS, from the description's own start.
THIRTEEN OF 67: `LinkPlain` HAS 32 FIELDS; WITH `reads` (13 clauses) AND `front` (13, of which
`fits` holds 8 and `tables` 5) LAID OPEN: 67 CLAUSES. THE OTHER 54 ARE NOT PAID HERE; SORTED BY WHAT
EACH READS (a sorting by reading, shown by no statement): 5 on the draws: Returns/DrawReached.lean ·
7 on the two rounds and the columns (fits₁ · vals · answers · loc · noneLeft · groups · reads.opens)
· 14 that read the plan's numbers, the target, the segment's messages or the codes alone (stands ·
plain · entry · plan · trees · own · front's restMain · keptAnswers · lengths · logC · logZ ·
groupCode · copiesCode · tables.bitsG) · 2 on the walk (the frame's next call is a first one · no
count of rows waits): Returns/FirstReached.lean, Returns/WaitsReached.lean · 3 on the kept members'
stored sample rows: Returns/StoredReached.lean, Returns/StoredTables.lean · 17 on the shape of what
the last closing left in the carried rows (eight of `reads`; seven of `fits`; the test on the
target; tables.bitsKept): eight of the 17, under three named tests on the public part:
Returns/PinReached.lean · AND, WITH NO PAYER AT A REACHED STATE THAT IS KNOWN HERE: 3 on the book
(reads' placed · stated · own) · 2 on the carried claim and the kept forms, which compare field
elements with (1, 1) · 1 on the positions read (front.inRange). THE ENTRY's TEST AT THE PLAN's LIST
STAYS A PREMISE: its one clause that is not by unfolding says that the number of samples is the
greatest count of answers among the announced messages. THE FIVE PREMISES IN FRONT ARE SHOWN MET
TOGETHER BY NOBODY HERE: NO MEMBER. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.DrawReached
import Johnson.IMR.FrontPin
import Johnson.IMR.GroupCount
import Johnson.IMR.AtReach
import Johnson.IMR.FinPin
import Johnson.IMR.MsgsPlaces
import Johnson.Goal.Meaning.MaskShort
import Johnson.Goal.Meaning.KeptRowsPos
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.Top.H0.Tw.K2C.HeadUnheardReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit foldBlocks Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds par9 unheard_reached finishFrontQ)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk (firstDue)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P1K2 (Prep Nums numsAt prepOf sw_link sw_head sw_finish numsAt_grp)
open IM (k2P)
open _root_.Tw.K2 (Front Col Sent switchNotices firstFront)
open ProofFile (Cl)

theorem codes_of_reqOk {codes : Codes} {s : Params.ReqShape} (h : reqOk codes s = true) :
    ∃ c zk, codes.base[s.code]? = some c ∧ codes.mask[s.maskCode]? = some zk := by
  unfold reqOk at h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  split at h2
  · rename_i c zk hc hz
    exact ⟨c, zk, hc, hz⟩
  · cases h2

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **Behind "laid", at each of the 25 segments**: the library's `laid_at`, with "a first call is
due" kept. -/
theorem laid_three (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.atBetween = true ∧ firstDue t₀.check = true ∧ t₀.check.frame.link = l := by
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨LkF, f, bL, bB, bC, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr l hl
  obtain ⟨tm, Rm, Cm, fm⟩ := Meaning.K2.fold_back (k := 14 * l + 1) f₀
  obtain ⟨rsL, gsL, dl⟩ := Meaning.K2.fold_next iL fm f₀
  rw [dL] at dl
  have hlf := ((hlay tm t₀).1 dl).1
  rw [efl] at hlf
  obtain ⟨et, hBm, hd, hk⟩ := Johnson.Desc.First.Walk.Law.layFront_ok hlf
  rw [et]
  exact ⟨hBm, hd, hk⟩

theorem link_walk_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s)) :
    s.here = .between ∧ firstDue s.check = true ∧ s.check.frame.link = l := by
  obtain ⟨-, rs, cols, hf⟩ := (reach_raw hr).fold
  obtain ⟨hB, hd, hk⟩ := laid_three hS hR O hl hf
  refine ⟨?_, hd, hk⟩
  unfold S.atBetween at hB
  split at hB
  · assumption
  · cases hB

/-- **The thirteen.** -/
theorem link_fields_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) :
    ∃ (L : Params.ReqLink) (Q : ReqGroup) (c₀ z₀ : Code),
      s.here = .between ∧ firstDue s.check = true ∧ s.check.frame.link ≠ 0 ∧
      s.check.frame.shape.link[s.check.frame.link]? = some L ∧
      s.check.frame.groups[s.check.frame.link]? = some Q ∧
      s.st.codes.base[s.check.frame.shape.code]? = some c₀ ∧
      s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀ ∧ z₀.logN ≤ c₀.logN ∧
      s.st.groups.size = (k2P Z a nm .link n).grp ∧
      (frontAt s L Q).st.oracles.size = s.book.place.size ∧
      (frontAt s L Q).st.codes.base[(frontAt s L Q).f.rows.code]? = some c₀ ∧
      (∀ (y : Sent) (r₂ : Fmt.RoundView) (cols : List OpenedColumn),
        (inFront (par9 (k2P Z a nm .link n)) (frontAt s L Q) s.book y r₂ cols).old.masks = 2) ∧
      ∀ k ∈ (frontAt s L Q).T.kept.toList, 0 < k.shape.mainRows := by
  obtain ⟨hh, hd, hk⟩ := link_walk_reached hS hR O (l := m + 1) (by omega) hr
  obtain ⟨Q0, -⟩ := sw_link hS hR O hF hpl h23 hP hn hr
  have hraw := reach_raw hr
  have hlen : 14 * (m + 1) + 2 ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.K2.front_len hS hR O]
    omega
  have RA := Meaning.K2.recAll_reached hS hR O hraw (by omega) hlen
  have hlt : s.check.frame.link < s.check.frame.shape.link.length := by
    unfold firstDue at hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    exact hd.2
  have hgs : s.check.frame.link < s.check.frame.groups.size := by
    rw [Q0.groups, Meaning.Carry.reqGroups_size]
    omega
  have hL : s.check.frame.shape.link[s.check.frame.link]? =
      some s.check.frame.shape.link[s.check.frame.link] := List.getElem?_eq_getElem hlt
  have hQ : s.check.frame.groups[s.check.frame.link]? =
      some s.check.frame.groups[s.check.frame.link] := Array.getElem?_eq_getElem hgs
  have hok : reqOk s.st.codes s.check.frame.shape = true := by
    rw [RA.codes, Q0.shape]
    exact RA.ok
  obtain ⟨c₀, z₀, hc, hz⟩ := codes_of_reqOk hok
  obtain ⟨-, rs, cols, hf⟩ := hraw.fold
  have hcnt := Meaning.K2.count_at hS hR O (m + 1) (by omega) s [] [] hf
  have hgrp : n.grp = m + 1 := by
    rw [numsAt_grp hn]
    rfl
  have hne : s.check.frame.link ≠ 0 := by
    rw [hk]
    omega
  obtain ⟨r1, -, r3⟩ := Meaning.K2.rows_of_pub RA.walk hne
  have hkp := Meaning.K2.kept_pos_ok hok (l := s.check.frame.link)
    (G := s.check.frame.groups[s.check.frame.link]) (by rw [← Q0.groups]; exact hQ)
  refine ⟨_, _, c₀, z₀, hh, hd, hne, hL, hQ, hc, hz, Meaning.K2.mask_le_main hok hc hz, ?_,
    (Meaning.K2.bookHas_reached O hraw hlen).symm, ?_, fun _ _ _ => r3, ?_⟩
  · show s.st.groups.size = n.grp
    rw [hcnt, hgrp]
  · show s.st.codes.base[s.check.frame.rows.code]? = some c₀
    rw [r1, ← Q0.shape]
    exact hc
  · intro k hk'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk'
    have hi' : i < (s.check.frame.groups[s.check.frame.link]).target.kept.size := by
      simpa using hi
    simpa using hkp i hi'

/-- **So the text's front returns there**, if the frame's next call is a first one. -/
theorem link_front_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (first : s.check.frame.next = .first) :
    ∃ L Q, firstFront s.st s.check.frame = .ok (frontAt s L Q) := by
  obtain ⟨L, Q, c₀, z₀, -, -, h0, h2, h3, hc, hz, hle, -⟩ :=
    link_fields_reached hS hR O hF hpl h23 hP hn hr default ""
  exact ⟨L, Q, firstFront_returns s.st s.check.frame L Q c₀ z₀ first h0 h2 h3 hc hz hle⟩

/-- **And the five on the draws**, the entry's test being asked AT THE PLAN's OWN LIST: no front, no
state. -/
theorem link_draws_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (first : s.check.frame.next = .first) (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (he : planOk1 none n.sent (par9 (k2P Z a nm .link n)).eSeed = true)
    (h : roundsFit (rounds (k2P Z a nm .link n)) [r₁, r₂] = true) :
    ∃ x, firstFront s.st s.check.frame = .ok x ∧
      (∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a nm .link n).logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length = (sendingAt (k2P Z a nm .link n) x).seeds *
        ((sendingAt (k2P Z a nm .link n) x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ w ∈ K1.seedsOf (sendingAt (k2P Z a nm .link n) x) r₁, isZeroE w.2 = false := by
  obtain ⟨L, Q, hx⟩ := link_front_reached hS hR O hF hpl h23 hP hn hr first
  have hN := (sw_link hS hR O hF hpl h23 hP hn hr).2 _ hx
  exact ⟨_, hx, link_draws_reached hS hR O hF hpl h23 hP hn hr a nm hx r₁ r₂
    (by rw [hN]; exact he) h⟩

/-- The like in front of the output head's switch. -/
theorem head_draws_plan (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a : Place) (nm : String) {x : Front}
    (hx : VerifiableInference.Desc.First.K2.frontAt (k2P Z a nm .head n) s = some x)
    (r₁ r₂ : Fmt.RoundView) (he : planOk1 none n.sent (par9 (k2P Z a nm .head n)).eSeed = true)
    (h : roundsFit (rounds (k2P Z a nm .head n)) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a nm .head n).logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length = (sendingAt (k2P Z a nm .head n) x).seeds *
        ((sendingAt (k2P Z a nm .head n) x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ w ∈ K1.seedsOf (sendingAt (k2P Z a nm .head n) x) r₁, isZeroE w.2 = false := by
  have hN := (sw_head hS hR O hF hpl a nm hP hn hr).2 _ hx
  exact head_draws_reached hS hR O hF hpl hP hn hr a nm hx r₁ r₂ (by rw [hN]; exact he) h

/-- The like at the finish. -/
theorem finish_draws_plan (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (hq : finishFrontQ s = .ok t)
    (a : Place) (nm : String) {x : Front}
    (hx : VerifiableInference.Desc.First.K2.frontAt (k2P Z a nm .finish n) t = some x)
    (r₁ r₂ : Fmt.RoundView) (he : planOk1 none n.sent (par9 (k2P Z a nm .finish n)).eSeed = true)
    (h : roundsFit (rounds (k2P Z a nm .finish n)) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a nm .finish n).logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length = (sendingAt (k2P Z a nm .finish n) x).seeds *
        ((sendingAt (k2P Z a nm .finish n) x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ w ∈ K1.seedsOf (sendingAt (k2P Z a nm .finish n) x) r₁, isZeroE w.2 = false := by
  have hN := (sw_finish hS hR O hF hpl h25 a nm hP hn hr hq).2 _ hx
  exact finish_draws_reached hS hR O hF hpl h25 hP hn hr hq a nm hx r₁ r₂
    (by rw [hN]; exact he) h

/-- **In front of the output head's switch the state stands in the head's segment.** -/
theorem head_here_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) : ∃ a, s.here = .head a := by
  obtain ⟨a, ha, -⟩ := unheard_reached hS hR O s (reach_raw hr)
  exact ⟨a, ha⟩

end

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.codes_of_reqOk
#print axioms VerifiableInference.Desc.K2.Honest.Returns.laid_three
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_walk_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_fields_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_front_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_draws_first
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_draws_plan
#print axioms VerifiableInference.Desc.K2.Honest.Returns.finish_draws_plan
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_here_reached
