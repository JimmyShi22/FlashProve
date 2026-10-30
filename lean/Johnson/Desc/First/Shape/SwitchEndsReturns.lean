-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchEndsReturns.lean: THE QUIET STEPS AROUND THE CODE SWITCH AT THE
HEAD's LINK AND AT THE FINISH (kind K2: the second half of "H:2"; the first and the last third of
"F:1"): "RETURNS" ON THE FIRST CHAIN's SHAPE WITH THE ROWS' MAKES BESIDE IT. General laws; nothing
is evaluated. It is the way back to Johnson/Desc/First/Shape/SwitchEnds.lean, which has the updates
as code and "carries" from a yes.

The question. Each update of SwitchEnds.lean asks fewer tests than its text. What must be asked
besides, so that the text returns where the update does? THE FINDING, step by step:
* K2.finishBehindQ: NOTHING: it returns wherever `finBehindU` does.
* K2.finishFrontQ: FIVE CLAUSES ON THE SHAPE (`finFrontB`): no mark; the chain stands between two
  links; it is in no link; every link is behind; the frame's next call is a first one. No test on a
  value.
* K2.headOpenQ: SEVEN CLAUSES ON THE PLAN AND THE SHAPE (`headQuietB`): no mark; it is not link 0; a
  reply lies in the seat; the record is of the head's kind; the chain stands in the head's link; as
  many numbers came back as there were announcements; the walk stands at the record's link. AND
  THREE TESTS THAT READ THE STATE ITSELF (`headQuietV`): the reply is an entry of the vocabulary;
  the covered positions can be made of the request's words; their four arrays have the length T
  (this last one reads sizes, no value).

Main names.
* `joinG_returns_sh`, `joins_returns_sh`, `newGroupG_returns_sh`: a joining, several in a row, a new
  group: where the routine on shapes returns, the routine returns. By `join_returns` and
  `newGroup_returns` (Johnson/Desc/Ground/Shape/Ground.lean): the routines on shapes ask the
  routines' whole guards; and, from one joining to the next, by `joinG_sh`
  (Johnson/Desc/First/Shape/Switch.lean).
* `firstBehind_returns_sh`: Tw.K2.firstBehind returns where `firstBehindU` does and as many numbers
  came back as there were announcements.
* `between_of_no`, `failed_of_no`: two readings of the shape.
* `finFrontB`, `finFront_returns`; `finBehind_returns`; `headQuietB`, `headQuietV`,
  `headOpen_returns`: as above.

How. The library's closed forms of a yes, read from right to left: `finishFrontQ_iff`,
`finishBehindQ_iff`, `headOpenQ_iff`, `firstBehind_iff`, `finishFront_iff`
(Johnson/Top/H0/Tw/K2C/Asks.lean).

Limits. ONE WAY: the tests and the update's return give the text's return. NO STATE IS SHOWN AT
WHICH THE TESTS ACCEPT OR THE UPDATES RETURN. The steps alone: they are not joined to the places'
blocks here, and the switch that stands between them is not here. No member of the proof file's list
is named. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.SwitchEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Ground.Sh (StSh CoreSh stSh shD joinS newGroupS)
open VerifiableInference.Desc.First.K2 (HeadPar headOpenQ finishFrontQ finishBehindQ sizedOk)
open OnBytes.Params (ReqMessage)
open Johnson.Desc.First.Walk (firstKept finishDue)
open _root_.Tw.K2 (dOf joinG newGroupG Front firstBehind finishFront)

/-! ## 1 Joinings and a new group: where the routine on shapes returns, the routine returns -/

/-- One joining. -/
theorem joinG_returns_sh {S : Statement} {g o : Nat} {kept : Bool} {y : StSh}
    (h : onSt (joinS · g o kept) (stSh S) = some y) : ∃ S', joinG S g o kept = .ok S' := by
  unfold onSt at h
  obtain ⟨c, hc, -⟩ := Option.map_eq_some_iff.1 h
  have hc' : joinS (shD (dOf S)) g o kept = some c := hc
  obtain ⟨d', hd⟩ := Ground.Sh.join_returns (dOf S) g o kept c hc'
  unfold joinG
  rw [hd]
  exact ⟨_, rfl⟩

/-- Several joinings in a row. -/
theorem joins_returns_sh {ι : Type} (g : Nat) (who : ι → Nat) (kept : ι → Bool) :
    ∀ (l : List ι) (S : Statement) (y : StSh), joinsSt g who kept l (stSh S) = some y →
      ∃ S', l.foldlM (fun S p => joinG S g (who p) (kept p)) S = .ok S'
  | [], S, _, _ => ⟨S, rfl⟩
  | p :: l, S, y, h => by
    unfold joinsSt at h
    rw [List.foldlM_cons] at h
    obtain ⟨a1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨S1, e1⟩ := joinG_returns_sh h1
    obtain rfl : a1 = stSh S1 := Option.some.inj (h1.symm.trans (joinG_sh e1).1)
    obtain ⟨S', e2⟩ := joins_returns_sh g who kept l S1 y h2
    refine ⟨S', ?_⟩
    rw [List.foldlM_cons, e1]
    exact e2

/-- A new group. -/
theorem newGroupG_returns_sh {S : Statement} {code maskCode : Nat} {y : StSh × Nat}
    (h : newGroupSt (stSh S) code maskCode = some y) :
    ∃ S' g, newGroupG S code maskCode = .ok (S', g) := by
  unfold newGroupSt at h
  obtain ⟨c, hc, -⟩ := Option.map_eq_some_iff.1 h
  have hc' : newGroupS (shD (dOf S)) code maskCode = some c := hc
  obtain ⟨⟨n, d⟩, hd⟩ := Ground.Sh.newGroup_returns (dOf S) code maskCode c hc'
  unfold newGroupG
  rw [hd]
  exact ⟨_, _, rfl⟩

/-! ## 2 What stands behind a switch at a link -/

/-- **Tw.K2.firstBehind returns where its update on shapes does**, and as many numbers came back as
there were announcements (the one test that the update does not ask). -/
theorem firstBehind_returns_sh {S : Statement} {x : Front} {sw : Switched} {plain : List E}
    {y : StSh × FrameSh × Array Nat} (hn : sw.others.size = x.others.size)
    (h : firstBehindU (stSh S) (frameSh x.f) x.own sw.kept sw.others plain.length = some y) :
    ∃ S' f mine, firstBehind S x sw plain = .ok (S', f, mine) := by
  unfold firstBehindU at h
  obtain ⟨mask, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨s5, hj, -⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨S', hS⟩ := joins_returns_sh _ _ _ _ S s5 hj
  have hlt : x.own.length < sw.others.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at hm
    cases hm
  refine ⟨S', _, _, (_root_.Tw.K2.firstBehind_iff S x sw plain _ _ _).2
    ⟨mask, ⟨hn, hm, rfl, ?_, hS, rfl⟩⟩⟩
  rw [Array.size_extract]
  omega

/-! ## 3 The finish ("F:1"): the two quiet steps -/

/-- **What K2.finishFrontQ asks of the shape beyond its update**: no mark; the chain stands between
two links; it is in no link, and every link is behind; the frame's next call is a first one. -/
def finFrontB (x : ChainF) : Bool :=
  !x.1.marked && x.1.here == 0 && !x.1.check.inLink &&
    x.1.check.frame.link == x.1.check.frame.shape.link.length &&
    decide (x.1.check.frame.next = .first)

/-- The chain stands between two links. -/
theorem between_of_no {s : S} (h : ((chainF s).1.here == 0) = true) : s.here = .between := by
  have h0 : hereNo s.here = 0 := beq_iff_eq.1 h
  cases hh : s.here with
  | between => rfl
  | lay a => rw [hh] at h0; cases h0
  | att a => rw [hh] at h0; cases h0
  | head a =>
    rw [hh] at h0
    cases ho : a.opened <;> simp [hereNo, ho] at h0
  | fin a => rw [hh] at h0; cases h0
  | mem a => rw [hh] at h0; cases h0

/-- No mark. -/
theorem failed_of_no {s : S} (h : (!(chainF s).1.marked) = true) : s.failed = none := by
  have h' : (!s.failed.isSome) = true := h
  cases e : s.failed with
  | none => rfl
  | some m => rw [e] at h'; cases h'

/-- **THE QUIET STEP IN FRONT OF THE FINISH's SWITCH RETURNS.** -/
theorem finFront_returns {s : S} {y : ChainF} (hB : finFrontB (chainF s) = true)
    (hU : finFrontU (chainF s) = some y) : ∃ s', finishFrontQ s = .ok s' := by
  unfold finFrontB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩ := hB
  have hb := between_of_no b2
  have hf := failed_of_no b1
  unfold finFrontU at hU
  dsimp only at hU
  obtain ⟨G, hG, hU⟩ := Option.bind_eq_some_iff.1 hU
  obtain ⟨n, hn, -⟩ := Option.map_eq_some_iff.1 hU
  have hn' : newGroupSt (stSh s.st) s.check.frame.shape.code s.check.frame.shape.maskCode =
    some n := hn
  obtain ⟨S', g, hN⟩ := newGroupG_returns_sh hn'
  have hG' : s.check.frame.groups[s.check.frame.link]? = some G := hG
  have hl : s.check.frame.link = s.check.frame.shape.link.length := beq_iff_eq.1 b4
  have hat : s.atBetween = true := by
    unfold S.atBetween
    rw [hb]
  have hdue : finishDue s.check = true := by
    unfold finishDue
    have b3' : (!s.check.inLink) = true := b3
    rw [b3', Bool.true_and]
    exact b4
  have he : s.enterFin? = .ok { s with here := .fin { fr := s.check.frame, sw := default
                                                      row := default, L := default, mask := none
                                                      st := default } } := by
    unfold S.enterFin? S.enterFin
    rw [if_pos hat]
    exact (S.unmarked_ok _ _).2 ⟨rfl, hf⟩
  exact ⟨_, (First.K2.finishFrontQ_iff s _).2 ⟨G, _, _, _,
    ⟨hat, hdue, hG', (_root_.Tw.K2.finishFront_iff _ _ _).2 ⟨G, S', g, ⟨b5, hl, hG', hN, rfl⟩⟩,
      he, rfl, rfl⟩⟩⟩

/-- **THE QUIET STEP BEHIND THE FINISH's SWITCH RETURNS WHERE ITS UPDATE DOES.** -/
theorem finBehind_returns {s : S} {y : ChainF} (hU : finBehindU (chainF s) = some y) :
    ∃ s', finishBehindQ s = .ok s' := by
  unfold finBehindU at hU
  obtain ⟨a, ha, hU⟩ := Option.bind_eq_some_iff.1 hU
  obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.1 hU
  have ha' : finOf s.here = some a := ha
  cases hh : s.here with
  | fin a₀ =>
    rw [hh] at ha'
    obtain rfl : finSh a₀ = a := Option.some.inj ha'
    exact ⟨_, (First.K2.finishBehindQ_iff s _).2 ⟨a₀, m, hh, hm, rfl⟩⟩
  | between => rw [hh] at ha'; cases ha'
  | lay _ => rw [hh] at ha'; cases ha'
  | att _ => rw [hh] at ha'; cases ha'
  | head _ => rw [hh] at ha'; cases ha'
  | mem _ => rw [hh] at ha'; cases ha'

/-! ## 4 The quiet step behind the head's switch (the second half of "H:2") -/

/-- **What K2.headOpenQ asks of the plan and the shape beyond its update**: no mark; it is not link
0; a reply lies in the seat; the record is of the head's kind; the chain stands in the head's link;
as many numbers came back as there were announcements; the walk stands at the record's link. -/
def headQuietB (P : HeadPar) (x : ChainF) : Bool :=
  !x.1.marked && P.l != 0 && x.1.reply && P.X.kind == 2 &&
    (x.1.head).any fun hd =>
      hd.ids.size == (x.1.check.frame.blank.atMoment 0).length + 1 && hd.fr.link == P.l

/-- **What K2.headOpenQ asks of the state itself**: the reply is an entry of the vocabulary; the
covered positions can be made of the request's words, and their four arrays have the length T. -/
def headQuietV (P : HeadPar) (s : S) : Bool :=
  (s.out.reply.all fun y => y.c1 == 0 && y.c2 == 0 && decide (y.c0.toNat < P.V)) &&
    match s.covered P.T P.V with
    | .ok cov => sizedOk cov P.T
    | .error _ => false

/-- **THE QUIET STEP BEHIND THE HEAD's SWITCH RETURNS.** -/
theorem headOpen_returns {P : HeadPar} {s : S} {y : ChainF} (hB : headQuietB P (chainF s) = true)
    (hV : headQuietV P s = true) (hU : headOpenU P (chainF s) = some y) :
    ∃ s', headOpenQ P s = .ok s' := by
  unfold headOpenU at hU
  obtain ⟨hd, hhd, hU⟩ := Option.bind_eq_some_iff.1 hU
  obtain ⟨sh, hsh, hU⟩ := Option.bind_eq_some_iff.1 hU
  obtain ⟨yy, hyy, -⟩ := Option.map_eq_some_iff.1 hU
  unfold headQuietB at hB
  rw [hhd] at hB
  simp only [Bool.and_eq_true, Option.any_some, bne_iff_ne, beq_iff_eq] at hB
  obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5, b6⟩ := hB
  have hf := failed_of_no b1
  have hhd' : headOf s.here = some hd := hhd
  cases hh : s.here with
  | head a =>
    rw [hh] at hhd'
    obtain rfl : headSh a = hd := Option.some.inj hhd'
    have hfresh : a.opened = false := by
      cases ho : a.opened with
      | false => rfl
      | true =>
        have : (headSh a).shut = none := by
          unfold headSh
          simp [ho]
        rw [this] at hsh
        cases hsh
    have b3' : s.out.reply.isSome = true := b3
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 b3'
    have hlen : s.out.reply.toList.length = if (chainF s).1.reply then 1 else 0 := by
      show _ = if s.out.reply.isSome then 1 else 0
      rw [hr]
      rfl
    have hyy' : firstBehindU (stSh s.st) (frameSh a.fr) (s.check.frame.atMoment 0) a.kept a.ids
        s.out.reply.toList.length = some yy := by
      rw [hlen]
      exact hyy
    have b5' : a.ids.size = (s.check.frame.atMoment 0).length + 1 := b5
    obtain ⟨st, f, mine, hb⟩ := firstBehind_returns_sh (S := s.st)
      (x := ⟨s.st, a.fr, s.check.frame.atMoment 0,
        ReqFrame.notices (s.check.frame.atMoment 0) ++
          #[foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})], default, 0⟩)
      (sw := { (default : Switched) with kept := a.kept, others := a.ids })
      (plain := s.out.reply.toList)
      (by
        show a.ids.size = _
        rw [b5']
        simp [ReqFrame.notices])
      hyy'
    obtain ⟨mask, A⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 hb
    have hfr : Johnson.Desc.First.Walk.front P.X P.l (firstKept s.check f mine) s.out =
        .ok ({ check := firstKept s.check f mine, link := P.l, arrayOf := P.X.arrayOf
               list := P.X.Tp }, s.out) := by
      have e1 : (firstKept s.check f mine).frame.plain.length = 1 := by
        show f.plain.length = 1
        rw [A.frame]
        show s.out.reply.toList.length = 1
        rw [hr]
        rfl
      have e2 : (firstKept s.check f mine).frame.link = P.l := by
        show f.link = P.l
        rw [A.frame]
        exact b6
      unfold Johnson.Desc.First.Walk.front
      simp [e1, e2, b4]
    unfold headQuietV at hV
    rw [Bool.and_eq_true, hr] at hV
    obtain ⟨v1, v2⟩ := hV
    simp only [Option.all_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at v1
    cases hc : s.covered P.T P.V with
    | error e => rw [hc] at v2; cases v2
    | ok cov =>
      rw [hc] at v2
      have ho : s.openHead? = .ok { s with here := .head { a with
          opened := true, L := { a.L with check := s.check } } } := by
        unfold S.openHead? S.openHead
        rw [hh]
        simp only [hfresh, Bool.false_eq_true, if_false]
        exact (S.unmarked_ok _ _).2 ⟨rfl, hf⟩
      exact ⟨_, (First.K2.headOpenQ_iff P s _).2 ⟨a, st, f, mine, _, _, r, cov, _, _,
        ⟨hh, hfresh, b2, hb, hfr, hr, ⟨v1.1.1, v1.1.2, v1.2⟩, hc, v2, ho, rfl, rfl⟩⟩⟩
  | between => rw [hh] at hhd'; cases hhd'
  | lay _ => rw [hh] at hhd'; cases hhd'
  | att _ => rw [hh] at hhd'; cases hhd'
  | fin _ => rw [hh] at hhd'; cases hhd'
  | mem _ => rw [hh] at hhd'; cases hhd'

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.headOpen_returns
#print axioms VerifiableInference.Desc.First.Shape.joinG_returns_sh
#print axioms VerifiableInference.Desc.First.Shape.joins_returns_sh
#print axioms VerifiableInference.Desc.First.Shape.newGroupG_returns_sh
#print axioms VerifiableInference.Desc.First.Shape.firstBehind_returns_sh
#print axioms VerifiableInference.Desc.First.Shape.between_of_no
#print axioms VerifiableInference.Desc.First.Shape.failed_of_no
#print axioms VerifiableInference.Desc.First.Shape.finFront_returns
#print axioms VerifiableInference.Desc.First.Shape.finBehind_returns
