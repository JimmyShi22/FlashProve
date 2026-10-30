-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchDoor.lean: the closing of a segment (K10): at the state behind an accepted
closing the way into the next code switch (`doorZ`, Johnson/Top/H0/K2Caller/CarryClosed.lean) and that switch's front
(`First.K2.frontAt`, Johnson/Top/H0/K2Hears/Long.lean) return. This is the field door of `CarryOwed`
(Honest/K10/Xch/CarryTop.lean). Public: no witness is read.

Why it holds. An accepted closing writes into the live frame "a link's first message is due" and the next link's number,
and leaves the frame's shape and groups and the statement's codes as they were. The way in and the front ask just this,
and that the shape has the link, the list of groups an entry for it, the codes the shape's two numbers, and that the state
bears no mark. The three sorts of place: a link's first message (behind segments 0 to 22), the head's link (behind 23),
the finish (behind 24).

First, with no head:
  `newGroup_returns`, `firstFront_returns`, `finishFront_returns`   the three texts return where their tests pass
  `head_way_returns`, `fin_way_returns`   the quiet step in front of the head's link, and of the finish, returns at a state
                    between the links, and the switch's front is there at what it returns
  `inLink_of_stand`, `rest_of_stand`   a state that stands inside an open link, and what `rest` makes of it
  **`door_of_facts`**   the way in and the front return, at all three sorts, from facts on the state
  `written_group_ok`, `stand_at_23`   two closed facts, by Lean's kernel: the written codes have the written shape's two
                    numbers; at the closing of segment 23 the table has the chain stand inside an attention segment
Then at the head's thread:
  `stand_is_thr`      wherever the invariant holds at a border, the state stands where the table says
  **`door_at_step`**    from the invariant in front of a closing and the block's accepted step: the field door's conclusion
  `door_at_stepAt`    the same from `StepAt`, to the sign of the field

Limits. The head (`P5J.AtMgA`, at the older hash) is a premise; whether it can be had at any files is not shown here, nor
that the invariant holds in any run, nor that the step accepts. What the front holds is not said. The full size alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.CarryTop
import Johnson.Desc.ProofFile.Honest.K10.Pay.FrameFacts
import Johnson.Desc.ProofFile.Honest.K10.Pay.Run
import Johnson.Desc.First.Link.Law.DressAtAll
import Johnson.Loose.H2K12.HsAtAll
import Johnson.Goal.Meaning.RecK10
import Johnson.IMR.SortDigits
import Johnson.P5T.ShapeFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S ModelPart standOf shapeAt onAt pubSets)
open VerifiableInference.Desc.First.Close (Par closeFrame entries closing_writes)
open VerifiableInference.Desc.First.K2 (P2 frontAt headFrontQ finishFrontQ)
open VerifiableInference.Desc.First.K2Caller (doorZ rest)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk (firstDue finishDue)
open Johnson.G (codesFull2)
open _root_.Tw.K2 (firstFront finishFront newGroupG)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## 1 No head -/

/-- A new group is made where the codes have the two numbers. -/
theorem newGroup_returns {T : Statement} {c z : Nat} (hc : Ground.ok (Ground.groupL T.codes c z) = true) :
    ∃ y, newGroupG T c z = .ok y := by
  have hc' : Ground.ok (Ground.newGroupL (_root_.Tw.K2.dOf T).st c z) = true := hc
  unfold _root_.Tw.K2.newGroupG Ground.newGroupP
  rw [if_pos hc']
  exact ⟨_, rfl⟩

/-- The front of a later link's switch returns. -/
theorem firstFront_returns {T : Statement} {f : ReqFrame} {L : Params.ReqLink} {G : ReqGroup}
    (h1 : f.next = .first) (h0 : f.link ≠ 0) (hL : f.shape.link[f.link]? = some L)
    (hG : f.groups[f.link]? = some G)
    (hc : Ground.ok (Ground.groupL T.codes f.shape.code f.shape.maskCode) = true) :
    ∃ x, firstFront T f = .ok x := by
  obtain ⟨⟨S', g⟩, hy⟩ := newGroup_returns hc
  have a1 : (f.next != .first) = false := by simp [h1]
  have a0 : (f.link == 0) = false := by simpa using h0
  unfold _root_.Tw.K2.firstFront
  simp only [a1, a0, hL, hG, hy, Bool.false_eq_true, if_false]
  exact ⟨_, rfl⟩

/-- The front of the finish's switch returns. -/
theorem finishFront_returns {T : Statement} {f : ReqFrame} {G : ReqGroup}
    (h1 : f.next = .first) (hl : f.link = f.shape.link.length) (hG : f.groups[f.link]? = some G)
    (hc : Ground.ok (Ground.groupL T.codes f.shape.code f.shape.maskCode) = true) :
    ∃ x, finishFront T f = .ok x := by
  obtain ⟨⟨S', g⟩, hy⟩ := newGroup_returns hc
  have a1 : (!(f.next == .first && f.link == f.shape.link.length)) = false := by
    rw [h1, ← hl]
    simp
  unfold _root_.Tw.K2.finishFront
  simp only [a1, hG, hy, Bool.false_eq_true, if_false]
  exact ⟨_, rfl⟩

/-- The quiet step in front of the head's link returns at a state between the links without a mark, and the switch's
front is there at what it returns. -/
theorem head_way_returns {p : P2} (hp : p.stands = .head) {v : S} (tl : HTailF2) (hb : v.here = .between)
    (hi : v.check.inLink = false) (hf : v.failed = none)
    (hlt : v.check.frame.link < v.check.frame.shape.link.length) {x : _root_.Tw.K2.Front}
    (hx : firstFront v.st v.check.frame = .ok x) {G : ReqGroup}
    (hG : v.check.frame.groups[v.check.frame.link]? = some G) :
    ∃ t, headFrontQ tl v = .ok t ∧ ∃ fx, frontAt p t = some fx := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := v
  dsimp only at hb hi hf hlt hx hG
  subst hb hf
  have hd : firstDue check = true := by
    unfold firstDue
    simp [hi, hlt]
  unfold headFrontQ
  simp only [S.atBetween, Bool.not_true, Bool.false_eq_true, if_false, hd]
  rw [hx]
  simp only [Except.bind, S.enterHead?, S.enterHead, S.atBetween, S.unmarked, if_true]
  refine ⟨_, rfl, ?_⟩
  unfold frontAt
  simp only [hp]
  rw [hG]
  exact ⟨_, rfl⟩

/-- The quiet step in front of the finish returns at such a state, and the switch's front is there at what it returns. -/
theorem fin_way_returns {p : P2} (hp : p.stands = .finish) {v : S} (hb : v.here = .between)
    (hi : v.check.inLink = false) (hf : v.failed = none)
    (hl : v.check.frame.link = v.check.frame.shape.link.length) {x : _root_.Tw.K2.Front}
    (hx : finishFront v.st v.check.frame = .ok x) {G : ReqGroup}
    (hG : v.check.frame.groups[v.check.frame.link]? = some G) :
    ∃ t, finishFrontQ v = .ok t ∧ ∃ fx, frontAt p t = some fx := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := v
  dsimp only at hb hi hf hl hx hG
  subst hb hf
  have hd : finishDue check = true := by
    unfold finishDue
    rw [hi, ← hl]
    simp
  unfold finishFrontQ
  simp only [S.atBetween, Bool.not_true, Bool.false_eq_true, if_false, hd]
  rw [hG, hx]
  simp only [Except.bind, S.enterFin?, S.enterFin, S.atBetween, S.unmarked, if_true]
  refine ⟨_, rfl, ?_⟩
  unfold frontAt
  simp only [hp, Option.map_some]
  exact ⟨_, rfl⟩

/-- A state that stands inside an open link has a link open. -/
theorem inLink_of_stand {u : S} {sub : ModelPart} (h : standOf u = .link sub) : u.inLink = true := by
  unfold standOf at h
  cases e : u.here with
  | between => rw [e] at h; cases h
  | lay a => simp [S.inLink, S.fork?, e]
  | att a => simp [S.inLink, S.fork?, e]
  | head a =>
    rw [e] at h
    by_cases c : u.inLink = true
    · exact c
    · simp [c] at h
  | fin a => rw [e] at h; cases h
  | mem a => rw [e] at h; cases h

/-- What `rest` makes of such a state. -/
theorem rest_of_stand {u : S} {sub : ModelPart} (h : standOf u = .link sub) :
    rest u = { u with check := { u.live with inLink := false }, here := .between } := by
  unfold rest
  rw [if_pos (inLink_of_stand h)]

/-- **The way in and the front return, at all three sorts of place**, from facts on the state. -/
theorem door_of_facts {Zp : ProofFile.Pub} {l : Nat} {u : S} {sub : ModelPart} (hst : standOf u = .link sub)
    (hnh : (ProofFile.pAtK2 Zp l).stands = .head → ∀ b, u.here ≠ .head b) (hf : u.failed = none)
    (h1 : u.live.frame.next = .first) (h0 : u.live.frame.link ≠ 0)
    (hlt : (ProofFile.pAtK2 Zp l).stands ≠ .finish → u.live.frame.link < u.live.frame.shape.link.length)
    (hfn : (ProofFile.pAtK2 Zp l).stands = .finish → u.live.frame.link = u.live.frame.shape.link.length)
    {G : ReqGroup} (hG : u.live.frame.groups[u.live.frame.link]? = some G)
    (hc : Ground.ok (Ground.groupL u.st.codes u.live.frame.shape.code u.live.frame.shape.maskCode) = true) :
    ∃ t fx, doorZ Zp l u = some t ∧ frontAt (ProofFile.pAtK2 Zp l) t = some fx := by
  have hR := rest_of_stand hst
  cases hs : (ProofFile.pAtK2 Zp l).stands with
  | link =>
    have hlt' := hlt (by rw [hs]; exact fun c => by cases c)
    obtain ⟨x, hx⟩ := firstFront_returns (T := u.st) h1 h0 (List.getElem?_eq_getElem hlt') hG hc
    refine ⟨rest u, x, ?_, ?_⟩
    · unfold doorZ
      rw [hs]
    · unfold frontAt
      rw [hs, hR]
      show (firstFront u.st u.live.frame).toOption = some x
      rw [hx]
      rfl
  | head =>
    have hlt' := hlt (by rw [hs]; exact fun c => by cases c)
    obtain ⟨x, hx⟩ := firstFront_returns (T := u.st) h1 h0 (List.getElem?_eq_getElem hlt') hG hc
    obtain ⟨t, ht, fx, hfx⟩ := head_way_returns (p := ProofFile.pAtK2 Zp l) hs
      (v := { u with check := { u.live with inLink := false }, here := .between }) {} rfl rfl hf hlt' hx hG
    refine ⟨t, fx, ?_, hfx⟩
    have hn := hnh hs
    unfold doorZ
    rw [hs, hR]
    cases e : u.here with
    | head b => exact absurd e (hn b)
    | between => show (headFrontQ {} _).toOption = some t; rw [ht]; rfl
    | lay a => show (headFrontQ {} _).toOption = some t; rw [ht]; rfl
    | att a => show (headFrontQ {} _).toOption = some t; rw [ht]; rfl
    | fin a => show (headFrontQ {} _).toOption = some t; rw [ht]; rfl
    | mem a => show (headFrontQ {} _).toOption = some t; rw [ht]; rfl
  | finish =>
    have hl' := hfn hs
    obtain ⟨x, hx⟩ := finishFront_returns (T := u.st) h1 hl' hG hc
    obtain ⟨t, ht, fx, hfx⟩ := fin_way_returns (p := ProofFile.pAtK2 Zp l) hs
      (v := { u with check := { u.live with inLink := false }, here := .between }) rfl rfl hf hl' hx hG
    refine ⟨t, fx, ?_, hfx⟩
    unfold doorZ
    rw [hs, hR]
    show (finishFrontQ _).toOption = some t
    rw [ht]
    rfl

set_option maxRecDepth 1000000 in
/-- The written codes have the written shape's two numbers, and the mask code is not the longer one. -/
theorem written_group_ok : Ground.ok (Ground.groupL codesFull2 shapeFull.code shapeFull.maskCode) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At the closing of segment 23 the table has the chain stand inside an attention segment. -/
theorem stand_at_23 :
    (P5J.At.ps[14 * 23 + IM.nAt 23 + 5]?).map (VerifiableInference.Desc.First.standAt P5J.At.links) =
      some (VerifiableInference.Desc.First.Stand.link .attention) := by
  decide +kernel

/-! ## 2 At the head's thread -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. The option turns off one early look at the notation's text, which has no
-- case for a field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- Wherever the invariant holds at a border in front of a block, the state stands where the table says. -/
theorem stand_is_thr {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 b k s m En) {p : Place} (hp : P5J.At.ps[b]? = some p) :
    standOf s = VerifiableInference.Desc.First.standAt P5J.At.links p := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hP, -, -, -, -⟩ := hT'
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 hP.1
  have hF : (𝕋).formP b (m.st.input.x.pub, s) := hP.2
  have hon : onAt (P5J.At.N Zp cF) (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links
      P5J.At.ps[b]? (P5J.oAt b)
      (((pubSets (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more P5J.At.links
        P5J.At.ps)[b]?).getD []) (m.st.input.x.pub, s) noStrs := hF
  rcases hon.2 with c | c
  · exact absurd hf c
  · have e := c.1
    simp only [Bool.and_eq_true] at e
    have hh := e.1.1.1.1.1
    rw [hp] at hh
    unfold shapeAt at hh
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    exact hh.1.1

/-- **Behind an accepted closing the way into the next code switch and that switch's front return.** -/
theorem door_at_step {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) {ft : Nat} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat}
    (hs : blk.step ft s rs cols = .ok (s', n)) :
    ∃ t fx, doorZ Zp l s' = some t ∧ frontAt (ProofFile.pAtK2 Zp l) t = some fx := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hl : l < 25 := link_lt h hlt
  have hr := thr_reach h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT
  have hf : s.failed = none := (run_held_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hT).1
  obtain ⟨-, -, hD, hf', -⟩ := tied_decides Td hs
  obtain ⟨y, hy, rfl⟩ := closing_writes Qc s s' _ _ hD
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := _root_.Meaning.K2.closeFrame_all hy
  obtain ⟨-, hc, hsh, -, -⟩ := facts_reached h hr hf
  have eL : (K9.recOf s).frame.link = l := (frame_rec h hl hr hf).2.1
  have eS : (K9.recOf s).frame.shape = shapeFull := hsh.trans h.toAtMg.shapeAt_full
  have eG : (K9.recOf s).frame.groups = reqGroups shapeFull := frame_groups_eq h hr hf
  have eF : (K9.putRec s ⟨none, y.1, y.2⟩).live.frame = y.1 := LeftIs.live_putRec s ⟨none, y.1, y.2⟩
  have len : shapeFull.link.length = 25 := congrArg Prod.fst P5T.shape_ok
  obtain ⟨sub, hst⟩ := stand_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl hT
  have hst' : standOf (K9.putRec s ⟨none, y.1, y.2⟩) = .link sub := (First.putRec_standOf _ _).trans hst
  have hgl : l + 1 < (reqGroups shapeFull).size := by
    have := frame_groups_size
    omega
  -- the sort of the place, by the segment
  have sort : (l < 23 ∧ (ProofFile.pAtK2 Zp l).stands = .link) ∨ (l = 23 ∧ (ProofFile.pAtK2 Zp l).stands = .head) ∨
      (l = 24 ∧ (ProofFile.pAtK2 Zp l).stands = .finish) := by
    rcases Nat.lt_or_ge l 23 with c | c
    · exact Or.inl ⟨c, h.stands_link_atAll l c⟩
    · rcases Nat.lt_or_ge l 24 with c' | c'
      · obtain rfl : l = 23 := by omega
        exact Or.inr (Or.inl ⟨rfl, H2K12.hs_atAll h⟩)
      · obtain rfl : l = 24 := by omega
        exact Or.inr (Or.inr ⟨rfl, h.stands_finish_atAll⟩)
  refine door_of_facts (G := (reqGroups shapeFull)[l + 1]) hst' ?_ hf' ?_ ?_ ?_ ?_ ?_ ?_
  · intro hh b hb
    rcases sort with ⟨-, c⟩ | ⟨rfl, -⟩ | ⟨-, c⟩
    · rw [c] at hh; cases hh
    · obtain ⟨q, hq, eq⟩ := Option.map_eq_some_iff.1 stand_at_23
      have e1 := stand_is_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hT hq
      have e2 : standOf (K9.putRec s ⟨none, y.1, y.2⟩) = .link .attention :=
        (First.putRec_standOf _ _).trans (e1.trans eq)
      obtain ⟨a, ha⟩ := _root_.Meaning.K2.att_of_stand e2
      rw [ha] at hb
      cases hb
    · rw [c] at hh; cases hh
  · rw [eF]; exact a4
  · rw [eF, a3]; omega
  · intro hn
    rw [eF, a3, a1, eL, eS, len]
    rcases sort with ⟨c, -⟩ | ⟨c, -⟩ | ⟨-, c⟩
    · omega
    · omega
    · exact absurd c hn
  · intro hh
    rw [eF, a3, a1, eL, eS, len]
    rcases sort with ⟨-, c⟩ | ⟨-, c⟩ | ⟨c, -⟩
    · rw [c] at hh; cases hh
    · rw [c] at hh; cases hh
    · omega
  · rw [eF, a3, a2, eL, eG]
    exact Array.getElem?_eq_getElem hgl
  · rw [eF, a1, eS]
    show Ground.ok (Ground.groupL y.2.codes shapeFull.code shapeFull.maskCode) = true
    rw [a5]
    show Ground.ok (Ground.groupL s.st.codes shapeFull.code shapeFull.maskCode) = true
    rw [hc, h.toAtMg.codes_full]
    exact written_group_ok

/-- **The field door of `CarryOwed`**, at every second condition Said. -/
theorem door_at_stepAt (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn} {s' : TS}
    (St : StepAt 𝕋 Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s') :
    ∃ t fx, doorZ Zp l s' = some t ∧ frontAt (ProofFile.pAtK2 Zp l) t = some fx :=
  door_at_step h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td St.thr.1 St.step.2

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.newGroup_returns
#print axioms ProofFile.Honest.K10.firstFront_returns
#print axioms ProofFile.Honest.K10.finishFront_returns
#print axioms ProofFile.Honest.K10.head_way_returns
#print axioms ProofFile.Honest.K10.fin_way_returns
#print axioms ProofFile.Honest.K10.inLink_of_stand
#print axioms ProofFile.Honest.K10.rest_of_stand
#print axioms ProofFile.Honest.K10.door_of_facts
#print axioms ProofFile.Honest.K10.written_group_ok
#print axioms ProofFile.Honest.K10.stand_at_23
#print axioms ProofFile.Honest.K10.stand_is_thr
#print axioms ProofFile.Honest.K10.door_at_step
#print axioms ProofFile.Honest.K10.door_at_stepAt
