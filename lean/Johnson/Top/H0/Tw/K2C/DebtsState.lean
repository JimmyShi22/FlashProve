-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-

Johnson/Top/H0/Tw/K2C/DebtsState.lean: the code switch: WHAT IS OWED ON THE TABLE's NUMBERS AT A
SWITCH (LinkDebts | SwitchDebts), FROM SIX FACTS ON THE STATE AT THE BORDER, THE FENCE's FIRST
CLAUSE AND CLOSED FACTS: DebtsJoin.lean's premises on the state, paid out of their payers' theorems.
  frontOf_iff  FrontOf (SendsOn.lean) and K2.frontAt (K2Hears/Long.lean) say
               the same
  fence_of_first  the fence's three clauses from its first (the notices are the plan's) and the
               statement's codes; the number of messages is the state's own
  SwState      THE SIX FACTS: the walk's copy of the frame has the plan's shape · its groups are
               that shape's · it stands at link m · the statement's codes · the two invariants on
               stored sample rows
  target_of_plan_finish  at the finish too the front's target is the plan's at the frame's link
               (PositionAtPlan.lean's target_of_plan does not reach the finish)
  both_at_front  the two invariants at the front's statement
  debts_at_front · debts_at_finish  THE STATEMENTS: both structures at a link's or the head's
               switch; SwitchDebts at the finish's
CALLED: told_succ_ps (First/ToldSucc.lean) · keptPos_atFront |
keptPos_atFinish (KeptPosAt.lean) · target_of_plan · finishFrontQ_st | _fr (FinFront.lean) ·
front_tables (K2Hears/SampleGood.lean) · rowsInv_congr · answered_congr · hone_of_both
(OneStored.lean) · debts_link | _head | _finish (DebtsJoin.lean). WHO PAYS SwState. shape · groups ·
codes: fields of FoldFacts (First/FoldFacts.lean). good · answered: both_in_scope (in P1K2R/). link:
«in front of the switch into group m the walk's copy of the frame stands at link m»: no field of
FoldFacts says it between two links [by a reading not held against the file that ships]; the walk in
Johnson/IMR/ has it (its fence1_* spend it); «laid» m tests it (Walk/Frame.lean's layFront, W2).
LIMITS. Joins. None of the premises is shown at a real value here. No soundness is claimed.

-/
import Johnson.Top.H0.Tw.K2C.DebtsJoin
import Johnson.Top.H0.Tw.K2C.OneStored
import Johnson.Top.H0.Tw.K2C.KeptPosAt
import Johnson.Top.H0.Tw.K2C.FinFront
import Johnson.Top.H0.K2Hands.SampleChainS
import Johnson.Desc.First.ToldSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place Block)
open _root_.Tw.K2 (switchNotices firstFront)
open P1K2 (oraclesAt)

/-- The two ways of saying «x is the front that the switch is handed off s». -/
theorem frontOf_iff {p : P2} {s : S} {x : _root_.Tw.K2.Front} :
    FrontOf p s x ↔ frontAt p s = some x := by
  unfold FrontOf frontAt
  cases hp : p.stands with
  | link =>
    simp only [true_and, reduceCtorEq, false_and, or_false]
    cases hf : firstFront s.st s.check.frame with
    | error e => simp [Except.toOption]
    | ok y => simp [Except.toOption]
  | head =>
    simp only [true_and, reduceCtorEq, false_and, or_false, false_or]
    cases hq : s.here with
    | head a =>
      constructor
      · rintro ⟨a', G, ha, hG, rfl⟩
        cases ha
        simp [hG]
      · intro h
        obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨a, G, rfl, hG, rfl⟩
    | between => simp
    | lay a => simp
    | att a => simp
    | fin a => simp
    | mem a => simp
  | finish =>
    simp only [true_and, reduceCtorEq, false_and, false_or]
    cases hq : s.here with
    | fin a =>
      constructor
      · rintro ⟨a', G, ha, hG, rfl⟩
        cases ha
        simp [hG]
      · intro h
        obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨a, G, rfl, hG, rfl⟩
    | between => simp
    | lay a => simp
    | att a => simp
    | head a => simp
    | mem a => simp

/-- **The fence from its first clause and the statement's codes.** -/
theorem fence_of_first {p : P2} {sent : Array OracleNotice} {codes : Codes} {t : S}
    (h1 : ∀ x, FrontOf p t x → switchNotices x.T x.others = sent) (hc : t.st.codes = codes) :
    Fence p sent codes t.st.oracles.size t := by
  intro x hx
  obtain ⟨c1, c2⟩ := front_tables (frontOf_iff.1 hx)
  exact ⟨h1 x hx, c1.trans hc, by rw [c2]⟩

/-- **What is asked of the state at the border in front of a switch.** sh: the plan's shape of the
request. m: the group into which the switch leads. -/
structure SwState (sh : Params.ReqShape) (m : Nat) (codes : Codes) (s : S) : Prop where
  shape : s.check.frame.shape = sh
  groups : s.check.frame.groups = reqGroups s.check.frame.shape
  link : s.check.frame.link = m
  codes : s.st.codes = codes
  good : SampleGoodS s.st
  answered : AnsweredStored s.st

/-- At the finish the front's target is the plan's too. -/
theorem target_of_plan_finish {p : P2} {s t : S} {x : _root_.Tw.K2.Front}
    (he : finishFrontQ s = .ok t) (h : frontAt p t = some x) (hp : p.stands = .finish) {m : Nat}
    (hm : s.check.frame.link = m)
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape) :
    x.T = ((reqGroups s.check.frame.shape).getD m {}).target := by
  obtain ⟨a, G, ha, hG, hgr, _, _, hl, hfg, _⟩ := finishFrontQ_fr he
  rcases front_target h with ⟨_, a', G', ha', hG', e⟩ | ⟨hn, _⟩
  · cases ha.symm.trans ha'
    obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
    rw [hfg, hl, hm, hg] at hgr
    rw [e, Array.getD_eq_getD_getElem?, hgr]
    rfl
  · exact absurd hp hn

/-- The two invariants at the front's statement, from a statement with the same codes and oracle
messages. -/
theorem both_at_front {p : P2} {s t : S} {x : _root_.Tw.K2.Front} (h : frontAt p t = some x)
    (w1 : t.st.codes = s.st.codes) (w2 : t.st.oracles = s.st.oracles) (hG : SampleGoodS s.st)
    (hA : AnsweredStored s.st) : SampleGoodS x.st ∧ AnsweredStored x.st := by
  obtain ⟨c1, c2⟩ := front_tables h
  exact ⟨(sampleGoodS_iff _).2 (rowsInv_congr (Q := QGoodS) (c1.trans w1) (c2.trans w2)
    ((sampleGoodS_iff _).1 hG)), answered_congr (c2.trans w2) hA⟩

section
variable {St Cl : Type} {N₀ : Numbers} {sh : Params.ReqShape} {links : List ModelPart}
  {bs : List (Block St Cl)} {ps : List Place}

/-- **AT A LINK's OR THE HEAD's SWITCH: BOTH STRUCTURES, FROM THE STATE's SIX FACTS.** -/
theorem debts_at_front (hps : blockPlaces bs = ps) (hnd : ps.Nodup) {k : Nat} {b : Block St Cl}
    (hbk : bs[k]? = some b) {grp : Nat} {codes : Codes} {sent : Array OracleNotice}
    (hor : b.oracles.flatten = oraclesAt grp codes sent) {m : Nat} (hm : m ≠ 0)
    (hT : sentFitB (N₀.atBlocks sh links bs) m ps[k]? codes sent = true) {d : Nat}
    (hpos : possAt bs links.length m = d) (hok : reqShapeOk sh = true)
    (hlenC : (N₀.keptOf (m - 1)).length = ((reqGroups sh).getD m {}).target.kept.size) {s : S}
    (hb : First.bookAt (N₀.atBlocks sh links bs) ps[k]? s = true) (Q : SwState sh m codes s)
    {p : P2}
    (hp : p.stands ≠ .finish) (h1 : ∀ x, FrontOf p s x → switchNotices x.T x.others = sent)
    {x : _root_.Tw.K2.Front} (h : frontAt p s = some x) {W : SwitchFrame}
    (hW : frameAt x = some W) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay)
    (hans : ∀ κ ∈ W.kept, ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧
      xo.shape.answers = 1) :
    LinkDebts (N₀.atBlocks sh links bs) m ps[k]? ps[k + 1]? s d x W lay ∧
      SwitchDebts (N₀.atBlocks sh links bs) m ps[k]? ps[k + 1]? s.book.trees.size d
        (1 + x.T.kept.size + x.own.length) x W lay := by
  have hts := told_succ_ps N₀ sh links bs ps hps hnd k b hbk
  have hx := frontOf_iff.2 h
  have hF := fence_of_first h1 Q.codes
  have kp := keptPos_atFront h hp Q.shape Q.groups hok
  have hTg : x.T = ((reqGroups sh).getD m {}).target := by
    have e := target_of_plan h hp Q.link Q.groups
    rwa [Q.shape] at e
  have hlen : (N₀.keptOf (m - 1)).length = x.T.kept.size := by rw [hTg]; exact hlenC
  obtain ⟨g, a⟩ := both_at_front h rfl rfl Q.good Q.answered
  have hone := hone_of_both g a hans
  exact ⟨debts_link hts hor hm hT hb hF hx hl hW kp hTg hpos hlen hone,
    debts_head hts hor hm hT hb hF hx hl hW kp hTg hpos hlen hone⟩

/-- **AT THE FINISH's SWITCH.** s: the state at the border. t: behind the way in. -/
theorem debts_at_finish (hps : blockPlaces bs = ps) (hnd : ps.Nodup) {k : Nat} {b : Block St Cl}
    (hbk : bs[k]? = some b) {grp : Nat} {codes : Codes} {sent : Array OracleNotice}
    (hor : b.oracles.flatten = oraclesAt grp codes sent) {m : Nat} (hm : m ≠ 0)
    (hT : sentFitB (N₀.atBlocks sh links bs) m ps[k]? codes sent = true) {d : Nat}
    (hpos : possAt bs links.length m = d) (hok : reqShapeOk sh = true)
    (hlenC : (N₀.keptOf (m - 1)).length = ((reqGroups sh).getD m {}).target.kept.size) {s t : S}
    (hb : First.bookAt (N₀.atBlocks sh links bs) ps[k]? s = true) (Q : SwState sh m codes s)
    (he : finishFrontQ s = .ok t) {p : P2} (hp : p.stands = .finish)
    (h1 : ∀ x, FrontOf p t x → switchNotices x.T x.others = sent)
    {x : _root_.Tw.K2.Front} (h : frontAt p t = some x) {W : SwitchFrame}
    (hW : frameAt x = some W) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay)
    (hans : ∀ κ ∈ W.kept, ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧
      xo.shape.answers = 1) :
    SwitchDebts (N₀.atBlocks sh links bs) m ps[k]? ps[k + 1]? s.book.trees.size d
      (1 + x.T.kept.size) x W lay := by
  have hts := told_succ_ps N₀ sh links bs ps hps hnd k b hbk
  have hx := frontOf_iff.2 h
  have w1 : t.st.codes = s.st.codes := by rw [finishFrontQ_st he]; rfl
  have w2 : t.st.oracles = s.st.oracles := by rw [finishFrontQ_st he]; rfl
  have hF := fence_of_first h1 (w1.trans Q.codes)
  have kp := keptPos_atFinish he h hp Q.shape Q.groups hok
  have hTg : x.T = ((reqGroups sh).getD m {}).target := by
    have e := target_of_plan_finish he h hp Q.link Q.groups
    rwa [Q.shape] at e
  have hlen : (N₀.keptOf (m - 1)).length = x.T.kept.size := by rw [hTg]; exact hlenC
  obtain ⟨g, a⟩ := both_at_front h w1 w2 Q.good Q.answered
  have hone := hone_of_both g a hans
  exact debts_finish hts hor hm hT hb hp hF hx hl hW kp hTg hpos hlen hone

end

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.debts_at_front
#print axioms VerifiableInference.Desc.First.K2.debts_at_finish

#print axioms VerifiableInference.Desc.First.K2.frontOf_iff
#print axioms VerifiableInference.Desc.First.K2.fence_of_first
#print axioms VerifiableInference.Desc.First.K2.target_of_plan_finish
#print axioms VerifiableInference.Desc.First.K2.both_at_front
