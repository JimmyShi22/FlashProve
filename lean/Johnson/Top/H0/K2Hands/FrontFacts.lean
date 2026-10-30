-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontFacts.lean: the code switch's law: THE ONE TEST ON A SWITCH's FRONT
(frontB2, FrontB2.lean) AS NINETEEN PLAIN FACTS, BOTH WAYS; and how the front that the text makes
hangs on the verifier's state. So that a theorem along the fold can pay the test fact by fact. A law
file; no running text imports it.

x₀: the written front of the place's entry. W₀: its frame. grp, rows, n0, olds: the place's own
numbers. fx: the front that the text makes of the verifier's state t in front of the switch.

  FrontFacts x₀ W₀ grp rows n0 olds fx   a structure, a field a fact. WHO HAS EACH stands in
                 the field's own comment.
  frontB2_iff    frontB2 x₀ W₀ grp rows n0 olds fx = true ↔ FrontFacts x₀ W₀ grp rows n0 olds fx.
  CopyAt p t f   which copy of the frame the switch at p is handed: at a link the chain's own; at
                 the head's link and at the finish the own part's.
  front_of_state: frontAt p t = some fx gives: the front's codes and messages are t's; its carried
                 rows are that copy's; its target is the target of a group of a frame of t's, at
                 that frame's link.
Limits. Nothing is paid here: the file turns a Bool into Props and back. Four fields have no payer
(oldsIs, keptRows, tensors, d0 | d1): all speak of the carried rows that the last closing laid.
Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontB2
import Johnson.Top.H0.K2Hears.SampleGood
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes

/-- **The test on a switch's front, fact by fact.** -/
structure FrontFacts (x₀ : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (grp rows n0 : ℕ) (olds : List ℕ)
    (fx : _root_.Tw.K2.Front) : Prop where
  /-- payer: the fold's fact «codes» at t, front_of_state, a closed fact at the written entry -/
  codes : fx.st.codes = x₀.st.codes
  /-- NO PAYER: the kept members of the carried rows' layout are the place's own numbers -/
  oldsIs : (switchKept fx.f.rows).toList = olds
  /-- payer: the fold's fact «msgShapes» at t, given oldsIs and below; a closed fact on the listed
  shapes -/
  shapes : olds.map (fun o => (fx.st.oracles[o]?).map (·.shape)) = keptShapes x₀
  /-- payer: a closed fact on (olds, n0); or, at a yes, the switch's own test on its target -/
  below : ∀ o ∈ olds, o < n0
  /-- payer: closed, at the written entry -/
  below₀ : keptBelowB x₀ = true
  /-- payer, these four: front_of_state, the fold's facts «groups» | «frameGroups» and «shape» |
  «frameShape», the link's number; a closed fact on the public shape's groups -/
  tShape : fx.T.shape = x₀.T.shape
  tMain : fx.T.main = x₀.T.main
  tRest : fx.T.rest = x₀.T.rest
  tKept : fx.T.kept.toList.map (·.shape) = x₀.T.kept.toList.map (·.shape)
  /-- payer, these three: the walk's fact on every copy of the frame -/
  code : fx.f.rows.code = x₀.f.rows.code
  maskCode : fx.f.rows.maskCode = x₀.f.rows.maskCode
  masks : fx.f.rows.masks = x₀.f.rows.masks
  /-- NO PAYER: the closing's count of the kept members' main rows -/
  keptRows : fx.f.rows.keptRows = x₀.f.rows.keptRows
  /-- payer: at a link the front pushes the group; at the head and the finish the text asks it -/
  group : fx.f.group = grp
  /-- payer: the front's group is fresh -/
  fresh : ∃ G, fx.st.groups[grp]? = some G ∧ G.rows.size = rows
  /-- payer: the count of messages at the cut -/
  count : fx.st.oracles.size = n0
  /-- NO PAYER: the closing's form on the main row's message -/
  tensors : ∀ v ∈ fx.f.rows.c.tensors, v.vars = W₀.code.logEll
  /-- NO PAYER, these two: the lengths of the closing's two vectors on the mask rows -/
  d0 : (fx.f.rows.d.getD 0 #[]).size ≤ W₀.zk.ell
  d1 : (fx.f.rows.d.getD 1 #[]).size ≤ W₀.zk.ell

theorem facts_of_test {x₀ fx : _root_.Tw.K2.Front} {W₀ : SwitchFrame} {grp rows n0 : ℕ}
    {olds : List ℕ} (h : frontB2 x₀ W₀ grp rows n0 olds fx = true) :
    FrontFacts x₀ W₀ grp rows n0 olds fx := by
  simp only [frontB2, Bool.and_eq_true] at h
  obtain ⟨⟨hp, hn⟩, hc⟩ := h
  obtain ⟨n1, n2, n3, n4⟩ := nums_of_test hn
  obtain ⟨c1, c2, c3⟩ := carried_of_test hc
  simp only [pinB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩, p8⟩, p9⟩, p10⟩, p11⟩, p12⟩ := hp
  refine ⟨p1, n4, ?_, ?_, p4, p5, p6, p7, p8, p9, p10, p11, p12, n1, n2, n3, c1, c2, c3⟩
  · rw [← p2, ← n4]
    rfl
  · intro o ho
    rw [← n4] at ho
    have := (Array.all_eq_true_iff_forall_mem.1 p3) o (Array.mem_toList_iff.1 ho)
    rw [← n3]
    exact of_decide_eq_true this

theorem test_of_facts {x₀ fx : _root_.Tw.K2.Front} {W₀ : SwitchFrame} {grp rows n0 : ℕ}
    {olds : List ℕ} (F : FrontFacts x₀ W₀ grp rows n0 olds fx) :
    frontB2 x₀ W₀ grp rows n0 olds fx = true := by
  have hk : keptShapes fx = keptShapes x₀ := by
    rw [← F.shapes, ← F.oldsIs]
    rfl
  have hb : keptBelowB fx = true := by
    refine Array.all_eq_true_iff_forall_mem.2 fun o ho => decide_eq_true ?_
    rw [F.count]
    exact F.below o (by rw [← F.oldsIs]; exact Array.mem_toList_iff.2 ho)
  obtain ⟨G, hG, hr⟩ := F.fresh
  simp only [frontB2, pinB, numsB, carriedB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨F.codes, hk⟩, hb⟩, F.below₀⟩, F.tShape⟩, F.tMain⟩, F.tRest⟩, F.tKept⟩,
    F.code⟩, F.maskCode⟩, F.masks⟩, F.keptRows⟩, ⟨⟨⟨F.group, ?_⟩, F.count⟩, F.oldsIs⟩⟩,
    ⟨⟨F.tensors, F.d0⟩, F.d1⟩⟩
  rw [F.group, hG]
  simpa using hr

/-- **The test is these nineteen facts.** -/
theorem frontB2_iff (x₀ fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (grp rows n0 : ℕ)
    (olds : List ℕ) :
    frontB2 x₀ W₀ grp rows n0 olds fx = true ↔ FrontFacts x₀ W₀ grp rows n0 olds fx :=
  ⟨facts_of_test, test_of_facts⟩

/-! ## From the verifier's state to the front -/

/-- Which copy of the frame the switch at p is handed. -/
def CopyAt (p : K2.P2) (t : S) (f : ReqFrame) : Prop :=
  match p.stands, t.here with
  | .link, _ => f = t.check.frame
  | .head, .head a => f = a.fr
  | .finish, .fin a => f = a.fr
  | _, _ => False

/-- **How the front hangs on the state.** -/
theorem front_of_state {p : K2.P2} {t : S} {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt p t = some fx) :
    fx.st.codes = t.st.codes ∧ fx.st.oracles = t.st.oracles ∧
      ∃ f, CopyAt p t f ∧ fx.f.rows = f.rows ∧ fx.f.shape = f.shape ∧ fx.f.link = f.link ∧
        ∃ g : ReqGroup, fx.T = g.target ∧
          (t.check.frame.groups[t.check.frame.link]? = some g ∨
            ∃ a, t.here = .fin a ∧ a.G = some g) := by
  obtain ⟨e1, e2⟩ := K2.front_tables h
  refine ⟨e1, e2, ?_⟩
  unfold K2.frontAt at h
  split at h
  · rename_i hs
    cases hf : _root_.Tw.K2.firstFront t.st t.check.frame with
    | error e => rw [hf] at h; simp [Except.toOption] at h
    | ok x =>
      rw [hf] at h
      obtain rfl : x = fx := by simpa [Except.toOption] using h
      obtain ⟨L, G, S', g, A⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hf
      refine ⟨t.check.frame, by simp [CopyAt, hs], ?_, ?_, ?_, G, ?_, Or.inl A.group⟩ <;> rw [A.out]
  · rename_i a hs hh
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨a.fr, by simp [CopyAt, hs, hh], rfl, rfl, rfl, G, rfl, Or.inl hG⟩
  · rename_i a hs hh
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨a.fr, by simp [CopyAt, hs, hh], rfl, rfl, rfl, G, rfl, Or.inr ⟨a, hh, hG⟩⟩
  · cases h

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.frontB2_iff
#print axioms VerifiableInference.Desc.First.K2Hands.front_of_state
