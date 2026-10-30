-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/FrontSide.lean: the code switch: THE FOLD's SIDE OF THE FIRST AND
THE FOURTH TIE AS ONE THEOREM: the premise hT1 of k02_t1R | k02_t4R (K2Caller/
TieOneR.lean · TieFourR.lean), at one state, from named premises, each in its payer's own letters.
  way_tables   the way in leaves the statement's codes and oracle messages: at a link and the head
               it is the identity; at the finish: finishFrontQ_st (Tw/K2C/FinFront.lean)
  kept_of_test  what the test on the front (K2Hands/FrontB2.lean's frontB2) says of the kept old
               messages, with one closed fact on the written front: olds is as long as the typed
               list of kept members, and the front's statement has, at each number of olds, a
               message of the typed kept member's shape. Out of the test's own clauses «the kept old
               messages' shapes are the written front's» and «what the carried rows keep is olds»
  frontSide_of  THE STATEMENT: the test accepts · the notices are the typed list · the invariant on
               stored sample rows at the front's statement · the test storedB at the written frame
               with the place's numbers · the state's and the front's statements hold the same
               oracle messages
ITS PREMISES, AND WHO PAYS EACH. hf: the front. h1: frontB2 accepts: frontB2_of_tops (K2Hands/
FrontJoin.lean). hG, hA: the two invariants AT THE BORDER's STATE: both_in_scope (BothInScope.lean).
hway: the way in: t is s, or at the finish
K2.finishFrontQ s = .ok t: the seated sub-protocol's door. hlen, hs: closed facts on the typed
structure and the written frame. hty: A NEW CLOSED FACT ON THE WRITTEN FRONT: its kept old
messages' shapes are the typed kept members': NO TEST WITH THIS SENTENCE LIES.
(Where this and lean/THEOREM.md differ, the page
holds.) hfence: the switch's notices are the plan's list: fence1_link | _head | _finish
(Johnson/IMR/MsgsBehind.lean; as reported: NOT READ HERE).
htied: closed: K2Hands/TiedAt.lean's tiedB at that list.
CALLED: front_of_state (K2Hands/FrontFacts.lean) · rowsInv_congr · sampleGoodS_iff (K2Hands/
SampleChain.lean · SampleChainS.lean) · answered_congr (K2Hands/AnsweredStored.lean) · storedB_of
(K2Caller/StoredOf.lean) · tied_of_sent (K2Hands/TiedAt.lean).
LIMITS. A join. None of the premises is shown at a real value here. No soundness is claimed.

-/
import Johnson.Top.H0.K2Caller.StoredOf
import Johnson.Top.H0.K2Hands.FrontFacts
import Johnson.Top.H0.K2Hands.TiedAt
import Johnson.Top.H0.K2Hands.SampleChainS
import Johnson.Top.H0.Tw.K2C.FinFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc.First VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

/-- **The way in leaves the statement's codes and oracle messages.** -/
theorem way_tables {p : K2.P2} {s t : S}
    (hway : (p.stands ≠ .finish ∧ t = s) ∨ (p.stands = .finish ∧ K2.finishFrontQ s = .ok t)) :
    t.st.codes = s.st.codes ∧ t.st.oracles = s.st.oracles := by
  rcases hway with ⟨-, rfl⟩ | ⟨-, hq⟩
  · exact ⟨rfl, rfl⟩
  · rw [K2.finishFrontQ_st hq]
    exact ⟨rfl, rfl⟩

/-- **What the test on the front says of the kept old messages**, with one closed fact on the
written front. -/
theorem kept_of_test {r : SwRow} {f₀ fx : _root_.Tw.K2.Front} {W : SwitchFrame}
    {grp rows n0 : ℕ} {olds : List ℕ} (h1 : frontB2 f₀ W grp rows n0 olds fx = true)
    (hty : keptShapes f₀ = r.kept.map fun i => (r.lo[i]?).map (·.1)) :
    olds.length = r.kept.length ∧
      ∀ (i o : ℕ) (y : OracleShape × ℕ), olds[i]? = some o →
        (r.kept[i]?).bind (r.lo[·]?) = some y →
        ∃ x : OnBytes.Oracle, fx.st.oracles[o]? = some x ∧ x.shape = y.1 := by
  simp only [frontB2, Bool.and_eq_true] at h1
  obtain ⟨⟨hp, hn⟩, -⟩ := h1
  obtain ⟨-, -, -, n4⟩ := nums_of_test hn
  have hks : olds.map (fun o => (fx.st.oracles[o]?).map (·.shape)) =
      r.kept.map fun i => (r.lo[i]?).map (·.1) := by
    rw [← n4]
    exact (pin_facts hp).shapes.trans hty
  refine ⟨by simpa using congrArg List.length hks, fun i o y ho hy => ?_⟩
  obtain ⟨k, hk, hy⟩ := Option.bind_eq_some_iff.1 hy
  have e := congrArg (fun l => l[i]?) hks
  simp only [List.getElem?_map, ho, hk, hy, Option.map_some] at e
  obtain ⟨x, hx, ex⟩ := Option.map_eq_some_iff.1 (Option.some.inj e)
  exact ⟨x, hx, ex⟩

/-- **THE FOLD's SIDE OF THE FIRST AND THE FOURTH TIE, AT ONE STATE.** s: the state at the border.
t: what the way in lets in of it. fx: the front that the text makes of t. -/
theorem frontSide_of {r : SwRow} {p : K2.P2} {s t : S} {fx f₀ : _root_.Tw.K2.Front}
    {W : SwitchFrame} {grp rows n0 : ℕ} {olds : List ℕ} (hf : K2.frontAt p t = some fx)
    (h1 : frontB2 f₀ W grp rows n0 olds fx = true)
    (hG : K2.SampleGoodS s.st) (hA : K2.AnsweredStored s.st)
    (hway : (p.stands ≠ .finish ∧ t = s) ∨ (p.stands = .finish ∧ K2.finishFrontQ s = .ok t))
    (hlen : W.kept.length = r.kept.length) (hs : keptShapeB r = true)
    (hty : keptShapes f₀ = r.kept.map fun i => (r.lo[i]?).map (·.1))
    (sent : List OracleNotice) (hfence : (switchNotices fx.T fx.others).toList = sent)
    (htied : tiedB r.l sent = true) :
    frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧
      K2.SampleGoodS fx.st ∧ storedB r (placeFrame W n0 olds) fx = true ∧
      s.st.oracles = fx.st.oracles := by
  obtain ⟨c1, c2, -⟩ := front_of_state hf
  obtain ⟨w1, w2⟩ := way_tables hway
  obtain ⟨hl, hsh⟩ := kept_of_test h1 hty
  exact ⟨h1, tied_of_sent r.l _ sent hfence htied,
    (K2.sampleGoodS_iff _).2 (K2.rowsInv_congr (Q := K2.QGoodS) (c1.trans w1) (c2.trans w2)
      ((K2.sampleGoodS_iff _).1 hG)),
    storedB_of hlen hsh hl (K2.answered_congr (c2.trans w2) hA) hs, (c2.trans w2).symm⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.way_tables
#print axioms VerifiableInference.Desc.First.K2Caller.kept_of_test
#print axioms VerifiableInference.Desc.First.K2Caller.frontSide_of
