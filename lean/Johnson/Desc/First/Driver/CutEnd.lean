-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Driver/CutEnd.lean: how the first chain's table of stretches ends; and where the
kind "reply" is written in it.

`cutOf` (Cut.lean) makes the table out of the plan's entries: the links' stretches, the finish's,
and last the members' places and the seal.
Main names:
  `membersCut_eq`: what `membersCut` returns: six stretches at the places pl, q and q + 1, where q
    is pl or pl + 1.
  `cutOf_end`: a table that `cutOf` returns ends in these six.
  `cutOf_last`: its last stretch is the seal's: no round, at the place behind the members'.
  `cutOf_reply`: in such a table a stretch of the kind "reply" has the look "H.0.front" or
    "H.0.call": the first two stretches of the head's link. On the way: `tailCut_reply`,
    `linkCut_reply`, `linksCut_reply`, `stagesCut_reply`, `finishCut_reply`; `ReplyAt`; two small
    tools on `Option` (`ite_some`, `bind_some'`), by which `linkCut`'s text is opened step by step.
Limits: on the text of `cutOf` alone. It writes out again: six of Cut.lean's stretches (`endCuts`),
and the strings "reply", "H.0.front", "H.0.call", "send", "sendLoc": if Cut.lean turns there, this
file goes red or says another thing. That a table HAS a stretch of the kind "reply" is not said; nor
that each look comes once. Of the stretches in front of the last six nothing else; the two numbers
pl and b are not said. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.First.Driver.Cut

set_option autoImplicit false
namespace VerifiableInference.Desc.First

/-- The members' places and the seal, at the places pl, q, q + 1; b: the rounds of the batching. -/
def endCuts (pl q b : Nat) : List Cut :=
  [⟨"M.0.front", "mFront", pl, "batPsc", 0⟩, ⟨"M.0.call", "mBatt", pl, "batPsc", b⟩,
    ⟨"M.0.quiet", "mBattQuiet", pl, "batPsc", 0⟩, ⟨"M.1.call", "mSend", q, "send", 2⟩,
    ⟨"M.1.quiet", "mSendQuiet", q, "send", 0⟩, ⟨"seal.behind", "seal", q + 1, "SEAL", 0⟩]

theorem membersCut_eq {pl : Nat} {ns : List String} {c : List Cut}
    (h : membersCut pl ns = some c) : ∃ q b, c = endCuts pl q b ∧ (q = pl ∨ q = pl + 1) := by
  unfold membersCut at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨b, _, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
  simp only [Option.bind_some] at h
  split at h
  · cases h
  cases h
  refine ⟨if b == 0 then pl else pl + 1, b, rfl, ?_⟩
  split
  · exact .inl rfl
  · exact .inr rfl

/-- **A table that `cutOf` returns ends in the members' places and the seal.** -/
theorem cutOf_end {es : List Fmt.Entry} {cs : List Cut} (h : cutOf es = some cs) :
    ∃ front pl q b, cs = front ++ endCuts pl q b ∧ (q = pl ∨ q = pl + 1) := by
  unfold cutOf at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨⟨a, pl, r₁⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨b, pl', r₂⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  obtain ⟨q, n, rfl, hq⟩ := membersCut_eq hc
  exact ⟨a ++ b, pl', q, n, rfl, hq⟩

/-- Its last stretch is the seal's. -/
theorem cutOf_last {es : List Fmt.Entry} {cs : List Cut} (h : cutOf es = some cs) :
    ∃ q, cs.getLast? = some ⟨"seal.behind", "seal", q + 1, "SEAL", 0⟩ := by
  obtain ⟨front, pl, q, b, rfl, _⟩ := cutOf_end h
  exact ⟨q, by simp [endCuts]⟩

/-! ## Where the kind "reply" is written -/

/-- A stretch of the kind "reply" is one of the head's link's first two. -/
def ReplyAt (c : Cut) : Prop := c.kind = "reply" → c.look = "H.0.front" ∨ c.look = "H.0.call"

theorem replyAt_of_ne {c : Cut} (h : c.kind ≠ "reply") : ReplyAt c := fun e => absurd e h

theorem tailCut_reply {c L : String} {i pl : Nat} {head : Bool} {claims : List (String × String)}
    {ns : List String} {x : List Cut × Nat × List String}
    (h : tailCut c L i pl head claims ns = some x) : ∀ y ∈ x.1, y.kind ≠ "reply" := by
  unfold tailCut at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  split at h
  · cases h
  simp only [Option.bind_some] at h
  obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨m, _, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  intro y hy
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hy
  rcases hy with (((hy | hy) | hy) | hy) | hy
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · split at hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> simp
    · cases hy
  · subst hy
    simp
  · obtain ⟨_, _, rfl⟩ := hy
    simp
  · rcases hy with rfl | rfl <;> simp

theorem ite_some {α : Type} {c : Prop} [Decidable c] {f g : Option α} {x : α}
    (h : (if c then f else g) = some x) : (c ∧ f = some x) ∨ (¬ c ∧ g = some x) := by
  by_cases hc : c
  · exact .inl ⟨hc, by rwa [if_pos hc] at h⟩
  · exact .inr ⟨hc, by rwa [if_neg hc] at h⟩

theorem bind_some' {α β : Type} {o : Option α} {f : α → Option β} {x : β}
    (h : (o >>= f) = some x) : ∃ a, o = some a ∧ f a = some x := Option.bind_eq_some_iff.1 h

theorem fk_ne (c : Prop) [Decidable c] : (if c then "send" else "sendLoc") ≠ "reply" := by
  split <;> decide

theorem linkCut_reply {g a pl : Nat} {ns : List String}
    {x : List Cut × Nat × Nat × Nat × Bool × List String} (h : linkCut g a pl ns = some x) :
    ∀ y ∈ x.1, ReplyAt y := by
  unfold linkCut at h
  dsimp only at h
  rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, h0, _⟩ := bind_some' h
    cases h0
  obtain ⟨_, _, h⟩ := bind_some' h
  obtain ⟨k, _, h⟩ := bind_some' h
  obtain ⟨o, _, h⟩ := bind_some' h
  rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, h0, _⟩ := bind_some' h
    cases h0
  obtain ⟨_, _, h⟩ := bind_some' h
  rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨t, ht, h⟩ := bind_some' h
    cases h
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fun _ => .inl rfl
      · exact fun _ => .inr rfl
      all_goals (refine replyAt_of_ne ?_; first | exact fk_ne _ | (simp; done))
    · exact replyAt_of_ne (tailCut_reply ht y hy)
  rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨sc, _, h⟩ := bind_some' h
    obtain ⟨zr, _, h⟩ := bind_some' h
    rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
    · obtain ⟨_, h0, _⟩ := bind_some' h
      cases h0
    obtain ⟨_, _, h⟩ := bind_some' h
    obtain ⟨t, ht, h⟩ := bind_some' h
    cases h
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (refine replyAt_of_ne ?_; first | exact fk_ne _ | (simp; done))
    · exact replyAt_of_ne (tailCut_reply ht y hy)
  · obtain ⟨t, ht, h⟩ := bind_some' h
    cases h
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      all_goals (refine replyAt_of_ne ?_; first | exact fk_ne _ | (simp; done))
    · exact replyAt_of_ne (tailCut_reply ht y hy)

theorem linksCut_reply : ∀ (fuel g a pl : Nat) (ns : List String)
    (x : List Cut × Nat × List String), linksCut fuel g a pl ns = some x → ∀ y ∈ x.1, ReplyAt y
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, g, a, pl, ns, x, h => by
    unfold linksCut at h
    obtain ⟨⟨rows, g', a', pl', wasHead, rest⟩, hl, h⟩ := bind_some' h
    dsimp only at h
    rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
    · cases h
      exact linkCut_reply hl
    · obtain ⟨⟨more, pl'', rest'⟩, hm, h⟩ := bind_some' h
      cases h
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact linkCut_reply hl y hy
      · exact linksCut_reply fuel g' a' pl' rest _ hm y hy

theorem stagesCut_reply : ∀ (fuel i pl : Nat) (ns : List String)
    (x : List Cut × Nat × List String), stagesCut fuel i pl ns = some x →
    ∀ y ∈ x.1, y.kind ≠ "reply"
  | 0, _, _, _, _, h => by cases h
  | fuel + 1, i, pl, ns, x, h => by
    unfold stagesCut at h
    rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
    · obtain ⟨c, _, h⟩ := bind_some' h
      obtain ⟨⟨more, j, rest⟩, hm, h⟩ := bind_some' h
      cases h
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp
      · exact stagesCut_reply fuel (i + 1) pl _ _ hm y hy
    · cases h
      intro y hy
      cases hy

theorem finishCut_reply {pl : Nat} {ns : List String} {x : List Cut × Nat × List String}
    (h : finishCut pl ns = some x) : ∀ y ∈ x.1, y.kind ≠ "reply" := by
  unfold finishCut at h
  dsimp only at h
  rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, h0, _⟩ := bind_some' h
    cases h0
  obtain ⟨_, _, h⟩ := bind_some' h
  obtain ⟨⟨st, i, rest⟩, hs, h⟩ := bind_some' h
  dsimp only at h
  rcases ite_some h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, h0, _⟩ := bind_some' h
    cases h0
  obtain ⟨_, _, h⟩ := bind_some' h
  cases h
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_append.1 hy with hy | hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact stagesCut_reply _ _ _ _ _ hs y hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    simp

/-- **In a table that `cutOf` returns, a stretch of the kind "reply" is one of the head's link's
first two**: "H.0.front" or "H.0.call". -/
theorem cutOf_reply {es : List Fmt.Entry} {cs : List Cut} (h : cutOf es = some cs) :
    ∀ c ∈ cs, c.kind = "reply" → c.look = "H.0.front" ∨ c.look = "H.0.call" := by
  unfold cutOf at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨⟨a, pl, r₁⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨b, pl', r₂⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  obtain ⟨q, n, rfl, _⟩ := membersCut_eq hc
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · rcases List.mem_append.1 hy with hy | hy
    · exact linksCut_reply _ _ _ _ _ _ ha y hy
    · exact replyAt_of_ne (finishCut_reply hb y hy)
  · refine replyAt_of_ne ?_
    simp only [endCuts, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.cutOf_end
#print axioms VerifiableInference.Desc.First.cutOf_last
#print axioms VerifiableInference.Desc.First.linkCut_reply
#print axioms VerifiableInference.Desc.First.cutOf_reply
