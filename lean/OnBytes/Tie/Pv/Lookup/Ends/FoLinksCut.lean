-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLinksCut.lean.
One link out of the chain of a proof's links, with the chain before it and the chain behind it.

`LinksRan` (OnBytes/Tie/Pv/Lookup/Ends/FoLinks.lean) is a chain: each link's start is the end of the
link before. `LinksRan.at`
(OnBytes/Tie/Pv/Lookup/Ends/FoLinksEach.lean) takes one link out and lets go of the chain. Here the
chain is kept.

 * `LinksRan.cut`: for the link at place i of the list: the links before it have run, from the
   chain's own start to mid (`LinksRan` of the first i links); the chain's first call for the link
   has run from mid's state of the chain's calls and mid's context, to (k', c1); `Clean c1`; the
   link's routine has run from the link's state made of k' and of the number l + i, from the planned
   state and from c1; `runLinkH` has run from mid to nxt; and the links behind it have run from nxt
   to the chain's own end r (`LinksRan` of the others). Every witness is fixed by a run equation, or
   by a chain of them, whose start is named.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLinks

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem LinksRan.cut (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay) :
    ∀ (rest : List Stages.LinkH) (l : Nat) (check : ChainCheck) (out : Proof.LinksResult)
      (c : Ctx) (r : (ChainCheck × Proof.LinksResult) × Ctx),
      LinksRan links p wsLay rest l check out c r →
      ∀ (i : Nat) (hi : i < rest.length),
        ∃ (mid nxt : (ChainCheck × Proof.LinksResult) × Ctx) (k' : ChainCheck) (c1 c2 : Ctx)
          (o : Option WsForkOut) (C : LinkCtx) (F : Fork),
          LinksRan links p wsLay (rest.take i) l check out c mid ∧
          mid.1.1.first mid.2 = .ok (k', c1) ∧ Clean c1 ∧
          (rest[i]).run { check := k', link := l + i, arrayOf := (rest[i]).arrayOf,
                          list := (rest[i]).Tp } (rest[i]).Fp c1 = .ok (((o, C), F), c2) ∧
          Stages.runLinkH links p wsLay (l + i) (rest[i]) mid.1.1 mid.1.2 mid.2 = .ok nxt ∧
          LinksRan links p wsLay (rest.drop (i + 1)) (l + i + 1) nxt.1.1 nxt.1.2 nxt.2 r
  | [], _, _, _, _, _, _, i, hi => absurd hi (by simp)
  | Y :: rest, l, check, out, c, r, h, i, hi => by
    obtain ⟨k', c1, c2, o, C, F, check1, out1, c3, e0, e1, e2, e3, e4⟩ := h
    cases i with
    | zero =>
      exact ⟨((check, out), c), ((check1, out1), c3), k', c1, c2, o, C, F, rfl, e0, e1, e2, e3, e4⟩
    | succ j =>
      have hj : j < rest.length := by simpa using hi
      obtain ⟨mid, nxt, q', d1, d2, o', C', F', a0, a1, a2, a3, a4, a5⟩ :=
        LinksRan.cut links p wsLay rest (l + 1) check1 out1 c3 r e4 j hj
      have el : l + (j + 1) = l + 1 + j := by omega
      refine ⟨mid, nxt, q', d1, d2, o', C', F', ?_, a1, a2, ?_, ?_, ?_⟩
      · exact ⟨k', c1, c2, o, C, F, check1, out1, c3, e0, e1, e2, e3, a0⟩
      · rw [el]
        exact a3
      · rw [el]
        exact a4
      · rw [el]
        exact a5

end Fo
