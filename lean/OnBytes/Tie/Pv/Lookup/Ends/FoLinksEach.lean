-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLinksEach.lean.
Link number i of a proof's chain has run the routine of the sub-proof that stands at place i, at the
public record's own arguments, from a context on the view with no message open.

`LinksRan` (OnBytes/Tie/Pv/Lookup/Ends/FoLinks.lean) is a chain: each link's start is the end of the
link before. Here one link
is taken out of the chain, by its place.

 * `LinksRan.at`: for the link at place i of the list there are a state k of the chain's calls and a
   context c0 such that the chain's first call for the link has run from (k, c0) to (k', c1); `Clean
   c1`; and the link's routine has run from the link's state made of k' and of the number l + i,
   from the planned state and from c1. What is lost against `LinksRan`: that (k, c0) is where the
   link before ended.
 * `RanAt X cov Y Fp L c1 C F c2`: by the kind of the link Y: the routine of the layers of group
   `Y.g` at the plan `X.G[Y.g]`, or attention's at `X.A[Y.g]`, or the output head's at X's own
   records, has run from (L, Fp, c1) to (C, F, c2). `ranAt_of`: so it is, if Y is as `KindAt` says
   (OnBytes/Tie/Pv/Lookup/Ends/FoLinksKindAt.lean) and Y's routine has run so.
 * `accepted_at`: if the checker accepts with the links as the verifier runs them, then at each
   place i of that array: `LinksRan.at`'s facts with the number i, and `RanAt` of the link at place
   i of `Verify.linksOf X cov`, from the planned state of the record at place i of the array. The
   premise is the very term of the library's `Verify.wholeCall_passed` and `Verify.requestRun_ok`
   (OnBytes/Model/VerifyLawsWhole.lean). So the statements on a whole routine's run, whose premises
   are that run and `Clean` of the context at its start, apply at every place.

Not said: which kind and group stand at place i; that the record that was built before has, at place
i, the kind and the group of the link of `Verify.linksOf` at that place (`built_bare` in
OnBytes/Tie/Pv/Lookup/Ends/FoBare.lean says that, for the records that `builtOf` returns).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAccepted
import OnBytes.Tie.Pv.Lookup.Ends.FoLinksKindAt

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- One link out of the chain, by its place. A corollary: k and c0 stand under the ∃, so c1 is tied
here to nothing before the link. Whoever needs that this run reads a given view's rounds takes
`LinksRan` itself. -/
theorem LinksRan.at (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay) :
    ∀ (rest : List Stages.LinkH) (l : Nat) (check : ChainCheck) (out : Proof.LinksResult)
      (c : Ctx) (r : (ChainCheck × Proof.LinksResult) × Ctx),
      LinksRan links p wsLay rest l check out c r →
      ∀ (i : Nat) (hi : i < rest.length), ∃ (k k' : ChainCheck) (c0 c1 c2 : Ctx)
        (o : Option WsForkOut) (C : LinkCtx) (F : Fork),
        k.first c0 = .ok (k', c1) ∧ Clean c1 ∧
        (rest[i]).run { check := k', link := l + i, arrayOf := (rest[i]).arrayOf,
                        list := (rest[i]).Tp } (rest[i]).Fp c1 = .ok (((o, C), F), c2)
  | [], _, _, _, _, _, _, i, hi => absurd hi (by simp)
  | Y :: rest, l, check, out, c, r, h, i, hi => by
    obtain ⟨k', c1, c2, o, C, F, check1, out1, c3, e0, e1, e2, _, e4⟩ := h
    cases i with
    | zero => exact ⟨check, k', c, c1, c2, o, C, F, e0, e1, e2⟩
    | succ j =>
      have hj : j < rest.length := by simpa using hi
      obtain ⟨k, k2, d0, d1, d2, o', C', F', a0, a1, a2⟩ :=
        LinksRan.at links p wsLay rest (l + 1) check1 out1 c3 r e4 j hj
      refine ⟨k, k2, d0, d1, d2, o', C', F', a0, a1, ?_⟩
      rw [show l + (j + 1) = l + 1 + j by omega]
      exact a2

/-- By the kind of the link Y: the routine of the sub-proof that Y holds has run from (L, Fp, c1)
to (C, F, c2). -/
def RanAt (X : Verify.Public) (cov : Head.Covered) (Y : Stages.LinkH) (Fp : Fork) (L : LinkCtx)
    (c1 : Ctx) (C : LinkCtx) (F : Fork) (c2 : Ctx) : Prop :=
  (Y.kind = 0 ∧ ∃ hp w, X.G[Y.g]? = some hp ∧
    Layer.runForkHidG2 { X.layers with tokv := cov.tokv } hp Y.g L Fp c1 =
      .ok (((w, C), F), c2)) ∨
  (Y.kind = 1 ∧ ∃ a, X.A[Y.g]? = some a ∧ Attention.run a L Fp c1 = .ok ((((), C), F), c2)) ∨
  (Y.kind = 2 ∧ ∃ w, Head.runForkHidH2 X.hS X.HLy (Verify.borderOf X.y) X.H X.owner cov
    X.layers.wsLay L Fp c1 = .ok (((w, C), F), c2))

theorem ranAt_of (X : Verify.Public) (cov : Head.Covered) (Y : Stages.LinkH)
    (hY : KindAt X cov Y) (Fp : Fork) (L C : LinkCtx) (F : Fork) (c1 c2 : Ctx)
    (o : Option WsForkOut) (h : Y.run L Fp c1 = .ok (((o, C), F), c2)) :
    RanAt X cov Y Fp L c1 C F c2 := by
  rcases hY with ⟨hk, hp, e1, e⟩ | ⟨hk, a, e1, e⟩ | ⟨hk, e⟩
  · rw [e] at h
    obtain ⟨w, _, h'⟩ := some_ok _ _ _ _ _ _ _ _ h
    exact Or.inl ⟨hk, hp, w, e1, h'⟩
  · rw [e] at h
    obtain ⟨_, _, h'⟩ := none_ok _ _ _ _ _ _ _ _ h
    exact Or.inr (Or.inl ⟨hk, a, e1, h'⟩)
  · rw [e] at h
    obtain ⟨w, _, h'⟩ := some_ok _ _ _ _ _ _ _ _ h
    exact Or.inr (Or.inr ⟨hk, w, h'⟩)

/-- The checker's yes: place by place. A corollary: k and c0 stand under the ∃, so c1 is tied here
to nothing of the file. Whoever needs that this run reads this file's rounds takes `accepted_ran`
(OnBytes/Tie/Pv/Lookup/Ends/FoAccepted.lean). -/
theorem accepted_at (X : Verify.Public) (cov : Head.Covered) (links built : Array Stages.LinkH)
    (hl : Verify.linksOf X cov = .ok links) (c : Params.ProofChains) (table : Params.TableName)
    (copy : Nat) (request words : ByteArray) (reply : E) (wsLay : WsLay) (file : ByteArray)
    (h : Proof.check c table copy request words reply
      (Stages.runLinksH (built.zipWith (fun b l => { b with run := l.run }) links) c.first wsLay)
      file = .accepted) (i : Nat) (hb : i < built.size) (hi : i < links.size) :
    ∃ (k k' : ChainCheck) (c0 c1 c2 : Ctx) (C : LinkCtx) (F : Fork),
      k.first c0 = .ok (k', c1) ∧ Clean c1 ∧
      RanAt X cov (links[i]) (built[i]).Fp
        { check := k', link := i, arrayOf := (built[i]).arrayOf, list := (built[i]).Tp } c1
        C F c2 := by
  obtain ⟨_, _, _, _, _, _, _, _, hr, _⟩ :=
    accepted_ran X cov links built hl c table copy request words reply wsLay file h
  have hz : i < (built.zipWith (fun (b l : Stages.LinkH) => { b with run := l.run })
      links).toList.length := by
    simp only [Array.length_toList, Array.size_zipWith]
    omega
  obtain ⟨k, k', c0, c1, c2, o, C, F, e0, e1, e2⟩ := LinksRan.at _ _ _ _ _ _ _ _ _ hr i hz
  simp only [Array.getElem_toList, Array.getElem_zipWith, Nat.zero_add] at e2
  exact ⟨k, k', c0, c1, c2, C, F, e0, e1,
    ranAt_of X cov _ (linksOf_kindAt X cov links hl _ (Array.getElem_mem_toList hi))
      _ _ _ _ _ _ o e2⟩

end Fo
