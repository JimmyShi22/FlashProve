-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/BehindChain.lean: THE SUB-PROTOCOL WITHOUT A ROUND "behind the
batching" of a link (Link.runBehind, Johnson/Desc/Block.lean): what its decision is, run by run;
and, where its runs are the smallness test's two, one step on the shape of the first chain's state
(chainSh, Johnson/Desc/First/Shape/Chain.lean) with its two laws. General laws; nothing is
evaluated.

The decision asks the link's tests behind the adding, which cannot turn the state, and then the runs
that the link's order names, each at the state that the one before has left. The protocol's orders
(orderAfterOf, Johnson/Desc/First/Driver/Chain.lean): an attention link and the output head's link:
"K8.lsTail", "K8.tests"; a layers' link: "K8.lsTail", "free-slot", "K8.tests".

  `runBehind_two`, `runBehind_three`: for a link whose order names two | three runs: the decision
    accepts from s to s' just if the tests accept at s and the runs accept in a row from s to s'.
    General in the state and in the link.
  `guarded_after_iff`: a run of a sub-protocol under the wrapper Block.guarded
    (Johnson/Desc/SeatGuard.lean) accepts just where the bare run accepts and the wrapper's
    comparison of the two states accepts.
  `K8Runs bs i p same r₁ r₂`: what the list bs states at number i under the two names are the runs
    of K8.whole p under that wrapper.
  `behindG gT nU`: the step on the shape: a test gT for the link's tests; then lsTailG; then testsGC
    (Johnson/Desc/First/TailClaims/TestsChain.lean).
  **`behind_carries`**: the decision accepts from s to s', and behindG returns t at chainSh s: then
    t = chainSh s'.
  **`behind_returns`**: behindG returns at chainSh s · the link's tests accept wherever gT and a
    test vT on values accept (A PREMISE: another house's law) · the wrapper's comparison accepts a
    state against the same state with the smallness test's part laid anew (A PREMISE on the
    wrapper) · vT accepts at s · the smallness test's tests on values accept at the state behind
    "K8.lsTail": then the decision accepts.

Limits. THE TWO-RUN ORDER ALONE has the step and its laws here: at a layers' link "free-slot" stands
between the two runs: runBehind_three cuts the decision there; the step is BehindLayers.lean's, with
the run in the middle, its step and its two laws as letters and premises. That a description's link
has such an order, and K8.whole under that wrapper at i, is not said here. That behindG returns at a
shape of the protocol is not shown. behind_returns asks its two marked premises at every state; its
proof spends the first at s alone, the second at s and at one state made of s. guarded_after_iff has
no caller. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.TestsChain
import Johnson.Desc.First.TailClaims.K8SitsLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (partOf afterIn_cons afterIn_cons_of
  lookup_map_snd sits_lsTail sits_tests)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)

/-! ## 1 The decision, run by run -/

section General
variable {T Cl : Type}

theorem runBehind_iff (L : Link T Cl) (s s' : T) :
    L.runBehind s = .ok s' ↔ L.tests s = .ok () ∧ afterIn L.hear L.orderAfter s = .ok s' := by
  unfold Link.runBehind
  cases L.tests s with
  | ok u => exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  | error e => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩

theorem runBehind_two {L : Link T Cl} {o₁ o₂ : Nat × String} {r₁ r₂ : T → Except String T}
    (ho : L.orderAfter = [o₁, o₂])
    (h₁ : ((L.hear[o₁.1]?).bind fun b => b.after.lookup o₁.2) = some r₁)
    (h₂ : ((L.hear[o₂.1]?).bind fun b => b.after.lookup o₂.2) = some r₂) (s s' : T) :
    L.runBehind s = .ok s' ↔ L.tests s = .ok () ∧ ∃ s₁, r₁ s = .ok s₁ ∧ r₂ s₁ = .ok s' := by
  rw [runBehind_iff, ho]
  constructor
  · rintro ⟨ht, h⟩
    obtain ⟨u₁, s₁, e₁, a₁, h⟩ := afterIn_cons h
    obtain ⟨u₂, s₂, e₂, a₂, h⟩ := afterIn_cons h
    obtain rfl := Option.some.inj (h₁.symm.trans e₁)
    obtain rfl := Option.some.inj (h₂.symm.trans e₂)
    obtain rfl : s₂ = s' := Except.ok.inj h
    exact ⟨ht, s₁, a₁, a₂⟩
  · rintro ⟨ht, s₁, a₁, a₂⟩
    exact ⟨ht, afterIn_cons_of h₁ a₁ (afterIn_cons_of h₂ a₂ rfl)⟩

theorem runBehind_three {L : Link T Cl} {o₁ o₂ o₃ : Nat × String}
    {r₁ r₂ r₃ : T → Except String T} (ho : L.orderAfter = [o₁, o₂, o₃])
    (h₁ : ((L.hear[o₁.1]?).bind fun b => b.after.lookup o₁.2) = some r₁)
    (h₂ : ((L.hear[o₂.1]?).bind fun b => b.after.lookup o₂.2) = some r₂)
    (h₃ : ((L.hear[o₃.1]?).bind fun b => b.after.lookup o₃.2) = some r₃) (s s' : T) :
    L.runBehind s = .ok s' ↔
      L.tests s = .ok () ∧ ∃ s₁ s₂, r₁ s = .ok s₁ ∧ r₂ s₁ = .ok s₂ ∧ r₃ s₂ = .ok s' := by
  rw [runBehind_iff, ho]
  constructor
  · rintro ⟨ht, h⟩
    obtain ⟨u₁, s₁, e₁, a₁, h⟩ := afterIn_cons h
    obtain ⟨u₂, s₂, e₂, a₂, h⟩ := afterIn_cons h
    obtain ⟨u₃, s₃, e₃, a₃, h⟩ := afterIn_cons h
    obtain rfl := Option.some.inj (h₁.symm.trans e₁)
    obtain rfl := Option.some.inj (h₂.symm.trans e₂)
    obtain rfl := Option.some.inj (h₃.symm.trans e₃)
    obtain rfl : s₃ = s' := Except.ok.inj h
    exact ⟨ht, s₁, s₂, a₁, a₂, a₃⟩
  · rintro ⟨ht, s₁, s₂, a₁, a₂, a₃⟩
    exact ⟨ht, afterIn_cons_of h₁ a₁ (afterIn_cons_of h₂ a₂ (afterIn_cons_of h₃ a₃ rfl))⟩

end General

/-! ## 2 Under the wrapper -/

/-- A run under the wrapper accepts just where the bare run and the wrapper's comparison accept. -/
theorem guarded_after_iff (same : S → S → Bool) (but : Place → Bool) (b : Block S Claim)
    (k : String) (r' : S → Except String S) (h : (b.guarded same but).after.lookup k = some r') :
    ∃ r, b.after.lookup k = some r ∧ (k, r) ∈ b.after ∧
      ∀ t y, r' t = .ok y ↔ r t = .ok y ∧ same t y = true := by
  obtain ⟨r, hl, hr, rfl⟩ := lookup_map_snd
    (fun (c : S → Except String S) t => (c t).bind (seatSame same t)) b.after k r' h
  refine ⟨r, hl, hr, fun t y => ?_⟩
  show (r t).bind (seatSame same t) = .ok y ↔ _
  cases hc : r t with
  | error e => exact ⟨fun hy => (nomatch hy), fun hy => (nomatch hy.1)⟩
  | ok y0 =>
    show seatSame same t y0 = .ok y ↔ _
    unfold seatSame
    by_cases hs : same t y0 = true
    · rw [if_pos hs]
      constructor
      · intro hy
        obtain rfl := Except.ok.inj hy
        exact ⟨rfl, hs⟩
      · rintro ⟨hy, -⟩
        exact hy
    · rw [if_neg hs]
      constructor
      · intro hy
        exact nomatch hy
      · rintro ⟨hy, h2⟩
        obtain rfl := Except.ok.inj hy
        exact absurd h2 hs

/-- **What the list states at number i under the two names are K8.whole p's runs, each asked
together with a comparison `same` of the states in front and behind.** With same := fun _ _ => true:
the bare runs. -/
structure K8Runs (bs : List (Block S Claim)) (i : Nat) (p : K8.ParW) (same : S → S → Bool)
    (r₁ r₂ : S → Except String S) : Prop where
  look₁ : ((bs[i]?).bind fun b => b.after.lookup "K8.lsTail") = some r₁
  look₂ : ((bs[i]?).bind fun b => b.after.lookup "K8.tests") = some r₂
  bare₁ : ∃ u, ("K8.lsTail", u) ∈ (K8.whole p).after ∧
    ∀ t y, r₁ t = .ok y ↔ u t = .ok y ∧ same t y = true
  bare₂ : ∃ u, ("K8.tests", u) ∈ (K8.whole p).after ∧
    ∀ t y, r₂ t = .ok y ↔ u t = .ok y ∧ same t y = true

/-! ## 3 The step on the shape, at the order of two runs -/

/-- **The step on the shape.** gT: a test on the shape for the link's tests behind the adding. -/
def behindG (gT : ChainSh → Bool) (nU : Array Nat) (a : ChainSh) : Except String ChainSh :=
  if gT a then (lsTailG a).bind (testsGC nU) else .error "the tests behind the adding: the shape"

variable {L : Link S Claim} {i : Nat} {p : K8.ParW} {same : S → S → Bool}
  {r₁ r₂ : S → Except String S} {gT : ChainSh → Bool}

theorem behind_carries (ho : L.orderAfter = [(i, "K8.lsTail"), (i, "K8.tests")])
    (K : K8Runs L.hear i p same r₁ r₂) (s s' : S) (t : ChainSh) (hr : L.runBehind s = .ok s')
    (hg : behindG gT p.nU (chainSh s) = .ok t) : t = chainSh s' := by
  obtain ⟨-, s₁, a₁, a₂⟩ := (runBehind_two ho K.look₁ K.look₂ s s').1 hr
  obtain ⟨u₁, m₁, e₁⟩ := K.bare₁
  obtain ⟨u₂, m₂, e₂⟩ := K.bare₂
  unfold behindG at hg
  by_cases hb : gT (chainSh s) = true
  · rw [if_pos hb] at hg
    cases h1 : lsTailG (chainSh s) with
    | error e => rw [h1] at hg; exact nomatch hg
    | ok t₁ =>
      rw [h1] at hg
      have c₁ := lsTail_carries p u₁ m₁ s s₁ t₁ ((e₁ s s₁).1 a₁).1 h1
      subst c₁
      exact testsC_carries p u₂ m₂ s₁ s' t ((e₂ s₁ s').1 a₂).1 hg
  · rw [if_neg hb] at hg
    exact nomatch hg

theorem behind_returns (ho : L.orderAfter = [(i, "K8.lsTail"), (i, "K8.tests")])
    (K : K8Runs L.hear i p same r₁ r₂) {vT : S → Bool}
    (hT : ∀ s, gT (chainSh s) = true → vT s = true → L.tests s = .ok ())
    (hsame : ∀ (s : S) (q : K8Part), same s (k8PartP.set s q) = true) (s : S) (t : ChainSh)
    (hg : behindG gT p.nU (chainSh s) = .ok t) (hv : vT s = true)
    (hv₂ : ∀ s₁, r₁ s = .ok s₁ → valsS p.nU s₁ = true) : ∃ s', L.runBehind s = .ok s' := by
  obtain ⟨u₁, m₁, e₁⟩ := K.bare₁
  obtain ⟨u₂, m₂, e₂⟩ := K.bare₂
  unfold behindG at hg
  by_cases hb : gT (chainSh s) = true
  · rw [if_pos hb] at hg
    cases h1 : lsTailG (chainSh s) with
    | error e => rw [h1] at hg; exact nomatch hg
    | ok t₁ =>
      rw [h1] at hg
      obtain ⟨s₁, b₁⟩ := lsTail_returns p u₁ m₁ s t₁ h1
      have w₁ : same s s₁ = true := by
        obtain ⟨q, -, rfl⟩ := (sits_lsTail p u₁ m₁ s s₁).1 b₁
        exact hsame s _
      have a₁ : r₁ s = .ok s₁ := (e₁ s s₁).2 ⟨b₁, w₁⟩
      have c₁ := lsTail_carries p u₁ m₁ s s₁ t₁ b₁ h1
      subst c₁
      obtain ⟨s', b₂⟩ := testsC_returns p u₂ m₂ s₁ t hg (hv₂ s₁ a₁)
      have w₂ : same s₁ s' = true := by
        obtain ⟨q, Fc, -, -, rfl⟩ := (sits_tests p u₂ m₂ s₁ s').1 b₂
        exact hsame s₁ _
      exact ⟨s', (runBehind_two ho K.look₁ K.look₂ s s').2
        ⟨hT s hb hv, s₁, a₁, (e₂ s₁ s').2 ⟨b₂, w₂⟩⟩⟩
  · rw [if_neg hb] at hg
    exact nomatch hg

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.runBehind_two
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.runBehind_three
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.guarded_after_iff
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.behind_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.behind_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.runBehind_iff
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.K8Runs
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.behindG
