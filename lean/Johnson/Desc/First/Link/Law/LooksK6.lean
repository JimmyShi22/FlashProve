-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksK6.lean: THE OUTPUT HEAD's OWN ROUNDS (kind K6) HAND ON «THE
LEDGER's
ARRAYS HAVE THE PLAN's SHAPES»: K6's share of the walk of
Johnson/Desc/First/Link/Law/LooksWalk.lean. Theorems. No text already in the library turns.

  `setHeard_ctx`: where the seat's laying of what was heard returns: of the head's own part the mark
    "opened", the ledger and THE LINK's CONTEXT are left (`setHeard_ok`,
    Johnson/Desc/Kinds/Law/HeardAt.lean, proof for proof, with the context beside).
  `k6_reads`: an accepting decision: a ledger and a link were open in front; behind, a ledger is
    open, and the same context.
  `k6_steps`: **(blockAt h iU3 work l).Steps (KeepsLooks shOf)**: with `blockAt_trees`
    (Johnson/Desc/Kinds/Law/KeepsTrees.lean: the decision leaves the ledger's list of arrays).
  `k6_steps_of`, `k6_steps_seated`: so of `blockOf W l`'s value and of the sub-protocol as a lot
  seats
    it (`seatedClaims W l ms`).
Limits. THE DECISION ALONE: nothing on this sub-protocol's four runs of claims (these are the
batching's runs' share). Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.Kinds.Law.KeepsTrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law

/-- Of the head's own part the mark "opened", the ledger and the link's context are left. -/
theorem setHeard_ctx (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) {s s2 : S} {H : HeardAll}
    (e : (seatAt h iU3).setHeard s H = .ok s2) :
    ∃ (o o' : VerifiableInference.Desc.First.HeadOwn), s.here = .head o ∧
      s2 = { s with here := .head o' } ∧ o'.opened = o.opened ∧ o'.F = o.F ∧ o'.L = o.L := by
  unfold seatAt at e
  dsimp only at e
  split at e
  · rename_i o ho
    split at e
    · simp only [Except.ok.injEq] at e
      exact ⟨o, _, ho, e.symm, rfl, rfl, rfl⟩
    · cases e
  · cases e

/-- What an accepting decision reads in front and behind. -/
theorem k6_reads (h : OnBytes.Model.Head.Shape) (iU3 work l : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ F0 F' L, s.fork? = some F0 ∧ s.link? = some L ∧ s'.fork? = some F' ∧ s'.link? = some L := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, _, e1, e2, hs⟩ := decideBy_spec hd'
  have e1' : s.putFork? F = .ok s1 := e1
  have hs1 := putFork?_ok e1'
  have hsome : s.fork?.isSome = true := by
    unfold S.putFork? at e1'
    split at e1'
    · assumption
    · cases e1'
  obtain ⟨o, o', ho, rfl, hq, hF, hL⟩ := setHeard_ctx h iU3 e2
  have hs' : s' = { s1 with here := .head o' } := hs
  subst hs1
  cases hh : s.here with
  | head a =>
    by_cases hop : a.opened = true
    · simp only [S.putFork, hh, hop, if_true] at ho
      simp only [VerifiableInference.Desc.First.Here.head.injEq] at ho
      subst ho
      refine ⟨a.F, F, a.L, by simp [S.fork?, hh, hop], by simp [S.link?, hh, hop], ?_, ?_⟩
      · rw [hs']
        simp [S.fork?, hq, hF]
      · rw [hs']
        simp [S.link?, hq, hL]
    · simp [S.fork?, hh, hop] at hsome
  | lay a => simp [S.putFork, hh] at ho
  | att a => simp [S.putFork, hh] at ho
  | between => simp [S.fork?, hh] at hsome
  | fin a => simp [S.fork?, hh] at hsome
  | mem a => simp [S.fork?, hh] at hsome

/-- **K6: the output head's own rounds.** -/
theorem k6_steps (shOf : ℕ → List Look) (h : OnBytes.Model.Head.Shape) (iU3 work l : ℕ) :
    (blockAt h iU3 work l).Steps (KeepsLooks shOf) := by
  intro s rs gs s' hd
  obtain ⟨F0, F', L, a1, a2, a3, a4⟩ := k6_reads h iU3 work l s s' rs gs hd
  have ht : (s'.fork?.getD {}).trees = (s.fork?.getD {}).trees :=
    blockAt_trees h iU3 work l s s' rs gs hd
  rw [a1, a3] at ht
  refine keeps_of_cases shOf fun G' L' hG hL' => Or.inr ⟨F0, L, a1, a2, ?_, ?_⟩
  · rw [Option.some.inj (a4.symm.trans hL')]
  · rw [← Option.some.inj (a3.symm.trans hG)]
    exact congrArg (·.map look) ht

/-- So of `blockOf`'s value. -/
theorem k6_steps_of (shOf : ℕ → List Look) (W : OnBytes.Model.Verify.Public) (l : ℕ)
    (b : Block S Unit) (hb : blockOf W l = some b) : b.Steps (KeepsLooks shOf) := by
  unfold blockOf at hb
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact k6_steps shOf _ _ _ _

/-- **So of the sub-protocol as a lot seats it.** -/
theorem k6_steps_seated (shOf : ℕ → List Look) {W : OnBytes.Model.Verify.Public} {l : ℕ}
    {ms : List (ℕ × ℕ)} {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    b.Steps (KeepsLooks shOf) := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  intro s rs gs s' hd
  exact k6_steps shOf W.hS i _ l s rs gs s' ((tested_decide _ _ _ _ _ _ _ _).1 hd).1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.setHeard_ctx
#print axioms VerifiableInference.Desc.LinkJoin.k6_reads
#print axioms VerifiableInference.Desc.LinkJoin.k6_steps
#print axioms VerifiableInference.Desc.LinkJoin.k6_steps_of
#print axioms VerifiableInference.Desc.LinkJoin.k6_steps_seated
