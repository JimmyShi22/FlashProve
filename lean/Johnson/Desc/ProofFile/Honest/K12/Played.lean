-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Played.lean: the messages that the moves of a proximity test's two
parts (Parts.lean) compute one by one are the rounds of `testAll` (Test.lean) at the whole list of
sampled challenges. Statements and proofs. It imports Mathlib.

A move (`moveAt`, Parts.lean) computes round number i of `testAll` at the challenges received so
far, with an empty challenge in the place of each that has not been received. A statement on what a
verifier decides speaks of `testAll` at the sampled challenges of all rounds. This file joins the
two.

  `set_congr`      if two lists have the same entry number i, they still have after entry 0 of both
                   is replaced by one value
  `testAll_causal`   if two families of sampled challenges agree below i, round i of `testAll`
                   shows the same items and sends the same tree at both
  `msgAt_causal`   so the message of round i is the same
  `say_eq`         a move's message, at a state whose last i challenges are the first i of D, is the
                   message of round i at D

By what. `stagesAll_causal` (Johnson/Desc/K12/Honest/Causal.lean).

Limits. The statements hold for every job and all random values, also where a `decide` function of
the description rejects. Nothing on a decision or on the shape of a message. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Desc.K12.Honest.Causal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link (BOut)

variable {W X C : Type}

theorem set_congr {α : Type} (a : α) : ∀ (l l' : List α) (i : ℕ), l[i]? = l'[i]? →
    (l.set 0 a)[i]? = (l'.set 0 a)[i]?
  | [], [], _, _ => rfl
  | [], _ :: _, 0, h => by simp at h
  | [], _ :: _, _ + 1, h => by simpa using h
  | _ :: _, [], 0, h => by simp at h
  | _ :: _, [], _ + 1, h => by simpa using h
  | _ :: _, _ :: _, 0, _ => rfl
  | _ :: _, _ :: _, _ + 1, h => by simpa using h

/-- **What a round of the test shows depends only on the challenges sampled before it.** -/
theorem testAll_causal (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins)
    (D D' : ℕ → Fmt.Drawn) (i : ℕ) (h : ∀ n, n < i → D n = D' n) :
    ((testAll J w fr K D).rs[i]?).map (·.vals) = ((testAll J w fr K D').rs[i]?).map (·.vals) ∧
      (testAll J w fr K D).tr[i]? = (testAll J w fr K D').tr[i]? := by
  unfold testAll
  cases hs : J.p.nums.stages with
  | nil => exact ⟨rfl, rfl⟩
  | cons s rest =>
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i =>
      have h0 : D 0 = D' 0 := h 0 (Nat.succ_pos i)
      have ih := stagesAll_causal J.p (coinsOf (s :: rest) K.hide K.rest) rest 0 s (J.laid.drop 1) 1
        (J.recB w fr (D 0)) (J.first w fr K) (J.trees₀ w fr K.mem (J.first w fr K)) D D' i
        fun n hn => h n (by omega)
      simp only [List.getElem?_cons_succ]
      rw [← h0]
      refine ⟨ih.1, ?_⟩
      by_cases c : J.fresh.isNone = true
      · rw [if_pos c, if_pos c]
        exact set_congr _ _ _ i ih.2
      · rw [if_neg c, if_neg c]
        exact ih.2

/-- **The message of a round depends only on the challenges sampled before it.** -/
theorem msgAt_causal (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins)
    (D D' : ℕ → Fmt.Drawn) (i : ℕ) (h : ∀ n, n < i → D n = D' n) :
    msgAt J w fr K D i = msgAt J w fr K D' i := by
  obtain ⟨h1, h2⟩ := testAll_causal J w fr K D D' i h
  have e1 : ((testAll J w fr K D).rs[i]?).map (fun r => r.vals.filterMap saidOf) =
      ((testAll J w fr K D').rs[i]?).map fun r => r.vals.filterMap saidOf := by
    have := congrArg (Option.map fun v : List Fmt.ItemValue => v.filterMap saidOf) h1
    simpa [Option.map_map, Function.comp_def] using this
  have e2 : (testAll J w fr K D).tr.getD i (fun _ => []) =
      (testAll J w fr K D').tr.getD i fun _ => [] := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h2]
  unfold msgAt
  simp only
  rw [e1, e2]

/-- **A move's message is the round of `testAll` at the whole list of sampled challenges.** t: a
state whose last i challenges are D 0, ..., D (i - 1). -/
theorem say_eq (J : TestJob W X) (rd : C → TestCoins) (i : ℕ) (c : C) (s : Seen) (t : State W X)
    (D : ℕ → Fmt.Drawn) (h : ∀ n, n < i → (t.lately i).getD n ⟨[], [], [], none⟩ = D n) :
    (moveAt J rd i).say c s t = .ok (msgAt J t.input
      ⟨t.heard.take (t.heard.length - i), t.own, s.front i⟩ (rd c) D
      i) :=
  congrArg Except.ok (msgAt_causal J _ _ _ _ D i h)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.set_congr
#print axioms ProofFile.Honest.K12.testAll_causal
#print axioms ProofFile.Honest.K12.msgAt_causal
#print axioms ProofFile.Honest.K12.say_eq
