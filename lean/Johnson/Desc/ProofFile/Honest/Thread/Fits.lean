-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Fits.lean: THE TESTS WITH CODE ON A THREAD's LETTERS
(`Thread.fits`, Honest/Thread/Thr.lean), CUT INTO THEIR FIVE CONJUNCTS, each as a sentence: so that
`Sits.fits` (Honest/Thread/File.lean) need not be evaluated whole at a description that is too large
for that. One small lemma on lists; one lemma general in the thread. No definition.

  `map_eq_of_zip`   two lists of one length whose members agree pair by pair under two functions
  `Thread.fits_of`

THE FIVE, AND WHO CAN PAY EACH.
  (i)   whatever one of the first n rows asks or shuts is open in front of it (`fwdFit`): written
        lists alone: a test with code
  (ii)  each member states a list of oracle messages for each round, one message a root: FOLLOWS
        FROM THE PLAN's OWN TEST `shaped` AT EVERY MEMBER (`shaped_parts`, Honest/Law/Data.lean),
        which `planOk_all` (Honest/Thread/File.lean) has off F.planOk: NO EVALUATION
  (iii) no tree that is taken over has an own tree's source: a sentence on the letter taken
  (iv)  a tree that is at hand at a border is fixed by the challenges heard there: A PREMISE ON THE
        LETTER fixed: it stays named
  (v)   near ≤ front

The converse of (iv) and (v) is `Thread.fits_parts` (Honest/Thread/PaysLaw.lean).

Limits. A conditional lemma on our own definitions. None is one of the library's goals. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.ProofFile.Honest.Law.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

/-- Two lists of one length whose members agree pair by pair under two functions have one image. -/
theorem map_eq_of_zip {α β γ : Type} (f : α → γ) (g : β → γ) : ∀ (l₁ : List α) (l₂ : List β),
    l₁.length = l₂.length → (∀ z ∈ l₁.zip l₂, f z.1 = g z.2) → l₁.map f = l₂.map g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l₁, b :: l₂, h, hz => by
    have h0 : f a = g b := hz (a, b) List.mem_cons_self
    have ih := map_eq_of_zip f g l₁ l₂ (Nat.succ.inj h)
      fun z hz' => hz z (List.mem_cons_of_mem _ hz')
    rw [List.map_cons, List.map_cons, h0, ih]

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **THE TESTS ON THE LETTERS, FROM THEIR FIVE CONJUNCTS.** -/
theorem Thread.fits_of {n : Nat} (h1 : fwdFit T.start T.row n = true)
    (h2 : ∀ z ∈ T.bs, z.shaped = true) (h3 : ∀ σ ∈ T.taken, ∃ c j, σ = Fmt.TreeSource.taken c j)
    (h4 : ∀ b, b ≤ n → ∀ σ ∈ T.hand b, T.fixed σ ≤ T.front + roundsTo T.bs b)
    (h5 : T.near ≤ T.front) : T.fits n = true := by
  unfold Thread.fits
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩, decide_eq_true h5⟩
  · refine List.all_eq_true.2 fun z hz => ?_
    obtain ⟨e1, e2⟩ := shaped_parts (h2 z hz)
    show (z.rounds.length == z.oracles.length &&
      z.rounds.map (·.entry.roots) == z.oracles.map (·.length)) = true
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    exact ⟨e1.symm, map_eq_of_zip _ _ _ _ e1.symm fun y hy => (e2 y hy).symm⟩
  · refine List.all_eq_true.2 fun σ hσ => ?_
    obtain ⟨c, j, rfl⟩ := h3 σ hσ
    rfl
  · exact List.all_eq_true.2 fun b hb => List.all_eq_true.2 fun σ hσ =>
      decide_eq_true (h4 b (Nat.le_of_lt_succ (List.mem_range.1 hb)) σ hσ)

end ProofFile.Honest

#print axioms ProofFile.Honest.map_eq_of_zip
#print axioms ProofFile.Honest.Thread.fits_of
