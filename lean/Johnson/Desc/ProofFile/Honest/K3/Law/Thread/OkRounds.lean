-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/OkRounds.lean: the honest side of the kind "lookup"
(K3): the words of a course's rounds are below the prime: the library's test `okRoundsE`
(Johnson/Top/H/K3LawKind.lean) accepts on them. Theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `okGot_said`: an item that was said, as a view shows it, has its words below the prime.
  `ok_aloneFrom`, `ok_stage`, `ok_run`: hence so has every item of a part's rounds; of a stage's; of
    stages in a row.
  `ok_drawn`: so has every element of challenges that pass the frame's test.
  `okRounds_course`: conditional on `Fit` (Honest/K3/Law/Statements.lean), `okRoundsE` accepts on
    the course's rounds.
  `okRounds_noDigest`: and on them without their digests. On a front part of them: the library's
    `okRoundsE_take` (Johnson/Desc/First/Look/K3DigitsSeatedYes.lean).

Hypotheses that remain.
  `hF`, `h`: (in `okRounds_course`) `Fit R`; the course's rounds return.

How the proof goes. What a part says is an element of the field, and the frame writes it into the
words below the prime that are read as it (`Said.got`, Honest/Frame.lean), whatever the part
computed. What is sampled passes the frame's test on challenges (`drawsFit`, there), which asks that
of every word.

Imported, through Honest/K3/Law/CutOf.lean: Honest/Frame.lean and the files under Honest/SumLaw/.

Users. Honest/K3/Law/Thread/OkPlayed.lean calls `okGot_said` and `ok_drawn`;
Honest/K3/Law/Thread/BehindStep.lean calls `okRounds_course` and `okRounds_noDigest`.

Limits. No instance of these hypotheses is exhibited in this file. The courses of
Honest/K3/Law/Members.lean pass the test for `Fit`, by evaluation.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.CutOf
import Johnson.Top.H.K3LawKind
import Johnson.Desc.BlockSlotProofs
import OnBytes.Slice.KeyOfRecBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E okE okF)
open OnBytes.Maker (okGot)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.OnPublicFiles (okRoundsE)
open ProofFile.Honest.SumLaw (alone aloneFrom)
open ProofFile.Honest.K3.Law

variable {W : Type}

/-- An item that was said, as a view shows it, has its words below the prime. -/
theorem okGot_said (y : Said) : okGot y.got = true := by
  cases y with
  | f x =>
    show okF (OnBytes.Slice.ofF x) = true
    rw [OnBytes.okF_eq]
    exact OnBytes.Slice.ok_ofF x
  | e x => exact OnBytes.Slice.okE_writeE x
  | word x => rfl
  | answer x => exact OnBytes.Slice.okE_writeE x

theorem ok_aloneFrom {Cn X : Type} (c : Cn) : ∀ (mvs : List (Move Cn W X)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (y : List Fmt.RoundView),
    aloneFrom c mvs t seen ds = some y → ∀ r ∈ y, r.vals.all okGot = true
  | [], _, _, [], y, h => by
    simp only [aloneFrom, Option.some.injEq] at h
    subst h
    intro r hr
    simp at hr
  | [], _, _, _ :: _, y, h => by simp [aloneFrom] at h
  | _ :: _, _, _, [], y, h => by simp [aloneFrom] at h
  | mv :: mvs, t, seen, d :: ds, y, h => by
    unfold aloneFrom at h
    split at h
    · dsimp only at h
      obtain ⟨y', hy', e⟩ := Option.map_eq_some_iff.1 h
      have ih := ok_aloneFrom c mvs _ _ _ _ hy'
      subst e
      intro r hr
      rcases List.mem_cons.1 hr with h1 | h1
      · rw [h1, List.all_eq_true]
        intro g hg
        obtain ⟨z, _, rfl⟩ := List.mem_map.1 hg
        exact okGot_said z
      · exact ih r h1
    · cases h

theorem ok_stage (R : Course W) {s : Stage} {t : State W Unit} {seen : Seen}
    {d : List Fmt.Drawn} {y : List Fmt.RoundView} (h : R.stage s t seen d = some y) :
    ∀ r ∈ y, r.vals.all okGot = true := by
  unfold Course.stage at h
  split at h
  · exact ok_aloneFrom _ _ _ _ _ _ h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      intro r hr
      obtain rfl : r = _ := by simpa using hr
      rfl
    · cases h

theorem ok_run (R : Course W) : ∀ (l : List Stage) (t : State W Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (x : List Fmt.RoundView), R.run l t seen ds = some x →
    ∀ r ∈ x, r.vals.all okGot = true
  | [], _, _, [], x, h => by
    simp only [Course.run, Option.some.injEq] at h
    subst h
    intro r hr
    simp at hr
  | [], _, _, _ :: _, x, h => by simp [Course.run] at h
  | s :: l, t, seen, ds, x, h => by
    unfold Course.run at h
    obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z, hz, e⟩ := Option.map_eq_some_iff.1 h2
    subst e
    intro r hr
    rcases List.mem_append.1 hr with h1 | h1
    · exact ok_stage R hy r h1
    · exact ok_run R l _ _ _ _ hz r h1

/-- Every element of challenges that pass the frame's test has its words below the prime. -/
theorem ok_drawn : ∀ (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit zs ds = true →
    ∀ D ∈ ds, (D.elems.all fun x => okE (E.ofTriple x)) = true
  | [], [], _ => by simp
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | z :: zs, d :: ds, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    intro D hD
    rcases List.mem_cons.1 hD with hD | hD
    · subst hD
      have h1 := h.1
      simp only [drawFit, Bool.and_eq_true] at h1
      have h2 := h1.1.2
      rw [List.all_eq_true] at h2 ⊢
      intro x hx
      have h3 := h2 x hx
      have e : okE (E.ofTriple x) = okGot (.e x) := rfl
      rw [e, VerifiableInference.Desc.okGot_eq]
      simpa using h3
    · exact ok_drawn zs ds h.2 D hD

/-- **The words of the course's rounds are below the prime.** Conditional on `Fit`. No instance of
these hypotheses is exhibited in this file. -/
theorem okRounds_course (R : Course W) (x : List Fmt.RoundView) (hF : Fit R) (h : R.rounds = some x) :
    okRoundsE x = true := by
  have hv := ok_run R _ _ _ _ _ h
  have hd := (cut_run R _ _ _ _ _ h).1
  have hw := ok_drawn _ _ hF.draws
  unfold okRoundsE
  rw [List.all_eq_true]
  intro r hr
  rw [Bool.and_eq_true]
  refine ⟨hv r hr, hw r.drawn ?_⟩
  rw [← hd]
  exact List.mem_map.2 ⟨r, hr, rfl⟩

/-- The test reads no digest. -/
theorem okRounds_noDigest (x : List Fmt.RoundView) (h : okRoundsE x = true) :
    okRoundsE (x.map noDigest) = true := by
  unfold okRoundsE at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
  exact h r' hr'

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.okGot_said
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_aloneFrom
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_stage
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_run
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_drawn
#print axioms ProofFile.Honest.K3.Law.AtThr.okRounds_course
#print axioms ProofFile.Honest.K3.Law.AtThr.okRounds_noDigest
