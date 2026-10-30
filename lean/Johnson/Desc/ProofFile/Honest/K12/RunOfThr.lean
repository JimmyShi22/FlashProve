--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/RunOfThr.lean: WHAT "THE MEMBER PLAYS" ASKS WHERE THE THREAD HOLDS
IN FRONT (`RunPlays`, PlaysK12.lean in this folder) FROM THE FRAME's THREAD ITSELF (`Thr`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean), A TEST ON THE BOOK, AND PREMISES ON THE THREAD's
LETTERS AND ON THE JOB THAT NAME NO RUN. General in the thread; where the first fold's fresh table
has come earlier. Statements and proofs.

  `agree_of_ties'`   `agree_of_ties` (AgreeBook.lean) at a job that is a letter, with its word on
                 the fresh table as a premise
  `words_of_hand`   a tree that is at hand as the thread says has as many words as the thread's
                 table
  `WideAt`       ON THE THREAD's LETTERS: each old source that the test's declared rounds open is at
                 hand at the border, and the thread's table behind it has the declared width,
                 wherever a letter A holds
  **`runPlays_of_thr`**   a letter A holds that gives the thread in front of the member · the row
                 of the two parts is lent its coins · `tiesB` at the book · k = h + g at the first
                 stage · the first stage's message reads the job's members' stretches alone ·
                 `WideAt` ⟹ `RunPlays` at the number of trees that the chain's members in front
                 state

Limits. `tiesB`, the clause on the job's rows and `WideAt` are asked. Of the thread two clauses are
spent: the trees at hand and the count of trees sent. WHY A LETTER: beside tables that are those of
the frame's own play (`tableBy`, Johnson/Desc/ProofFile/Honest/Small/PlayedTo.lean) the width cannot
be had from the thread alone: such a table falls to a default where the play fails; the pair of the
thread and "the run stands where the play stands" shuts that out: A is meant to be that pair.
Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import Johnson.Desc.ProofFile.Honest.Thread.Sent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- `agree_of_ties` at a job that is a letter. -/
theorem agree_of_ties' (J : TestJob W X) (f : Addr × ℕ) (hfr : J.fresh = some f) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (h : lendRow B rows look J.p.place [(firstPart J : Part V W X), restPart J] 0 = .ok c) (w : W)
    (fr : Front X) (hT : tiesB B J.p.place J.members.length = true)
    (hk : J.s₀.k = (sgOf J.s₀).h + (sgOf J.s₀).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf J.s₀) (J.rows₀ w fr mem) = μOf (sgOf J.s₀) (J.rows₀ w fr mem')) :
    Agree J w fr J.s₀ (firstRd J c.1) (restCoins J c.2.1) := by
  cases J with
  | mk p ms fresh r ro tr =>
    have e : fresh = some f := hfr
    subst e
    exact agree_of_ties p ms f r ro tr B rows look c h w fr hT hk hrows

/-- A tree that is at hand as the thread says has as many words as the thread's table. -/
theorem words_of_hand (T : Thread Bk S Cl V W X Pb) {σ : Fmt.TreeSource} {k : Coins Bk} {m : Mid W X}
    {E : Env} (h : T.handAt σ k m E = true) :
    ∃ pt, E.tree σ = some pt ∧ pt.2.words = (T.tableAt σ k m).2.words := by
  obtain ⟨pt, hE, -, hs⟩ := T.handAt_elim h
  unfold Table.same at hs
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  exact ⟨pt, hE, beq_iff_eq.1 hs.1.2⟩

/-- **On the thread's letters.** -/
def WideAt (T : Thread Bk S Cl V W X Pb) (A : Coins Bk → S → Mid W X → Env → Prop) (b : ℕ)
    (J : TestJob W X) : Prop :=
  ∀ d ∈ (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds, ∀ o ∈ d.opens,
    oldSrc (treesTo T.bs b) o.2 = true →
    o.2 ∈ T.hand b ∧ ∀ k st m E, A k st m E → (T.tableAt o.2 k m).2.words = o.1.W

/-- **`RunPlays` from the thread in front.** -/
theorem runPlays_of_thr (T : Thread Bk S Cl V W X Pb) (b : ℕ)
    (A : Coins Bk → S → Mid W X → Env → Prop) (hAT : ∀ k st m E, A k st m E → Thr T b k st m E)
    (J : TestJob W X) (f : Addr × ℕ) (hfr : J.fresh = some f)
    (hT : tiesB Bk J.p.place J.members.length = true)
    (hk : J.s₀.k = (sgOf J.s₀).h + (sgOf J.s₀).g)
    (hrows : ∀ (w : W) (fr : Front X) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf J.s₀) (J.rows₀ w fr mem) = μOf (sgOf J.s₀) (J.rows₀ w fr mem'))
    (hW : WideAt T A b J) (k : Coins Bk) (st : S) (m : Mid W X) (E : Env)
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) (hA : A k st m E)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c) :
    RunPlays J (treesTo T.bs b) m E c := by
  obtain ⟨⟨-, hH⟩, -, -, -, ⟨-, -, hsent, -⟩, -, -⟩ := hAT k st m E hA
  refine ⟨agree_of_ties' J f hfr Bk _ _ c hc _ _ hT hk (hrows _ _), hsent, fun d hd o ho hO => ?_⟩
  rw [hsent] at hO
  obtain ⟨hin, hw⟩ := hW d hd o ho hO
  obtain ⟨pt, h1, h2⟩ := words_of_hand T (hH o.2 hin)
  exact ⟨pt, h1, h2.trans (hw k st m E hA)⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.agree_of_ties'
#print axioms ProofFile.Honest.K12.words_of_hand
#print axioms ProofFile.Honest.K12.runPlays_of_thr
