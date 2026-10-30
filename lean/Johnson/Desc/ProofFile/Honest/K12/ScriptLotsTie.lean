-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ScriptLotsTie.lean: beside ScriptLots.lean: `psAt` IS TIED TO
`testAll`. Four theorems, one of them a helper; no definition.

Why. ScriptLots.lean has two roads to what the test's second part sends. Its lot of trees cuts a
table off `msgAt`, which reads the columns that `testAll` writes. Its lots of messages read the
tables of `psAt`, a recursion written anew there. This file shows that both roads pass through the
same prover's state.

  `tr_split`   a helper: the columns of the whole run of the stages split into a front piece and the
                 columns of `stagesAll` started at stage j, at the state `psAt … j` and the round
                 `roundOf … j`
  `col_is_psAt`   the column of `testAll` at `seedRound … τ` equals the library's `aCol` at `psAt …
                 (τ + 1)`
  `msgAt_table_is_psAt`   so the one table of `msgAt` at that round is built from that `aCol`
  `hk_LFull`   the hypothesis hk at the written record

The hypothesis hk (h ≤ k at all stages). `roundOf`, and with it `psAt` and `seedRound`, adds k + 3
for a stage; `stagesAll` adds h + g + 3 with the library's `sgOf`, where g is k - h. The two sums
differ as soon as some earlier stage has h > k. The proofs use hk at the stages 0 … τ; it is asked
at all.

No hypothesis on `J.fresh`: where the first fold sends a table of its own, `testAll` overwrites the
column of own round 1, and every `seedRound` is at least 2.

Called: `roundOf_succ` (HalfSteps.lean: where the next stage begins), `length_aFold`
(Johnson/Desc/K12/Honest/Causal.lean). Near it in our folder, not called here and not compared with
it by us: SentTables.lean, Sim/CoreText.lean, KeptLaw4.lean.

Limits.
- What ScriptLots.lean's head says a law over coins has to mind holds here.
- `runs_L_at_laid` (AtFullSide/K12/RunsAtLaidL.lean): the book's fact that lends the carried runs
  (what the two parts spend; of what they carry, how many runs and the last one or two): by the
  book, in scope, at the full size. It is not imported here and occurs in no statement here.
- `aCol` is a column of code words. How its symbols relate to the entries which `stageMsg` returns
  is not treated here.
- The theorems are about `testAll` and `msgAt` at free w, fr, C, D. At the arguments that `testTbl`
  and `testMsgTxt` pass (`frontAt`, `restCoins`, `testDrawsAt`): not treated here.
- `msgAt_table_is_psAt` assumes ha, that `depthAt` gives a depth at that round. It is shown nowhere
  in general. At the written record `depth_LFull` (ScriptLotsNumbersL.lean; under a hypothesis of
  its own, that the fresh table came earlier) lists the rounds at which `depthAt` gives one, and
  `seedRound_LFull` (ScriptLotsAtL.lean) the five rounds: the step from these two to ha is not
  written out.
- That a part says `msgAt` at a run is not treated here.
- None of the four has a control.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ScriptLotsNumbersL
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

/-- A helper. The columns written by the run of all stages are a front piece pre followed by the
columns of `stagesAll` started at stage j with the state `psAt … j` and the round `roundOf … j`; pre
has one column for each round before that one, "BAT" not counted. -/
theorem tr_split (J : TestJob W X) (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: rest) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k) (w : W)
    (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    ∀ j, j < J.p.nums.stages.length → ∃ (l : Laid) (t : T12) (trees : List Tree) (pre : List (ℕ →
      List UInt64)),
      (stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 s (J.laid.drop 1) 1 (J.recB w fr
        (D 0))
          (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).tr =
        pre ++ (stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) (J.p.nums.stages.drop (j + 1))
          j
          (J.p.nums.stages.getD j default) l (roundOf J.p.nums.stages j) t (psAt J w fr C D j) trees
            D).tr ∧
      pre.length + 1 = roundOf J.p.nums.stages j := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨J.laid.drop 1, J.recB w fr (D 0), J.trees₀ w fr C.mem (J.first w fr C), [], ?_, ?_⟩
    · have e1 : J.p.nums.stages.drop (0 + 1) = rest := by rw [hst]; rfl
      have e2 : J.p.nums.stages.getD 0 default = s := by rw [hst]; rfl
      have e3 : roundOf J.p.nums.stages 0 = 1 := by simp [roundOf]
      rw [e1, e2, e3]
      rfl
    · simp [roundOf]
  | succ j ih =>
    intro hj
    have hj' : j < J.p.nums.stages.length := by omega
    obtain ⟨l, t, trees, pre, h1, h2⟩ := ih hj'
    have ed : J.p.nums.stages.drop (j + 1) =
        J.p.nums.stages.getD (j + 1) default :: J.p.nums.stages.drop (j + 1 + 1) := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.drop_eq_getElem_cons hj
    have eh : (sgOf (J.p.nums.stages.getD j default)).h +
        (sgOf (J.p.nums.stages.getD j default)).g =
        (J.p.nums.stages.getD j default).k := by
      have hm : J.p.nums.stages.getD j default ∈ J.p.nums.stages := by
        rw [List.getD_eq_getElem _ _ hj']
        exact List.getElem_mem hj'
      have := hk _ hm
      show (J.p.nums.stages.getD j default).h +
        ((J.p.nums.stages.getD j default).k - (J.p.nums.stages.getD j default).h) = _
      omega
    have el : (J.p.nums.stages.drop (j + 1 + 1)).isEmpty = (j + 2 == J.p.nums.stages.length) := by
      by_cases e : j + 2 = J.p.nums.stages.length
      · rw [show j + 1 + 1 = J.p.nums.stages.length from e, List.drop_length]
        simp
      · have : j + 1 + 1 < J.p.nums.stages.length := by omega
        have hb : (j + 2 == J.p.nums.stages.length) = false := by simpa using e
        rw [List.drop_eq_getElem_cons this, hb]
        rfl
    rw [ed] at h1
    simp only [stagesAll] at h1
    rw [el, eh] at h1
    have er : roundOf J.p.nums.stages j + (J.p.nums.stages.getD j default).k + 3 =
        roundOf J.p.nums.stages (j + 1) := by
      rw [roundOf_succ _ _ hj']
      omega
    rw [er, ← List.append_assoc] at h1
    refine ⟨_, _, _, _, h1, ?_⟩
    rw [← er, List.length_append, List.length_append, List.length_map, length_aFold, eh]
    simp only [List.length_cons, List.length_nil]
    omega

/-- **(T-b) The column that `testAll` writes at the sending round of tree τ is the library's `aCol`
at `psAt … (τ + 1)`.** -/
theorem col_is_psAt (J : TestJob W X) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k) (w : W) (fr : Front X)
    (C : TestCoins) (D : ℕ → Fmt.Drawn) {τ : ℕ} (hτ : τ + 1 < J.p.nums.stages.length) :
    (testAll J w fr C D).tr.getD (seedRound J.p.nums.stages τ) (fun _ => []) =
      aCol (τ + 2 == J.p.nums.stages.length) (J.p.nums.stages.getD (τ + 1) default) (psAt J w fr C D
        (τ + 1)) := by
  obtain ⟨s, rest, hst⟩ : ∃ s rest, J.p.nums.stages = s :: rest := by
    cases h : J.p.nums.stages with
    | nil => rw [h] at hτ; simp at hτ
    | cons s rest => exact ⟨s, rest, rfl⟩
  have hτ' : τ < J.p.nums.stages.length := by omega
  obtain ⟨l, t, trees, pre, h1, h2⟩ := tr_split J s rest hst hk w fr C D τ hτ'
  have ed : J.p.nums.stages.drop (τ + 1) =
      J.p.nums.stages.getD (τ + 1) default :: J.p.nums.stages.drop (τ + 1 + 1) := by
    rw [List.getD_eq_getElem _ _ hτ]
    exact List.drop_eq_getElem_cons hτ
  have eh : (sgOf (J.p.nums.stages.getD τ default)).h + (sgOf (J.p.nums.stages.getD τ default)).g =
      (J.p.nums.stages.getD τ default).k := by
    have hm : J.p.nums.stages.getD τ default ∈ J.p.nums.stages := by
      rw [List.getD_eq_getElem _ _ hτ']
      exact List.getElem_mem hτ'
    have := hk _ hm
    show (J.p.nums.stages.getD τ default).h +
      ((J.p.nums.stages.getD τ default).k - (J.p.nums.stages.getD τ default).h) = _
    omega
  have el : (J.p.nums.stages.drop (τ + 1 + 1)).isEmpty = (τ + 2 == J.p.nums.stages.length) := by
    by_cases e : τ + 2 = J.p.nums.stages.length
    · rw [show τ + 1 + 1 = J.p.nums.stages.length from e, List.drop_length]
      simp
    · have : τ + 1 + 1 < J.p.nums.stages.length := by omega
      have hb : (τ + 2 == J.p.nums.stages.length) = false := by simpa using e
      rw [List.drop_eq_getElem_cons this, hb]
      rfl
  rw [ed] at h1
  simp only [stagesAll] at h1
  rw [el] at h1
  have hn : seedRound J.p.nums.stages τ =
      (pre.length + (1 + (J.p.nums.stages.getD τ default).k)) + 1 := by
    unfold seedRound
    omega
  have hB : ∀ (Bt : List (ℕ → List UInt64)),
      Bt[pre.length + (1 + (J.p.nums.stages.getD τ default).k)]? =
      some (aCol (τ + 2 == J.p.nums.stages.length) (J.p.nums.stages.getD (τ + 1) default)
        (psAt J w fr C D (τ + 1))) →
      ((fun _ => []) :: Bt).getD (seedRound J.p.nums.stages τ) (fun _ => []) =
        aCol (τ + 2 == J.p.nums.stages.length) (J.p.nums.stages.getD (τ + 1) default)
          (psAt J w fr C D (τ + 1)) := by
    intro Bt hBt
    rw [hn, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, hBt]
    rfl
  have hcol : (stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 s (J.laid.drop 1) 1
      (J.recB w fr (D 0)) (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C))
      D).tr[pre.length + (1 + (J.p.nums.stages.getD τ default).k)]? =
      some (aCol (τ + 2 == J.p.nums.stages.length) (J.p.nums.stages.getD (τ + 1) default)
        (psAt J w fr C D (τ + 1))) := by
    rw [h1, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.append_assoc, List.getElem?_append_right (by rw [List.length_map, length_aFold, eh]),
      List.length_map, length_aFold, eh, Nat.sub_self]
    rfl
  unfold testAll
  rw [hst]
  rw [hst] at hB hcol
  refine hB _ ?_
  split
  · rw [List.getElem?_set_ne (by omega)]
    exact hcol
  · exact hcol

/-- **The table of `msgAt` at the sending round of tree τ is built from `aCol` at `psAt … (τ +
1)`**, under ha: its depth a, its width the length of the column at 0, its symbols the column's
words. -/
theorem msgAt_table_is_psAt (J : TestJob W X) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k) (w : W)
    (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) {τ : ℕ} (hτ : τ + 1 < J.p.nums.stages.length)
    {a : ℕ} (ha : depthAt J (seedRound J.p.nums.stages τ) = some a) :
    (msgAt J w fr C D (seedRound J.p.nums.stages τ)).tables =
      [⟨a, (aCol (τ + 2 == J.p.nums.stages.length) (J.p.nums.stages.getD (τ + 1) default)
              (psAt J w fr C D (τ + 1)) 0).length,
        fun x k => toF ((aCol (τ + 2 == J.p.nums.stages.length) (J.p.nums.stages.getD (τ + 1)
          default)
              (psAt J w fr C D (τ + 1)) x).getD k.val 0)⟩] := by
  unfold msgAt
  simp only [ha, Option.toList_some, List.map_cons, List.map_nil]
  rw [col_is_psAt J hk w fr C D hτ]

/-- At the written record h ≤ k at each of the six stages. -/
theorem hk_LFull : ∀ a ∈ H2K.Member.piLFull.nums.stages, a.h ≤ a.k := by
  decide +kernel

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.tr_split
#print axioms ProofFile.Honest.K12.col_is_psAt
#print axioms ProofFile.Honest.K12.msgAt_table_is_psAt
#print axioms ProofFile.Honest.K12.hk_LFull
