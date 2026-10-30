-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/LentLaw3.lean: proof of `Spec.first_reads_in` (LentSpec.lean). At
the job of a `ManyJob` (RunMany.lean) whose stages pass `StagesOk` (RunBy.lean), the messages of the
first part's rounds are the same at two values of `TestCoins` (Test.lean) that agree within the
counts alone: `hide` below 2 k + 1, `mem` at the numbers of the members in the list, and, if the
first fold sends the fresh table itself, `tails` at rows below 2 ^ h and entries below Z.r.

  `first_reads_in`   the proof
  `many_rows`    the job's first rows depend on `mem` at the members' numbers alone
  `firstFold_in`, `freshCol_in`   `firstFold_congr` and `freshCol_congr` (KeptLaw4.lean) with
                 hypotheses on what is read alone

By what. The shape of the first k + 2 rounds and column functions of `testAll` is that of
KeptLaw4.lean (`testAll_rs`, `testAll_tr`, `msgAt_congr`). `hideAt` reads its argument below 2 k + 1
(`hideAt_congr`, HideCongr.lean). A symbol reads a tail below the code's r (`symG_congr`,
Johnson/Prover/Link/Base.lean), and an encoded list of n values reads its function below n
(`wr_congr`, RunByTab.lean).

Limits.
- An equation between two messages. Nothing follows on how a random value is sampled, or on what a
  verifier decides.
- At the jobs `A.toRun.toTest` only: for another `TestJob` nothing bounds the numbers at which
  `rows₀` reads `mem`.
- Of `StagesOk` the proof uses that there are two stages or more, and h ≤ k at the first.
- Nothing on the second part's rounds. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.LentSpec
import Johnson.Desc.ProofFile.Honest.K12.KeptLaw4
import Johnson.Desc.ProofFile.Honest.K12.RunByTab
import Johnson.Desc.ProofFile.Honest.K12.HideCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Johnson.Prover.Link (μOf packedN freshSym wordsOf wr symG_congr)
open Fmt.M1 (Stage)
open H2K.Pub (sgOf)

variable {W X : Type}

/-! ## 1 The first rows -/

theorem snd_lt_zipIdx {α : Type} : ∀ (l : List α) (k : ℕ) (x : α × ℕ),
    x ∈ l.zipIdx k → x.2 < k + l.length
  | [], _, _, h => absurd h List.not_mem_nil
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rw [List.length_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · show k < k + (l.length + 1)
      omega
    · have h2 := snd_lt_zipIdx l (k + 1) x h'
      omega

/-- The job's first rows depend on `mem` at the members' numbers alone. -/
theorem many_rows (A : ManyJob W X) (w : W) (fr : Front X) (mem mem' : ℕ → Stretch)
    (h : ∀ t < A.mems.length, mem t = mem' t) :
    A.toRun.toTest.rows₀ w fr mem = A.toRun.toTest.rows₀ w fr mem' := by
  have e : (A.mems.zipIdx.map fun m => (m.1.shape, m.1.rows w fr (mem m.2))) =
      A.mems.zipIdx.map fun m => (m.1.shape, m.1.rows w fr (mem' m.2)) :=
    List.map_congr_left fun m hm => by
      have hl := snd_lt_zipIdx A.mems 0 m hm
      rw [h m.2 (by omega)]
  show readPS A.toRun.s₀ (layFirst A.s₀ _) = readPS A.toRun.s₀ (layFirst A.s₀ _)
  rw [e]

/-! ## 2 The first fold and the fresh table -/

theorem firstFold_in (st : List Stage) (J : TestJob W X) (w : W) (fr : Front X)
    (C C' : TestCoins) (D : ℕ → Fmt.Drawn) (s : Stage)
    (hr : J.rows₀ w fr C.mem = J.rows₀ w fr C'.mem)
    (hh : ∀ n < 2 * ((sgOf s).h + (sgOf s).g) + 1, C.hide n = C'.hide n) :
    firstFold st J w fr C D s = firstFold st J w fr C' D s := by
  have e1 : μOf (sgOf s) (J.first w fr C) = μOf (sgOf s) (J.first w fr C') := by
    funext x
    cases x with
    | inl x =>
      show (J.rows₀ w fr C.mem).tabM _ = (J.rows₀ w fr C'.mem).tabM _
      rw [hr]
    | inr x =>
      show (J.rows₀ w fr C.mem).tabZ _ = (J.rows₀ w fr C'.mem).tabZ _
      rw [hr]
  have e2 : (coinsOf st C.hide C.rest).W (sgOf s) 0 =
      (coinsOf st C'.hide C'.rest).W (sgOf s) 0 := by
    show hideAt _ (if (0 : ℕ) = 0 then C.hide else _) =
      hideAt _ (if (0 : ℕ) = 0 then C'.hide else _)
    rw [if_pos rfl, if_pos rfl]
    exact hideAt_congr _ _ _ hh
  unfold firstFold aFold
  rw [e1, e2]

theorem freshCol_in (J : TestJob W X) (w : W) (fr : Front X) (C C' : TestCoins) (s : Stage)
    (hh : ∀ n < 2 * ((sgOf J.s₀).h + (sgOf J.s₀).g) + 1, C.hide n = C'.hide n)
    (ht : ∀ b < 2 ^ s.h, ∀ q < s.Z.r, C.tails b q = C'.tails b q) :
    freshCol (sgOf s) (J.first w fr C) = freshCol (sgOf s) (J.first w fr C') := by
  funext x
  show wordsOf (wr (2 ^ s.h) (freshSym (sgOf s) (packedN _ (hideAt _ C.hide)) C.tails x)) =
    wordsOf (wr (2 ^ s.h) (freshSym (sgOf s) (packedN _ (hideAt _ C'.hide)) C'.tails x))
  rw [hideAt_congr _ C.hide C'.hide hh]
  exact congrArg wordsOf (wr_congr _ _ _ fun b hb =>
    symG_congr s.Z _ _ _ _ _ (fun _ _ => rfl) fun q hq => ht b hb q hq)

/-! ## 3 The statement -/

theorem first_reads_in : Spec.first_reads_in := by
  intro W X A w fr C C' D i ok hi hh hm ht
  have hsA : A.toRun.toTest.p.nums.stages = A.p.nums.stages := rfl
  cases hs : A.p.nums.stages with
  | nil =>
    rw [hs] at ok
    have no : false = true := ok
    cases no
  | cons s l =>
    cases l with
    | nil =>
      rw [hs] at ok
      have no : false = true := ok
      cases no
    | cons n r =>
      rw [hs] at ok hi
      have ok' : okFrom s (n :: r) = true := ok
      have hk : s.h ≤ s.k := by
        simp only [okFrom, Bool.and_eq_true, decide_eq_true_eq] at ok'
        exact ok'.1.1.1
      have hi' : i < s.k + 2 := by
        have h2 : i < 2 + s.k := hi
        omega
      have es : A.s₀ = s := by
        unfold ManyJob.s₀
        rw [hs]
        rfl
      rw [es] at hh ht
      have ej : A.toRun.toTest.s₀ = s := es
      have eg : (sgOf s).h + (sgOf s).g = s.k := sg_k hk
      have hh' : ∀ n < 2 * ((sgOf s).h + (sgOf s).g) + 1, C.hide n = C'.hide n := by
        rw [eg]
        exact hh
      have hs' : A.toRun.toTest.p.nums.stages = s :: n :: r := hs
      have ef := firstFold_in (s :: n :: r) A.toRun.toTest w fr C C' D s
        (many_rows A w fr C.mem C'.mem hm) hh'
      refine msgAt_congr A.toRun.toTest w fr C C' D i (get_of_take ?_ hi') (get_of_take ?_ hi')
      · rw [testAll_rs _ w fr C D s n r hs' hk, testAll_rs _ w fr C' D s n r hs' hk, ef]
      · rw [testAll_tr _ w fr C D s n r hs' hk, testAll_tr _ w fr C' D s n r hs' hk, ef]
        by_cases hf : A.toRun.toTest.fresh.isNone = true
        · rw [if_pos hf, if_pos hf,
            freshCol_in A.toRun.toTest w fr C C' s (by rw [ej]; exact hh') (ht hf)]
        · rw [if_neg hf, if_neg hf]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.snd_lt_zipIdx
#print axioms ProofFile.Honest.K12.Light.many_rows
#print axioms ProofFile.Honest.K12.Light.firstFold_in
#print axioms ProofFile.Honest.K12.Light.freshCol_in
#print axioms ProofFile.Honest.K12.Light.first_reads_in
