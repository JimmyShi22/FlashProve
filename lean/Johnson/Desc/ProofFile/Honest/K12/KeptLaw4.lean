-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/KeptLaw4.lean: proof of `Spec.first_reads` (KeptSpec.lean). The
messages of the first part's rounds (the round "BAT" and the first fold; `msgAt`, `firstLen`,
Parts.lean) are the same at two values of `TestCoins` (Test.lean) that agree in the fields `hide`
and `mem` and, if the first fold sends the fresh table itself, in the field `tails`. The field
`rest` may differ. It holds for every `TestJob` whose stages pass `StagesOk` (RunBy.lean).

  `first_reads`  the proof
  `testAll_rs`, `testAll_tr`   the first k + 2 rounds and column functions of `testAll`: the round
                 "BAT", then the first fold's (`firstFold`); the fresh table's column stands at
                 entry 1 if the fold sends that table
  `firstFold_congr`, `freshCol_congr`   which fields of `TestCoins` these two depend on

By what. `msgAt` reads entry i of the rounds and of the column functions of `testAll`, and never the
opened columns. Below k + 2 these entries belong to the first fold, which is computed from the first
stage's two tables (`rows₀` at `mem`) and from `hide`. The job's field `trees₀`, which is given the
whole first state and so the tails, enters only the opened columns and the state after the first
switch. Of `StagesOk` the proof uses that there are at least two stages, and h ≤ k at the
first.

Limits.
- An equation between two messages. Nothing follows on how a random value is sampled, or on what a
  verifier decides.
- "Agree in a field" means as whole functions, outside the counts too. The two parts' own
  `TestCoins` do not agree so: see `Spec.first_reads_in` (LentSpec.lean).
- Nothing on the second part's rounds. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.KeptSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Johnson.Prover.Link (μOf rowOf length_showRV packedN freshSym wordsOf wr)
open Fmt.M1 (Stage)
open H2K.Pub (sgOf)

variable {W X : Type}

/-! ## 1 Lists -/

theorem get_of_take {α : Type} {l l' : List α} {m i : ℕ} (h : l.take m = l'.take m) (hi : i < m) :
    l[i]? = l'[i]? :=
  calc l[i]? = (l.take m)[i]? := (List.getElem?_take_of_lt hi).symm
    _ = (l'.take m)[i]? := by rw [h]
    _ = l'[i]? := List.getElem?_take_of_lt hi

/-! ## 2 What a message reads -/

/-- A message depends on `testAll` through entry i of its rounds and of its column functions. -/
theorem msgAt_congr (J : TestJob W X) (w : W) (fr : Front X) (C C' : TestCoins)
    (D : ℕ → Fmt.Drawn) (i : ℕ)
    (h1 : (testAll J w fr C D).rs[i]? = (testAll J w fr C' D).rs[i]?)
    (h2 : (testAll J w fr C D).tr[i]? = (testAll J w fr C' D).tr[i]?) :
    msgAt J w fr C D i = msgAt J w fr C' D i := by
  have h3 : (testAll J w fr C D).tr.getD i (fun _ => []) =
      (testAll J w fr C' D).tr.getD i fun _ => [] := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h2]
  unfold msgAt
  dsimp only
  rw [h1, h3]

/-! ## 3 The first fold -/

/-- The first fold's rounds, as `testAll` computes them. st: the list of stages. s: the first. -/
def firstFold (st : List Stage) (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (s : Stage) : List Fmt.RoundView :=
  aFold (coinsOf st C.hide C.rest) 0 s 1 (J.first w fr C) (rowOf (J.recB w fr (D 0))) D

theorem firstFold_length (st : List Stage) (J : TestJob W X) (w : W) (fr : Front X)
    (C : TestCoins) (D : ℕ → Fmt.Drawn) (s : Stage) (hk : s.h ≤ s.k) :
    (firstFold st J w fr C D s).length = s.k + 1 := by
  unfold firstFold aFold foldShown
  rw [List.length_cons, length_showRV]
  show s.h + (s.k - s.h) + 1 = s.k + 1
  omega

/-- The first fold's rounds depend on the fields `hide` and `mem` alone. -/
theorem firstFold_congr (st : List Stage) (J : TestJob W X) (w : W) (fr : Front X)
    (C C' : TestCoins) (D : ℕ → Fmt.Drawn) (s : Stage) (hh : C.hide = C'.hide)
    (hm : C.mem = C'.mem) : firstFold st J w fr C D s = firstFold st J w fr C' D s := by
  have e1 : μOf (sgOf s) (J.first w fr C) = μOf (sgOf s) (J.first w fr C') := by
    funext x
    cases x with
    | inl x =>
      show (J.rows₀ w fr C.mem).tabM _ = (J.rows₀ w fr C'.mem).tabM _
      rw [hm]
    | inr x =>
      show (J.rows₀ w fr C.mem).tabZ _ = (J.rows₀ w fr C'.mem).tabZ _
      rw [hm]
  have e2 : (coinsOf st C.hide C.rest).W (sgOf s) 0 =
      (coinsOf st C'.hide C'.rest).W (sgOf s) 0 := by
    show hideAt _ (if (0 : ℕ) = 0 then C.hide else _) =
      hideAt _ (if (0 : ℕ) = 0 then C'.hide else _)
    rw [if_pos rfl, if_pos rfl, hh]
  unfold firstFold aFold
  rw [e1, e2]

/-- The fresh table's column depends on the fields `hide` and `tails` alone. -/
theorem freshCol_congr (J : TestJob W X) (w : W) (fr : Front X) (C C' : TestCoins) (s : Stage)
    (hh : C.hide = C'.hide) (ht : C.tails = C'.tails) :
    freshCol (sgOf s) (J.first w fr C) = freshCol (sgOf s) (J.first w fr C') := by
  funext x
  show wordsOf (wr _ (freshSym _ (packedN _ (hideAt _ C.hide)) C.tails x)) =
    wordsOf (wr _ (freshSym _ (packedN _ (hideAt _ C'.hide)) C'.tails x))
  rw [hh, ht]

/-! ## 4 The first k + 2 entries of `testAll` -/

theorem testAll_rs (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (s n : Stage) (r : List Stage) (hs : J.p.nums.stages = s :: n :: r) (hk : s.h ≤ s.k) :
    (testAll J w fr C D).rs.take (s.k + 2) =
      ⟨[], D 0⟩ :: firstFold (s :: n :: r) J w fr C D s := by
  have hl := firstFold_length (s :: n :: r) J w fr C D s hk
  unfold testAll
  rw [hs]
  show ((⟨[], D 0⟩ : Fmt.RoundView) :: (firstFold (s :: n :: r) J w fr C D s ++ _ ++ _)).take
    (s.k + 1 + 1) = _
  rw [List.take_succ_cons, List.append_assoc, List.take_left' hl]

theorem testAll_tr (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (s n : Stage) (r : List Stage) (hs : J.p.nums.stages = s :: n :: r) (hk : s.h ≤ s.k) :
    (testAll J w fr C D).tr.take (s.k + 2) =
      (fun _ => []) ::
        (if J.fresh.isNone then
          ((firstFold (s :: n :: r) J w fr C D s).map
            fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)).set 0
              (freshCol (sgOf s) (J.first w fr C))
        else (firstFold (s :: n :: r) J w fr C D s).map
          fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)) := by
  have hl : ((firstFold (s :: n :: r) J w fr C D s).map
      fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)).length = s.k + 1 := by
    rw [List.length_map]
    exact firstFold_length (s :: n :: r) J w fr C D s hk
  unfold testAll
  rw [hs]
  show ((fun _ => []) ::
    (if J.fresh.isNone then
      ((firstFold (s :: n :: r) J w fr C D s).map
        (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)) ++ _ ++ _).set 0
          (freshCol (sgOf s) (J.first w fr C))
    else (firstFold (s :: n :: r) J w fr C D s).map
      (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)) ++ _ ++ _)).take (s.k + 1 + 1) = _
  rw [List.take_succ_cons]
  by_cases hf : J.fresh.isNone = true
  · rw [if_pos hf, if_pos hf, List.take_set, List.append_assoc, List.take_left' hl]
  · rw [if_neg hf, if_neg hf, List.append_assoc, List.take_left' hl]

/-! ## 5 The statement -/

theorem first_reads : Spec.first_reads := by
  intro W X J w fr C C' D i ok hi hh hm ht
  cases hs : J.p.nums.stages with
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
      have ef := firstFold_congr (s :: n :: r) J w fr C C' D s hh hm
      refine msgAt_congr J w fr C C' D i (get_of_take ?_ hi') (get_of_take ?_ hi')
      · rw [testAll_rs J w fr C D s n r hs hk, testAll_rs J w fr C' D s n r hs hk, ef]
      · rw [testAll_tr J w fr C D s n r hs hk, testAll_tr J w fr C' D s n r hs hk, ef]
        by_cases hf : J.fresh.isNone = true
        · rw [if_pos hf, if_pos hf, freshCol_congr J w fr C C' s hh (ht hf)]
        · rw [if_neg hf, if_neg hf]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.get_of_take
#print axioms ProofFile.Honest.K12.Light.msgAt_congr
#print axioms ProofFile.Honest.K12.Light.firstFold_length
#print axioms ProofFile.Honest.K12.Light.firstFold_congr
#print axioms ProofFile.Honest.K12.Light.freshCol_congr
#print axioms ProofFile.Honest.K12.Light.testAll_rs
#print axioms ProofFile.Honest.K12.Light.testAll_tr
#print axioms ProofFile.Honest.K12.Light.first_reads
#print axioms ProofFile.Honest.K12.Light.firstFold
