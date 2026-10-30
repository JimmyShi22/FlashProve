-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/CongruenceAtKey.lean: The premises of "the congruence"
at the key file's two shared proximity tests: so that
it can say no where its premises are not met, and so that it is not true and empty there.

  rows_of_none         a member of a sending whose vector is not handed in reads the heard alone
  rows_heard_KU, rows_heard_KO   RowsOfHeard at jobKU and jobKO, at all their letters
  p_KU, p_KO, fresh_KU, fresh_KO   what these jobs' numbers and word on the fresh table are
  hk_U, hk_O           h ≤ k at the stages
  len_U, len_O         five stages, four
  seeds_U, seeds_O     the sending rounds of the switches' trees
  rounds_U, rounds_O   the rounds at which such a job sends a table: these and no other
  ha_U, ha_O           the depth at each switch's sending round
  own_O                the depth at round 1 of the test on G_omega
  depths_len_U, depths_len_O   the lists of rounds have 35 and 24 entries; beyond, depthAt is none
  JKU, JKO             the key's two jobs as a TestJob, at the full size's places
  tables_key_U, tables_key_O, tables_key_own   THE CONGRUENCE TAKEN AT THESE: so that "not empty at the
      key" is Lean's word, and that the premises' forms fit the general theorems' binders. jobKU's
      word "none" stands at KeyHalves.lean:81, jobKO's at :89

Limits.
- The numbers are the places' at the full size (piKUFull, piKOFull): how they stand to a run is
  PlacesKeyFull.lean's word, and hk, the lengths and the depths are read off these terms alone.
- Nothing is played here; no run, no book, no coin. All of TablesAtFront.lean's head binds here, its
  "WHAT A YES IS" and "A YES WOULD NOT SHOW" first.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyHalves
import Johnson.Desc.ProofFile.Honest.K12.TablesAtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLay
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open H2K.Member (piKUFull piKOFull)
open ProofFile.Honest (Common Weights TableRand Addr Front Table)
open ProofFile.Honest.K14 (SendPub SendJob Ask)
open ProofFile.Honest.K12 (TestJob TestCoins RowsOfHeard rowsOfHeard_many depthAt depths seedRound Stretch
  msgAt frontAt tables_at_frontAt tables_at_own_round)
open ProofFile.Honest.K12.Light (memOfSending jobLocU jobAtU jobAtOmega)

variable {W₀ Rc X W : Type}

/-- **A member of a sending whose vector is not handed in reads of a front the heard alone.** -/
theorem rows_of_none (J : SendJob) (at_ : Addr) (k : ℕ) (fs : Option ℕ × Option ℕ)
    (ask : W → Ask) (w : W) (fr fr' : Front X) (c : Stretch) (he : fr.heard = fr'.heard) :
    (memOfSending J at_ k fs ask none).rows w fr c =
      (memOfSending J at_ k fs ask none).rows w fr' c := by
  simp only [memOfSending, he]

/-- **At the test on G_u, rows₀ reads the heard alone**, at all the job's letters. -/
theorem rows_heard_KU (A : SendPub) (pU : P12) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    RowsOfHeard (jobKU (X := X) A pU bs st weights rand).toRun.toTest := by
  refine rowsOfHeard_many _ fun m hm w fr fr' c he => ?_
  simp only [jobKU, jobLocU, jobAtU, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> exact rows_of_none _ _ _ _ _ w fr fr' c he

/-- **At the test on G_omega, rows₀ reads the heard alone**, at all the job's letters. -/
theorem rows_heard_KO (A : SendPub) (pU pO : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    RowsOfHeard (jobKO (X := X) A pU pO bs weights rand).toRun.toTest := by
  refine rowsOfHeard_many _ fun m hm w fr fr' c he => ?_
  simp only [jobKO, jobAtOmega, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> exact rows_of_none _ _ _ _ _ w fr fr' c he

/-- The numbers of jobKU are its letter's. -/
theorem p_KU (A : SendPub) (pU : P12) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    (jobKU (X := X) A pU bs st weights rand).toRun.toTest.p = pU := rfl

/-- The numbers of jobKO are its second letter's. -/
theorem p_KO (A : SendPub) (pU pO : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    (jobKO (X := X) A pU pO bs weights rand).toRun.toTest.p = pO := rfl

/-- At the test on G_u the fresh table came earlier. -/
theorem fresh_KU (A : SendPub) (pU : P12) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    (jobKU (X := X) A pU bs st weights rand).toRun.toTest.fresh.isNone = false := rfl

/-- At the test on G_omega the first fold sends it. -/
theorem fresh_KO (A : SendPub) (pU pO : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    (jobKO (X := X) A pU pO bs weights rand).toRun.toTest.fresh = none := rfl

/-- h ≤ k at the five stages of the test on G_u. -/
theorem hk_U : ∀ a ∈ piKUFull.nums.stages, a.h ≤ a.k := by
  decide +kernel

/-- h ≤ k at the four stages of the test on G_omega. -/
theorem hk_O : ∀ a ∈ piKOFull.nums.stages, a.h ≤ a.k := by
  decide +kernel

theorem len_U : piKUFull.nums.stages.length = 5 := by
  decide +kernel

theorem len_O : piKOFull.nums.stages.length = 4 := by
  decide +kernel

/-- The switches' sending rounds at the test on G_u. -/
theorem seeds_U : (List.range 4).map (seedRound piKUFull.nums.stages) = [9, 17, 24, 31] := by
  decide +kernel

/-- The switches' sending rounds at the test on G_omega. -/
theorem seeds_O : (List.range 3).map (seedRound piKOFull.nums.stages) = [6, 13, 20] := by
  decide +kernel

/-- **The rounds at which a job at the place of the test on G_u, whose fresh table came earlier,
sends a table: these four and no other.** 35 is that test's number of rounds. -/
theorem rounds_U (J : TestJob W X) (hJ : J.p = piKUFull) (hf : J.fresh.isNone = false) :
    (List.range 35).filter (fun i => (depthAt J i).isSome) = [9, 17, 24, 31] := by
  have e : (fun i => (depthAt J i).isSome) =
      fun i => ((none :: depths false piKUFull.nums.stages).getD i none).isSome := by
    funext i
    unfold depthAt
    rw [hJ, hf]
  rw [e]
  decide +kernel

/-- **The same at the test on G_omega, whose first fold sends its own table: round 1 too.** -/
theorem rounds_O (J : TestJob W X) (hJ : J.p = piKOFull) (hf : J.fresh = none) :
    (List.range 24).filter (fun i => (depthAt J i).isSome) = [1, 6, 13, 20] := by
  have hf' : J.fresh.isNone = true := by simp [hf]
  have e : (fun i => (depthAt J i).isSome) =
      fun i => ((none :: depths true piKOFull.nums.stages).getD i none).isSome := by
    funext i
    unfold depthAt
    rw [hJ, hf']
  rw [e]
  decide +kernel

/-- **The depth at each switch's sending round, at the test on G_u.** -/
theorem ha_U (J : TestJob W X) (hJ : J.p = piKUFull) (hf : J.fresh.isNone = false) :
    ∀ τ, τ < 4 → depthAt J (seedRound J.p.nums.stages τ) = some ([21, 17, 13, 14].getD τ 0) := by
  have e : ∀ τ, depthAt J (seedRound J.p.nums.stages τ) =
      (none :: depths false piKUFull.nums.stages).getD (seedRound piKUFull.nums.stages τ) none := by
    intro τ
    unfold depthAt
    rw [hJ, hf]
  intro τ
  rw [e]
  revert τ
  decide +kernel

/-- **The depth at each switch's sending round, at the test on G_omega.** -/
theorem ha_O (J : TestJob W X) (hJ : J.p = piKOFull) (hf : J.fresh = none) :
    ∀ τ, τ < 3 → depthAt J (seedRound J.p.nums.stages τ) = some ([18, 14, 15].getD τ 0) := by
  have hf' : J.fresh.isNone = true := by simp [hf]
  have e : ∀ τ, depthAt J (seedRound J.p.nums.stages τ) =
      (none :: depths true piKOFull.nums.stages).getD (seedRound piKOFull.nums.stages τ) none := by
    intro τ
    unfold depthAt
    rw [hJ, hf']
  intro τ
  rw [e]
  revert τ
  decide +kernel

/-- **The depth at round 1 of the test on G_omega**: the first fold's own table. -/
theorem own_O (J : TestJob W X) (hJ : J.p = piKOFull) (hf : J.fresh = none) :
    depthAt J 1 = some 13 := by
  have hf' : J.fresh.isNone = true := by simp [hf]
  unfold depthAt
  rw [hJ, hf']
  decide +kernel

/-- The list of the test on G_u's rounds has 35 entries. -/
theorem depths_len_U : (none :: depths false piKUFull.nums.stages).length = 35 := by
  decide +kernel

/-- The list of the test on G_omega's rounds has 24 entries. -/
theorem depths_len_O : (none :: depths true piKOFull.nums.stages).length = 24 := by
  decide +kernel

/-- The job at the test on G_u, at the full size's place, as a TestJob. -/
abbrev JKU (A : SendPub) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    TestJob (Common W₀ Rc TableKey) X :=
  (jobKU (X := X) A piKUFull bs st weights rand).toRun.toTest

/-- The job at the test on G_omega, at the full size's places, as a TestJob. -/
abbrev JKO (A : SendPub) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    TestJob (Common W₀ Rc TableKey) X :=
  (jobKO (X := X) A piKUFull piKOFull bs weights rand).toRun.toTest

/-- **THE CONGRUENCE AT THE KEY's TEST ON G_u, at each of its four switches**, at all the job's
letters. -/
theorem tables_key_U (A : SendPub) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (w : Common W₀ Rc TableKey) (own₀ : X) (n₀ : ℕ) (h : List Fmt.Drawn)
    (fr : Front X) (hfr : fr.heard = h.take n₀) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    {τ : ℕ} (hτ : τ < 4) :
    ∃ T : Table, T.logLength = [21, 17, 13, 14].getD τ 0 ∧
      (msgAt (JKU (X := X) A bs st weights rand) w fr C D
        (seedRound piKUFull.nums.stages τ)).tables = [T] ∧
      (msgAt (JKU (X := X) A bs st weights rand) w (frontAt own₀ n₀ h) C D
        (seedRound piKUFull.nums.stages τ)).tables = [T] :=
  tables_at_frontAt (JKU (X := X) A bs st weights rand) (rows_heard_KU A piKUFull bs st weights rand)
    hk_U w own₀ n₀ h fr hfr C D
    (show τ + 1 < piKUFull.nums.stages.length by rw [len_U]; omega)
    (ha_U (JKU (X := X) A bs st weights rand) rfl rfl τ hτ)

/-- **THE CONGRUENCE AT THE KEY's TEST ON G_omega, at each of its three switches**, at all the job's
letters. -/
theorem tables_key_O (A : SendPub) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (w : Common W₀ Rc TableKey) (own₀ : X) (n₀ : ℕ) (h : List Fmt.Drawn)
    (fr : Front X) (hfr : fr.heard = h.take n₀) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    {τ : ℕ} (hτ : τ < 3) :
    ∃ T : Table, T.logLength = [18, 14, 15].getD τ 0 ∧
      (msgAt (JKO (X := X) A bs weights rand) w fr C D
        (seedRound piKOFull.nums.stages τ)).tables = [T] ∧
      (msgAt (JKO (X := X) A bs weights rand) w (frontAt own₀ n₀ h) C D
        (seedRound piKOFull.nums.stages τ)).tables = [T] :=
  tables_at_frontAt (JKO (X := X) A bs weights rand)
    (rows_heard_KO A piKUFull piKOFull bs weights rand)
    hk_O w own₀ n₀ h fr hfr C D
    (show τ + 1 < piKOFull.nums.stages.length by rw [len_O]; omega)
    (ha_O (JKO (X := X) A bs weights rand) rfl rfl τ hτ)

/-- **THE OTHER SENDING ROUND AT THE KEY's TEST ON G_omega**: own 7's place, of .tables alone, at one
C: no text for it (TablesAtFront.lean's head). -/
theorem tables_key_own (A : SendPub) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (w : Common W₀ Rc TableKey) (fr fr' : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    ∃ T : Table, T.logLength = 13 ∧
      (msgAt (JKO (X := X) A bs weights rand) w fr C D 1).tables = [T] ∧
      (msgAt (JKO (X := X) A bs weights rand) w fr' C D 1).tables = [T] :=
  tables_at_own_round (JKO (X := X) A bs weights rand)
    (fresh_KO A piKUFull piKOFull bs weights rand) w fr fr' C D
    (own_O (JKO (X := X) A bs weights rand) rfl (fresh_KO A piKUFull piKOFull bs weights rand))

end AtPublicFiles.KeyLay

#print axioms AtPublicFiles.KeyLay.rows_of_none
#print axioms AtPublicFiles.KeyLay.rows_heard_KU
#print axioms AtPublicFiles.KeyLay.rows_heard_KO
#print axioms AtPublicFiles.KeyLay.p_KU
#print axioms AtPublicFiles.KeyLay.p_KO
#print axioms AtPublicFiles.KeyLay.fresh_KU
#print axioms AtPublicFiles.KeyLay.fresh_KO
#print axioms AtPublicFiles.KeyLay.hk_U
#print axioms AtPublicFiles.KeyLay.hk_O
#print axioms AtPublicFiles.KeyLay.len_U
#print axioms AtPublicFiles.KeyLay.len_O
#print axioms AtPublicFiles.KeyLay.seeds_U
#print axioms AtPublicFiles.KeyLay.seeds_O
#print axioms AtPublicFiles.KeyLay.rounds_U
#print axioms AtPublicFiles.KeyLay.rounds_O
#print axioms AtPublicFiles.KeyLay.ha_U
#print axioms AtPublicFiles.KeyLay.ha_O
#print axioms AtPublicFiles.KeyLay.own_O
#print axioms AtPublicFiles.KeyLay.depths_len_U
#print axioms AtPublicFiles.KeyLay.depths_len_O
#print axioms AtPublicFiles.KeyLay.JKU
#print axioms AtPublicFiles.KeyLay.JKO
#print axioms AtPublicFiles.KeyLay.tables_key_U
#print axioms AtPublicFiles.KeyLay.tables_key_O
#print axioms AtPublicFiles.KeyLay.tables_key_own
