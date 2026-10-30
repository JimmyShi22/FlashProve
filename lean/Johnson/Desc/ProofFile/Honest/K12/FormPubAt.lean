-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FormPubAt.lean: the four clauses on the plan under which every
list of challenges that can be sampled has the form `FormAsks` (the clauses: `FormPub`,
FormDraws.lean in this folder), as one function to Bool, `formPubB`, with the theorem that its
"true" gives `FormPub`. The function is true, by evaluation in Lean's kernel (`decide +kernel`), at
three small made-up places and at `piKRFull` (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean), which
is the place of the key file's test on the ranges at the full size, written out as a closed term.
`FormAsks` is one of the four hypotheses of `accepts_of_plan`, a theorem on the acceptance of a
proximity test's block (both: PlanB.lean in this folder). One computable definition, six theorems,
and two evaluations (`#guard`).

In the list: a place (`P12`, Johnson/Desc/K12/Frame.lean; also called the plan) holds the numbers of
a proximity test, among them the list of stages `p.nums.stages`. A stage (`Fmt.M1.Stage`) has a main
code C, a mask code Z and the numbers k, h and t. `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean)
pairs each declared round of the place with its oracle messages, so the declared rounds are
`(laidOf p).map (·.1)`. A list ds of challenges (`Fmt.Drawn`) can be sampled if `drawsFit`, a test
of the frame (Johnson/Desc/ProofFile/Honest/Frame.lean), is true of the declared rounds and ds.
`byNo ds` (PlayedTerm.lean in this folder) reads ds by the round's number. A job (`TestJob`,
Test.lean in this folder) is what a caller supplies for its test; `J.p` is its place. The front
(`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean) is what precedes the test; the coins have the type
`TestCoins` (Test.lean).

  `formAsks_KR`: at every job J with `J.p = piKRFull`, every input w of the prover, front fr, coins
    C and list ds that can be sampled, `FormAsks J w fr C (byNo ds)` holds
  `formPubB_toy`, `formPubB_came`, `formPubB_late`, `formPubB_KR`: `formPubB` is true at `Toy.p`,
    `ToyCame.p` and `ToyLate.p` (Toy.lean, ToyCame.lean, ToyLate.lean in this folder) and at
    `piKRFull`
  `formPub_of_B`: if the place's stages are `a :: next :: rest` and `formPubB p = true`, then
    `FormPub p a next rest` holds
  `formPubB p`: a definition: false at a place with fewer than two stages. Else, with the stages
    `a :: next :: rest`, the four clauses of `FormPub p a next rest` together: h ≤ k at a; `asked`
    (Johnson/Prover/Link/BodySorts.lean) of the declared rounds is
    `[] :: bodyItems a (next :: rest)` (Johnson/Prover/Link/LinkItems.lean); `switchCut`
    (Johnson/Prover/Link/FormSwitch.lean) is true of C.a at a and of `dS` and `dC`, the two declared
    rounds that `lettersOf` (AllB.lean in this folder) reads off the place for the first switch; the
    entry of `dC` states as many positions as t at a

By what. `formAsks_KR` calls `formAsks_of_draws` (FormDraws.lean) with `formPub_of_B` and
`formPubB_KR`; a list of fewer than two stages contradicts `formPubB_KR`. `formPub_of_B` unfolds
`formPubB`.

Limits.
- `formPubB` reads the place only.
- For some of `piKRFull`'s numbers the only source is the printed output of a run of Lean's
  evaluator, which is not in this library: the Limits in the head of PlaceKeyRangesFull.lean name
  them and say with what they are compared.
- That a description makes this place at any public files is not stated here.
- No job at `piKRFull` is defined here: J is a free parameter.
- No list ds that can be sampled at `piKRFull` is given by name here: `formAsks_KR` is shown at no
  written list.
- `formAsks_KR` does not say that the test accepts: `FormAsks` is one of the four hypotheses of
  `accepts_of_plan` (see the Limits of FormDraws.lean).
- The negative tests are evaluations by Lean's evaluator, outside the kernel: they leave no theorem.
  Both are at `Toy.p`, changed; each shows that `formPubB` is false, not which clause fails. By
  reading: the first change makes the clause h ≤ k false, and the second empties `laidOf p`, so that
  the clause on `asked` is false. The clauses on `switchCut` and on the number of positions have no
  negative test of their own.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FormDraws
import Johnson.Desc.ProofFile.Honest.K12.ToyCame
import Johnson.Desc.ProofFile.Honest.K12.ToyLate
import Johnson.Desc.K12.Law.PlaceKeyRangesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.Member (piKRFull)

variable {W X : Type}

/-- The four clauses of `FormPub` as one Bool, computed from the place only; false at a place with
fewer than two stages. -/
def formPubB (p : P12) : Bool :=
  match p.nums.stages with
  | a :: next :: rest =>
    decide (a.h ≤ a.k) && decide ((laidOf p).map asked = [] :: bodyItems a (next :: rest)) &&
      switchCut (sgOf a).C.a (lettersOf p a next).dS (lettersOf p a next).dC &&
      decide ((lettersOf p a next).dC.entry.poss = a.t)
  | _ => false

theorem formPub_of_B (p : P12) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : p.nums.stages = a :: next :: rest) (h : formPubB p = true) :
    FormPub p a next rest := by
  unfold formPubB at h
  rw [hst] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

set_option maxRecDepth 100000 in
theorem formPubB_toy : formPubB Toy.p = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem formPubB_came : formPubB ToyCame.p = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem formPubB_late : formPubB ToyLate.p = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem formPubB_KR : formPubB piKRFull = true := by decide +kernel

/-- **At a job at `piKRFull`, `FormAsks` holds at every list of challenges that can be sampled.** -/
theorem formAsks_KR (J : TestJob W X) (hJ : J.p = piKRFull) (w : W) (fr : Front X)
    (C : TestCoins) (ds : List Fmt.Drawn)
    (hd : drawsFit ((laidOf J.p).map (·.1)) ds = true) : FormAsks J w fr C (byNo ds) := by
  have hB : formPubB J.p = true := by
    rw [hJ]
    exact formPubB_KR
  cases hs : J.p.nums.stages with
  | nil =>
    unfold formPubB at hB
    rw [hs] at hB
    cases hB
  | cons a l =>
    cases l with
    | nil =>
      unfold formPubB at hB
      rw [hs] at hB
      cases hB
    | cons next rest =>
      exact formAsks_of_draws J w fr C ds a next rest hs (formPub_of_B _ _ _ _ hs hB) hd

-- Negative tests, at `Toy.p` changed: the first stage's h is k + 1; the list `oracles` is empty.
#guard !formPubB { Toy.p with nums := { Toy.p.nums with
  stages := Toy.p.nums.stages.modify 0 fun s => { s with h := s.k + 1 } } }
#guard !formPubB { Toy.p with oracles := [] }

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.formPub_of_B
#print axioms ProofFile.Honest.K12.formPubB_toy
#print axioms ProofFile.Honest.K12.formPubB_came
#print axioms ProofFile.Honest.K12.formPubB_late
#print axioms ProofFile.Honest.K12.formPubB_KR
#print axioms ProofFile.Honest.K12.formAsks_KR
#print axioms ProofFile.Honest.K12.formPubB
