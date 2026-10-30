-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/NumberPrices/ProofAtWrittenTeeth.lean: where the closed fact on the proof file's
prices (`ProofPricesWritten`, Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean) and its test bite,
and where they do not. The tools are those of Johnson/Desc/Ok/NumberPrices/KeyAtWrittenTeeth.lean.

`not_proofPriced_of_above` is a tool at the written lists. All else are facts on written files that
are bent here.

Definitions.
  `fineProof`: `proofThree` with the error of the record 31 of the first plan raised by one part in
    1024: a round "RNG", whose price is the bound itself (`rng_at_bound`), so that any increase at
    all is above it.
  `bentProof`, `halvedProof`: `proofThree` with the error of the record 19 of the second plan
    doubled, halved: the round "FOLD round" whose price stands nearest to the bound in that plan
    (0.006 of a bit, by the same program).
  `struckProof`: all errors of all three plans struck to 0.
Statements.
  `rng_at_bound`: the record 31 of the first plan has the name "RNG", no work and the error
    2 ^ -128. `rng_all_at_bound`: so has every record "RNG" of that plan. `rng_count`: the plan has
    25 such rounds. `rng_nowhere_else`: the proof file's two other plans and the key file's three
    have none.
  Where the test and the statement bite. `fine_proof_lit_no`: at `fineProof` the test on the first
    plan says no. `fine_proof_plan_no`: `Desc.chainOk 20` says no at the whole plan.
    `not_proofPrices_fine`: ¬ ProofPricesAt fineProof. `bent_proof_walk`: at `bentProof` the walk
    still says yes. `bent_proof_lit_no`, `bent_proof_no`: the test says no. `bent_proof_plan_no`:
    `Desc.chainOk 28` says no at the whole plan. `not_proofPriced_bent`: ¬ ProofPricedAt bentProof:
    the half on `PricedAt` is itself false there.
  Where the walk bites, at the second chain: `walkP_dropped_no`: with the last run dropped;
    `walkP_longer_no`: with one more round in front. Each time the walk says no.
  Where they do not bite, and must not. `halved_proof_ok`, `halved_proof_priced`: with that error
    halved the test says yes and the statement holds. `struck_proof_ok`, `struck_proof_priced`: with
    every error struck to 0 the test says yes and the statement holds.
By evaluations in Lean's kernel (`decide +kernel`): `rng_at_bound`, `rng_all_at_bound`,
`rng_nowhere_else`, inside `rng_count`, `fine_proof_lit_no`, `bent_proof_walk`, `bent_proof_lit_no`,
`walkP_dropped_no`, `walkP_longer_no`, `halved_proof_lit`, `struck_proof_lit0`, `1`, `2`, and the
premises inside `fine_proof_plan_no`, `bent_proof_plan_no`, `not_proofPriced_bent`. All else is by
proof.

What of OnBytes/Model/ is used: nothing by name.

Limits. At `fineProof` the statement is refuted here through its half on `Desc.chainAll`; that the
half on `PricedAt` fails there too is in
Johnson/Desc/Ok/NumberPrices/ProofAtWrittenFirst.lean. A
doubled error is caught only where the price has less than one bit of room. A smaller error passes
every clause: only a law from below, on a count, can catch it. For the rounds "RNG" there is one in
the library (Johnson/Flat/NoRoomSmall.lean); it is not laid against these records here. Nothing on
soundness.

-/
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
import Johnson.Desc.Ok.NumberPrices.KeyAtWrittenTeeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes.Params OnBytes.Flat OnBytes.Flat.Held OnBytes.Maker
open Johnson.G Johnson.G.Runs

/-- A plan of the second chain with a round above the bound: the half on `PricedAt` is false. -/
theorem not_proofPriced_of_above {T : Three}
    (h : ∃ r ∈ chainRounds T.B.plan, aboveB 20 r = true) : ¬ ProofPricedAt T := by
  intro H
  have H2 : List.Forall₂ Number.PricedAt writtenPFull.ds₂ (chainRounds T.B.plan) := H.2.1
  obtain ⟨r, hr, hb⟩ := h
  obtain ⟨d, _, P⟩ := f2_right H2 r hr
  exact not_pricedAt_of_above (above_of_test hb) P

/-! ## The bent plans -/

def fineProof : Three :=
  { proofThree with
    A := ⟨pricedProofSetFull, scaleAt 31 finer pricedProofRecsFull0, pricedProofRunsFull0⟩ }
def bentProof : Three :=
  { proofThree with
    B := ⟨pricedProofSetFull, scaleAt 19 twice pricedProofRecsFull1, pricedProofRunsFull1⟩ }
def halvedProof : Three :=
  { proofThree with
    B := ⟨pricedProofSetFull, scaleAt 19 halved pricedProofRecsFull1, pricedProofRunsFull1⟩ }

/-- All errors of all three plans struck to 0. -/
def struckProof : Three :=
  ⟨⟨pricedProofSetFull, pricedProofRecsFull0.map struck, pricedProofRunsFull0⟩,
    ⟨pricedProofSetFull, pricedProofRecsFull1.map struck, pricedProofRunsFull1⟩,
    ⟨pricedProofSetFull, pricedProofRecsFull2.map struck, pricedProofRunsFull2⟩⟩

/-! ## Where the test and the statement bite -/

/-- The record 31 of the first plan: a round "RNG" without work whose error is the bound itself. -/
theorem rng_at_bound : (pricedProofRecsFull0[31]?).any (fun r =>
    r.entry.name == "RNG" && r.entry.work == 0 && decide (r.error = ⟨1, -128⟩)) = true := by
  decide +kernel

/-- Every record "RNG" of the first plan has no work and the bound itself as its error. -/
theorem rng_all_at_bound : pricedProofRecsFull0.all (fun r =>
    r.entry.name != "RNG" || (r.entry.work == 0 && decide (r.error = ⟨1, -128⟩))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The first plan has 25 rounds "RNG". -/
theorem rng_count :
    (proofThree.A.plan.rounds.filter fun r => r.entry.name == "RNG").length = 25 := by
  have e : proofThree.A.plan.rounds = unrunG pricedProofRecsFull0 pricedProofRunsFull0 := rfl
  rw [e, count_unrunG]
  decide +kernel

/-- The proof file's two other plans and the key file's three have no record "RNG". -/
theorem rng_nowhere_else :
    (pricedProofRecsFull1 ++ pricedProofRecsFull2 ++ pricedKeyRecsFull0 ++ pricedKeyRecsFull1 ++
      pricedKeyRecsFull2).all (fun r => r.entry.name != "RNG") = true := by
  decide +kernel

/-- **With one price at the bound raised by one part in 1024 the test says no.** -/
theorem fine_proof_lit_no :
    litOk 20 40000 dryProofRecsFull dryProofRunsFull0 fineProof.A = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The whole plan is refused too.** -/
theorem fine_proof_plan_no : Desc.chainOk 20 fineProof.A.plan = false :=
  chainOk_false_of_idx (n := 0) (i := 31) (by decide +kernel) (by decide +kernel)

/-- **So the statement is false there.** -/
theorem not_proofPrices_fine : ¬ ProofPricesAt fineProof := by
  intro H
  have h1 := ((Desc.chainAll_iff 20 _).1 H.2.1).1
  rw [fine_proof_plan_no] at h1
  cases h1

/-- At the bent plan the walk still says yes: the entries are untouched. -/
theorem bent_proof_walk :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 40000
      (valRuns dryProofRecsFull dryProofRunsFull1)
      (chainRuns (scaleAt 19 twice pricedProofRecsFull1) pricedProofRunsFull1) = true := by
  decide +kernel

/-- **The test on the bent plan says no.** -/
theorem bent_proof_lit_no :
    litOk 28 40000 dryProofRecsFull dryProofRunsFull1 bentProof.B = false := by
  decide +kernel

/-- **So the test on the three says no.** -/
theorem bent_proof_no : proofLitOk 40000 bentProof = false := by
  simp [proofLitOk, bent_proof_lit_no]

/-- **The whole bent plan is refused too.** -/
theorem bent_proof_plan_no : Desc.chainOk 28 bentProof.B.plan = false :=
  chainOk_false_of_idx (n := 1) (i := 19) (by decide +kernel) (by decide +kernel)

/-- **At the three plans with one price doubled the half on `PricedAt` is false.** -/
theorem not_proofPriced_bent : ¬ ProofPricedAt bentProof :=
  not_proofPriced_of_above
    (mem_chain_of_idx (n := 1) (i := 19) (by decide +kernel) (by decide +kernel))

/-! ## Where the walk bites -/

/-- With the priced plan's last run dropped the walk says no. -/
theorem walkP_dropped_no :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 40000
      (valRuns dryProofRecsFull dryProofRunsFull1)
      (chainRuns pricedProofRecsFull1 pricedProofRunsFull1.dropLast) = false := by
  decide +kernel

/-- With a run of one more round in front it says no. -/
theorem walkP_longer_no :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 40000
      (valRuns dryProofRecsFull dryProofRunsFull1)
      (chainRuns pricedProofRecsFull1 ((1, 0) :: pricedProofRunsFull1)) = false := by
  decide +kernel

/-! ## Where they do not bite, and must not -/

theorem halved_proof_lit :
    litOk 28 40000 dryProofRecsFull dryProofRunsFull1 halvedProof.B = true := by
  decide +kernel

/-- With that price halved the test says yes. -/
theorem halved_proof_ok : proofLitOk 40000 halvedProof = true :=
  Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨Bool.and_eq_true_iff.2 ⟨proof_recs0, proof_walk0⟩, halved_proof_lit⟩,
    Bool.and_eq_true_iff.2 ⟨proof_recs2, proof_walk2⟩⟩

/-- **And the statement holds.** -/
theorem halved_proof_priced : ProofPricedAt halvedProof :=
  (pricedOfThree 40000 halvedProof).2 halved_proof_ok

set_option maxRecDepth 1000000 in
theorem struck_proof_lit0 :
    litOk 20 40000 dryProofRecsFull dryProofRunsFull0 struckProof.A = true := by
  decide +kernel

theorem struck_proof_lit1 :
    litOk 28 40000 dryProofRecsFull dryProofRunsFull1 struckProof.B = true := by
  decide +kernel

theorem struck_proof_lit2 :
    litOk 20 40000 dryProofRecsFull dryProofRunsFull2 struckProof.C = true := by
  decide +kernel

/-- With every error struck to 0 the test says yes. -/
theorem struck_proof_ok : proofLitOk 40000 struckProof = true :=
  Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨struck_proof_lit0, struck_proof_lit1⟩,
    struck_proof_lit2⟩

/-- **And the statement holds**: it then serves the count 0 alone. -/
theorem struck_proof_priced : ProofPricedAt struckProof :=
  (pricedOfThree 40000 struckProof).2 struck_proof_ok

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.not_proofPriced_of_above
#print axioms VerifiableInference.Number.ByRuns.rng_at_bound
#print axioms VerifiableInference.Number.ByRuns.rng_all_at_bound
#print axioms VerifiableInference.Number.ByRuns.rng_count
#print axioms VerifiableInference.Number.ByRuns.rng_nowhere_else
#print axioms VerifiableInference.Number.ByRuns.fine_proof_lit_no
#print axioms VerifiableInference.Number.ByRuns.fine_proof_plan_no
#print axioms VerifiableInference.Number.ByRuns.not_proofPrices_fine
#print axioms VerifiableInference.Number.ByRuns.bent_proof_walk
#print axioms VerifiableInference.Number.ByRuns.bent_proof_lit_no
#print axioms VerifiableInference.Number.ByRuns.bent_proof_no
#print axioms VerifiableInference.Number.ByRuns.bent_proof_plan_no
#print axioms VerifiableInference.Number.ByRuns.not_proofPriced_bent
#print axioms VerifiableInference.Number.ByRuns.walkP_dropped_no
#print axioms VerifiableInference.Number.ByRuns.walkP_longer_no
#print axioms VerifiableInference.Number.ByRuns.halved_proof_lit
#print axioms VerifiableInference.Number.ByRuns.halved_proof_ok
#print axioms VerifiableInference.Number.ByRuns.halved_proof_priced
#print axioms VerifiableInference.Number.ByRuns.struck_proof_lit0
#print axioms VerifiableInference.Number.ByRuns.struck_proof_lit1
#print axioms VerifiableInference.Number.ByRuns.struck_proof_lit2
#print axioms VerifiableInference.Number.ByRuns.struck_proof_ok
#print axioms VerifiableInference.Number.ByRuns.struck_proof_priced
