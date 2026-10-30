-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/RowsNeZero.lean: THE FIELD "rows" OF WHAT IS LEFT OF A LINK's LAW AT EACH SORT OF
LINK (`LayersRest3`, `AttRest3`, `HeadRest3`; it is LinkShare's second field): p.rows ≠ 0, AT THE
CLOSED CONSTANT: at the numbers p that the plan names for K9 at link m. Statements and proofs;
kernel lines with a negative one.

Why. "The batching combines at least one row" stands as a premise (hp0, hp, rows) in six
files of the link's law. By a search by name and by the sentence's end over the library's
sources in another version and K9's files' folders no theorem ended in it.

The road: NO INDEX IS COUNTED. (1) K9's one declared round at link m, k9Decl p, stands among the
first chain's sub-protocols' declared rounds (the batching sits in the flat list:
sits_at_constant). (2) Where the tests on the plan accept, these rounds in a row are the plan's
(decl_of_planOk), and the description's plan is the public part's D (descPure_plans). (3) In scope,
where the value is laid, the plan's entries are the written list's (plans_written, pubBy_entries).
(4) BY THE KERNEL: every entry of the written list of 48,293 that bears the name "BAT-sigma" has
rows ≠ 0. K9's entry bears that name and has p.rows for its rows, by definition.

What is said.
  `sigmaRowsB es`: the test on a list of entries. `sigma_rows_written`: **yes at the written
    list.** `sigma_count_written`: at least 25 entries bear the name: the sentence is not idle.
    `sigma_rows_bent`: THE NEGATIVE LINE: with one such entry of no rows in front the test says no.
  `k9_entry_written`: K9's entry at link m is a member of the written list's entries.
  `rows_ne_zero`: **(h : AtMg OnBytes.secondHashFunction ..) (hm : m < 25) (hp : IM.k9At Zp m = some p) :
    p.rows ≠ 0.**

Limits. o := OnBytes.secondHashFunction (sits_at_constant's). AtMg is a premise. It says "not none", not how
many. Nothing on soundness.

-/
import Johnson.LPFK9R.SitsAtConstant
import Johnson.P5T.FenceAtMg
import Johnson.Goal.Numbers.PlanWrittenPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.K9L (k9Decl)
open VerifiableInference.PlanWritten (plans_written pubBy_entries descPure_plans)
open Johnson.G (dryProofFull)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open P5J (AtMg F0T)

/-- Every entry of the name "BAT-sigma" has a row. -/
def sigmaRowsB (es : List Fmt.Entry) : Bool :=
  es.all fun e => !(e.name == "BAT-sigma") || e.rows != 0

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL: at the written list.** -/
theorem sigma_rows_written : sigmaRowsB (dryProofFull.1.map (·.1.entry)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At least 25 entries bear the name (other kinds' batching rounds bear it too). -/
theorem sigma_count_written :
    25 ≤ ((dryProofFull.1.map (·.1.entry)).filter fun e => e.name == "BAT-sigma").length := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line. -/
theorem sigma_rows_bent :
    sigmaRowsB ({ name := "BAT-sigma", rows := 0 } :: dryProofFull.1.map (·.1.entry)) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl}

/-- K9's entry at link m is a member of the written list's entries. -/
theorem k9_entry_written (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (m : ℕ) (hm : m < 25)
    (p : Where) (hp : IM.k9At Zp m = some p) :
    VerifiableInference.Desc.K9.entry p ∈ dryProofFull.1.map (·.1.entry) := by
  obtain ⟨L, p', Q, -, hp', -, hs⟩ := sits_at_constant h m hm
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
  have hmem : k9Decl p' ∈ (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.1 :=
    List.mem_flatMap.2 ⟨L.batchB, List.mem_of_getElem? hs.flat, by
      rw [hs.rounds]
      exact List.mem_singleton.2 rfl⟩
  rw [VerifiableInference.Desc.Sound.decl_of_planOk _ h.laid.planOk] at hmem
  obtain ⟨Z₁, hZ₁, e₁⟩ := descPure_plans h.laid.value
  obtain rfl : Z₁ = Zp := Except.ok.inj (hZ₁.symm.trans h.laid.pub)
  rw [e₁] at hmem
  obtain ⟨Z₂, hZ₂, w, -, -⟩ := plans_written h.scope h.laid.laidPOf
  obtain rfl : Z₂ = Z₁ := Except.ok.inj (hZ₂.symm.trans h.laid.pub)
  rw [← w, ← (pubBy_entries hZ₂).1]
  exact List.mem_map.2 ⟨_, hmem, rfl⟩

/-- **THE FIELD rows, AT THE CONSTANT.** -/
theorem rows_ne_zero (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (m : ℕ) (hm : m < 25)
    (p : Where) (hp : IM.k9At Zp m = some p) : p.rows ≠ 0 := by
  have h1 := List.all_eq_true.1 sigma_rows_written _ (k9_entry_written h m hm p hp)
  have h2 : ((VerifiableInference.Desc.K9.entry p).rows != 0) = true := by
    simpa [VerifiableInference.Desc.K9.entry] using h1
  simpa [VerifiableInference.Desc.K9.entry] using h2

end LPFK9

#print axioms LPFK9.sigma_rows_written
#print axioms LPFK9.sigma_count_written
#print axioms LPFK9.sigma_rows_bent
#print axioms LPFK9.k9_entry_written
#print axioms LPFK9.rows_ne_zero
