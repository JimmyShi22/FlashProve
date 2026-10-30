-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/RowsLe.lean: THE CLOSED NUMBER THAT THE FIELD Anumbers OF WHAT IS LEFT OF A LINK's
LAW TAKES AT d := p.rows (`OwesNumbers.hd`: d ≤ 2 ^ 60; the premise hd of numbers_layers3 ..,
Johnson/Desc/First/Link/Law/SortNumbers.lean), AT THE CLOSED CONSTANT. Statements and proofs; one
kernel line with a negative line.

The road is RowsNeZero.lean's: K9's entry at link m is a member of the written list's entries
(k9_entry_written); BY THE KERNEL every entry of that list of 48,293 that bears the name
"BAT-sigma" has at most 2 ^ 60 rows.

What is said.
  `sigmaLeB b es`: the test at a bound b. `sigma_le_written`: **yes at 2 ^ 60.** `sigma_le_tight`:
    THE NEGATIVE LINE: at the bound 1,000,000 it says no (some batching combines more rows than
    that).
  `rows_le`: **(h : AtMg OnBytes.secondHashFunction ..) (hm : m < 25) (hp : IM.k9At Zp m = some p) : p.rows ≤ 2
    ^ 60.**

Limits. o := OnBytes.secondHashFunction. AtMg is a premise. Nothing on soundness.

-/
import Johnson.LPFK9R.RowsNeZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Where)
open Johnson.G (dryProofFull)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open P5J (AtMg)

/-- Every entry of the name "BAT-sigma" has at most b rows. -/
def sigmaLeB (b : ℕ) (es : List Fmt.Entry) : Bool :=
  es.all fun e => !(e.name == "BAT-sigma") || decide (e.rows ≤ b)

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL: at the written list.** -/
theorem sigma_le_written : sigmaLeB (2 ^ 60) (dryProofFull.1.map (·.1.entry)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line. -/
theorem sigma_le_tight : sigmaLeB 1000000 (dryProofFull.1.map (·.1.entry)) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl}

/-- **hd AT d := p.rows, AT THE CONSTANT.** -/
theorem rows_le (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (m : ℕ) (hm : m < 25)
    (p : Where) (hp : IM.k9At Zp m = some p) : p.rows ≤ 2 ^ 60 := by
  have h1 := List.all_eq_true.1 sigma_le_written _ (k9_entry_written h m hm p hp)
  have h2 : decide ((VerifiableInference.Desc.K9.entry p).rows ≤ 2 ^ 60) = true := by
    simpa [VerifiableInference.Desc.K9.entry] using h1
  exact of_decide_eq_true h2

end LPFK9

#print axioms LPFK9.sigma_le_written
#print axioms LPFK9.sigma_le_tight
#print axioms LPFK9.rows_le
