-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ColsFitAtBuilt.lean: the smallness test (K8), public data alone: in
the goals' scope, under an opening of the description, the record of each of the 25 built segments
has `DigitColsFit` (Johnson/Desc/ProofFile/Honest/K8/AddressLaw.lean): the test on the matrices'
first rows passes, there is a matrix, and the list has as many matrices as are counted. So the
record's count of columns is the sum of its matrices' rows. Three theorems; no definition.

  `cols_at_built`   the library's test `DgP.colsTest` at the built segment's record: by
                  `IM.ground_tails` (Johnson/IMR/K8Seat.lean) and `Fo.ZPlan.public_cols`
  **`digitColsFit_at_built`**   with `matrix_at_built`, `made_count`
                  (Johnson/Desc/K8/Honest/HeldOutright.lean) and `made_at_built`
                  (Johnson/P1K8R/SecondLaidAtBatch.lean)
  `mz_at_built`     by `mz_allRows`: it meets the premise hmz of `hSt_at_head`
                  (Johnson/Desc/ProofFile/Honest/K8/ZzStateAtHead.lean)
AddressLaw.lean's head calls the second owed.
No option is raised; one instance is taken away, as in the files beneath. Tactics that search:
`omega` on two lines, on l.
Limits. The scope, the files read and the opening are hypotheses. The full size alone. No prover, no
Script, no input, no coin, no witness.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.AddressLaw
import Johnson.Desc.K8.Honest.HeldOutright
import Johnson.P1K8R.SecondLaidAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Claim FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Honest

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The test on the matrices' first rows passes at each built segment's record. -/
theorem cols_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : DgP.colsTest Xl.tl = true := by
  obtain ⟨tails, l24, e24, t24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨cG, cA, cH⟩ := _root_.Fo.ZPlan.public_cols O.public
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : l24 = Xl := Option.some.inj (e24.symm.trans e3)
    rw [t24]
    exact cH
  · obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    have hg12 : g < 12 := by omega
    obtain ⟨hp, a, x, x', ehp, ea, ex, etl, -, -, -, -, ex', etl', -⟩ := tails g hg12
    rcases hg with rfl | rfl
    · obtain rfl : x = Xl := Option.some.inj (ex.symm.trans e3)
      rw [etl]
      exact cG g hp ehp
    · obtain rfl : x' = Xl := Option.some.inj (ex'.symm.trans e3)
      rw [etl']
      exact cA g a ea

/-- **Each built segment's record has `DigitColsFit`.** -/
theorem digitColsFit_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) {l : ℕ}
    (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : DigitColsFit Xl.tl :=
  ⟨cols_at_built hS hR O hl e3, matrix_at_built hS hR O hOk hl e3,
    made_count (P1K8.made_at_built hS hR O hl e3)⟩

/-- The record's count of columns is the sum of its matrices' rows. -/
theorem mz_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) {l : ℕ}
    (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    Xl.tl.mz = allRows (parOfTail Xl.tl) :=
  mz_allRows Xl.tl (digitColsFit_at_built hS hR O hOk hl e3)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.cols_at_built
#print axioms ProofFile.Honest.K8.digitColsFit_at_built
#print axioms ProofFile.Honest.K8.mz_at_built
