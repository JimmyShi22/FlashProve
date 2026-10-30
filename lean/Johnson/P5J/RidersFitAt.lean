-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/RidersFitAt.lean: THE CLOSED TEST `ridersFitB` AT EVERY BORDER OF THE FIRST CHAIN, AT
THE COMPOSED MEANING's CONSTANT: BY THE KERNEL. Four theorems, ten controls.

Why. `ReadsOwed.fit` (Johnson/P5J/ReadsAtHead.lean) asks `ridersFitB` at the composed meaning's own
list of further public items. That list is a closed term (`mgMore`, by `mgAll_more_closed`,
Johnson/Desc/Sound/MgAllAt.lean): so the test is one on written lists alone.

What is said. `At.ridersFit_all`: the test accepts at all borders from 0 to the list's length, at
`mgMore`. `At.ridersFit_at`: so at each. `AtMgA.fit`: the field `fit` of `ReadsOwed`, to the letter.
The controls: nine of the ten arms of `riderFitB` that can say no say no at a bent item (`pileOne`,
whose test is `pile`'s, has no control); and the whole test says no on the list of places without
its first three: for other arms' reasons: that control bears no news on the fence on
`formsT … "weights"`.

Limits. A test on the table. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.ReadsAtHead
import Johnson.Desc.Sound.MgAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (ridersFitB riderFitB mgAll mgBase mgMore mgAll_more_closed)
open OnBytes.Maker (WholeD)

theorem At.ridersFit_all :
    (List.range (At.ps.length + 1)).all (fun i => ridersFitB mgMore At.links At.ps i) = true := by
  decide +kernel

/-- A test that holds at all numbers up to n holds at each. -/
theorem all_range_at {n : ℕ} {p : ℕ → Bool} (h : (List.range (n + 1)).all p = true) (i : ℕ)
    (hi : i ≤ n) : p i = true :=
  List.all_eq_true.1 h i (List.mem_range.2 (Nat.lt_succ_of_le hi))

theorem At.ridersFit_at (i : ℕ) (hi : i ≤ At.ps.length) :
    ridersFitB mgMore At.links At.ps i = true :=
  all_range_at At.ridersFit_all i hi

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The field `fit` of `ReadsOwed`.** -/
theorem AtMgA.fit (h : AtMgA o Z D r Zp Np cF x) (i : ℕ) (hi : i ≤ At.ps.length) :
    ridersFitB (mgAll h.𝔇 mgBase).more At.links At.ps i = true := by
  rw [mgAll_more_closed h.𝔇 mgBase rfl]
  exact At.ridersFit_at i hi

-- CONTROLS: nine of the ten arms that can say no do (`pileOne`, whose test is `pile`'s, has none)
example : riderFitB mgMore At.links At.ps 100 (.constr 25 .idn) = false := by decide +kernel
example : riderFitB mgMore At.links At.ps 100 (.worth 24 3 "keys") = false := by decide +kernel
example : riderFitB mgMore At.links At.ps 100 (.formsT 24 4 "weights") = false := by decide +kernel
example : riderFitB mgMore At.links At.ps 0 (.wo 0) = false := by decide +kernel
example : riderFitB mgMore At.links At.ps 0 (.row 0 .carried) = false := by decide +kernel
example : riderFitB mgMore At.links At.ps 100 (.row 0 (.sample 3)) = false := by decide +kernel
example : riderFitB mgMore At.links At.ps 100 (.tie 0) = false := by decide +kernel
example : riderFitB mgMore At.links At.ps 100 .wrow = false := by decide +kernel
example : riderFitB mgMore At.links [] 1 .pile = false := by decide +kernel
example : (List.range (At.ps.length - 2)).all
    (fun i => ridersFitB mgMore At.links (At.ps.drop 3) i) = false := by decide +kernel

end P5J

#print axioms P5J.all_range_at
#print axioms P5J.At.ridersFit_all
#print axioms P5J.At.ridersFit_at
#print axioms P5J.AtMgA.fit
