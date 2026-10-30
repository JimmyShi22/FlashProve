-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/Teeth.lean: where the tests `Desc.chainOk` (Johnson/Desc/MadeOk.lean)
and `Desc.keyFit`, `Desc.entryFit`, `Desc.proofFit` (Johnson/Desc/FitOk.lean), over which
`PricesGeneral` (Johnson/Desc/Ok/NumberPrices/Stated.lean) and `PricesAt`
(Johnson/Desc/Ok/NumberPrices/AtRelease.lean) are stated, say no, and which silly plans the first
lets pass.

WHERE THINGS STAND. No file under this folder imports a file under Ladder/: where the three public
files occur they are the letters pol, lay, KL; where a bound on a round's error occurs it is a
literal. `PricesAtRelease`, `PricesAtGap`, `PricesRungs`, `pricesRungs`, `PricesNamed`,
`pricesNamed_of`, `prices_at_release`, `below_step`, `pricedAt_of_release`, wherever a head under
this folder names them, stand in Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library].

THE THEOREMS HERE ARE TOOLS. No line under Owed/ [not in this library] is to be laid on them.

Statements and proofs. The plans here are small records written for the purpose, at the default
setting (the format's field, target 128); the tests on them are evaluated by `decide`.

Main names. The test can say no:
  `chainOk_false_of_round`: a plan with a round that does not hold is refused, at every w.
  `chainOk_false_of_work`: so is a plan with a round of more than w bits of work.
  `chainOk_false_of_target`: so is a plan whose target is not 128.
  `chainOk_false_of_side`: so is a plan of which the side conditions `sideB` say no.
  `deepPositions_no`, `moreNonzero_no`: the plan of one round with error 0 whose positions have 65
    bits, and the one that marks one element as never 0 and draws none, are refused at every w, by
    the side conditions; `zeroError_yes` is the control.
  `target127_no`: the plan with no rounds and the target 127 is refused.
  `fullError_no`: the plan of one round with error 1 and no work is refused at w = 128.
  `oneBit_no`, `oneBit_yes`: the plan of one round with error 0 and one bit of work is refused at w
    = 0 and passes at w = 1.
The tests on the format's words can say no. c: any record of what the planner makes.
  `keyFit_false_of`, `proofFit_false_of`: a record with a plan that does not fit is refused.
  `wideWord_no`: the plan of one round whose message has 2^64 bytes does not fit; `wideWord_yes`: at
    2^64 - 1 bytes it fits: the control. `badName_no`: the plan of one round whose name is a line
    feed does not fit.
  `keyFit_wide_no`, `entryFit_wide_no`, `proofFit_wide_no`: c with that first plan for the key's
    only plan (the entry's plan; the proof's only plan) is refused; `keyFit_wide_yes`: with the
    control it passes. `keyFit_none_yes`: c with no plan for the key passes.
The premise of `PricesGeneral` is needed:
  `fullError_not_priced`: PricesOf 128 is false of the plan of `fullError_no`: (G1) would say 1 ≤
    (1/2)^128.
Silly plans that pass:
  `empty_yes`: the plan with no rounds. `zeroError_yes`: the plan of one round with error 0. Of
    these two `PricesGeneral` holds idly.
  `allWork_yes`, `allWork_no`: the plan of one round that draws one position, with error 1 and 128
    bits of work, passes at w = 128; it is refused at w = 32. `allWork_equal`: of it (G1) holds with
    equality: all 128 bits are work.
  `idle_at_128`: 2^128 (1/2)^128 = 1: at w = 128 clause (G3) says that a price is at most 1.

Limits: nothing on `Desc.madeOk`, and nothing on the plan of any public files: neither test is shown
to say yes of a plan that the planner makes. That the silly plans are barred elsewhere (by a test
that the blocks' rounds are the plan's entries; by laws that bound counts by these very errors; by
the values of w in `Desc.madeOk`) is not shown here.


-/
import Johnson.Desc.Ok.NumberPrices.Proved

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number
open OnBytes.Params OnBytes.Flat.Held

/-- A plan with a round that does not hold is refused. -/
theorem chainOk_false_of_round (w : ℕ) (P : Planned) (r : PlanRound) (hr : r ∈ P.rounds)
    (h : roundHolds P.set (capped P.set) r = false) : Desc.chainOk w P = false := by
  by_contra hc
  have hy := (chainOk_parts (Bool.not_eq_false _ ▸ hc : Desc.chainOk w P = true)).1
  have := List.all_eq_true.1 (rounds_hold hy) r hr
  rw [h] at this
  exact Bool.false_ne_true this

/-- A plan with a round of more than w bits of work is refused. -/
theorem chainOk_false_of_work (w : ℕ) (P : Planned) (r : PlanRound) (hr : r ∈ P.rounds)
    (h : w < r.entry.work) : Desc.chainOk w P = false := by
  by_contra hc
  have hy := (chainOk_parts (Bool.not_eq_false _ ▸ hc : Desc.chainOk w P = true)).2.2.2 r hr
  omega

/-- A plan whose target is not 128 is refused. -/
theorem chainOk_false_of_target (w : ℕ) (P : Planned) (h : P.set.target ≠ 128) :
    Desc.chainOk w P = false := by
  by_contra hc
  exact h (chainOk_parts (Bool.not_eq_false _ ▸ hc : Desc.chainOk w P = true)).2.2.1

/-- A plan of which the side conditions say no is refused. -/
theorem chainOk_false_of_side (w : ℕ) (P : Planned) (h : sideB P = false) :
    Desc.chainOk w P = false := by
  by_contra hc
  have hy := (chainOk_parts (Bool.not_eq_false _ ▸ hc : Desc.chainOk w P = true)).2.1
  rw [h] at hy
  exact Bool.false_ne_true hy

/-- One round with error 0 whose positions have 65 bits: refused at every w. -/
theorem deepPositions_no (w : ℕ) :
    Desc.chainOk w ⟨{}, [{ entry := { name := "", logN := 65 } }]⟩ = false :=
  chainOk_false_of_side w _ (by decide)

/-- One round with error 0 that marks one element as never 0 and draws none: refused at every w. -/
theorem moreNonzero_no (w : ℕ) :
    Desc.chainOk w ⟨{}, [{ entry := { name := "", drawNZ := 1 } }]⟩ = false :=
  chainOk_false_of_side w _ (by decide)

/-- No rounds, and the target 127: refused. -/
theorem target127_no (w : ℕ) : Desc.chainOk w ⟨{ target := 127 }, []⟩ = false :=
  chainOk_false_of_target w _ (by decide)

/-- One round with error 1 and no work: refused. -/
theorem fullError_no :
    Desc.chainOk 128 ⟨{}, [{ entry := { name := "" }, error := ⟨1, 0⟩ }]⟩ = false := by decide

/-- Of that plan `PricesOf` is false. -/
theorem fullError_not_priced :
    ¬ PricesOf 128 ⟨{}, [{ entry := { name := "" }, error := ⟨1, 0⟩ }]⟩ := by
  intro h
  have h1 := (h.1 _ (List.mem_singleton.2 rfl)).1
  have e : price ⟨{}, [{ entry := { name := "" }, error := ⟨1, 0⟩ }]⟩
      { entry := { name := "" }, error := ⟨1, 0⟩ } = 1 := by
    show ((1 : ℕ) : ℚ) * (2 : ℚ) ^ (0 : ℤ) = 1
    norm_num
  rw [e] at h1
  norm_num at h1

/-- One round with error 0 and one bit of work: refused at w = 0. -/
theorem oneBit_no :
    Desc.chainOk 0 ⟨{}, [{ entry := { name := "", work := 1 } }]⟩ = false := by decide

/-- The same plan passes at w = 1. -/
theorem oneBit_yes :
    Desc.chainOk 1 ⟨{}, [{ entry := { name := "", work := 1 } }]⟩ = true := by decide

/-- The plan with no rounds passes. -/
theorem empty_yes : Desc.chainOk 0 ⟨{}, []⟩ = true := by decide

/-- The plan of one round with error 0 passes. -/
theorem zeroError_yes : Desc.chainOk 0 ⟨{}, [{ entry := { name := "" } }]⟩ = true := by decide

/-- One round that draws one position, with error 1 and 128 bits of work: passes at w = 128. -/
theorem allWork_yes :
    Desc.chainOk 128 ⟨{}, [{ entry := { name := "", work := 128, poss := 1 }, error := ⟨1, 0⟩ }]⟩ =
      true := by decide

/-- The same plan is refused at w = 32. -/
theorem allWork_no :
    Desc.chainOk 32 ⟨{}, [{ entry := { name := "", work := 128, poss := 1 }, error := ⟨1, 0⟩ }]⟩ =
      false := by decide

/-- Of that plan's round clause (G1) holds with equality. -/
theorem allWork_equal :
    price ⟨{}, [{ entry := { name := "", work := 128, poss := 1 }, error := ⟨1, 0⟩ }]⟩
      { entry := { name := "", work := 128, poss := 1 }, error := ⟨1, 0⟩ } / 2 ^ 128 =
        (2⁻¹ : ℚ) ^ 128 := by
  show ((1 : ℕ) : ℚ) * (2 : ℚ) ^ (0 : ℤ) / 2 ^ 128 = (2⁻¹ : ℚ) ^ 128
  norm_num

/-- At w = 128 clause (G3) says that a price is at most 1. -/
theorem idle_at_128 : (2 : ℚ) ^ 128 * (2⁻¹ : ℚ) ^ 128 = 1 := by norm_num

/-! ### The tests on the format's words -/

/-- A record with a plan for the key that does not fit is refused. -/
theorem keyFit_false_of {c : Configured} {P : Planned} (hP : P ∈ c.key)
    (h : P.plan.fit = false) : Desc.keyFit c = false := by
  by_contra hc
  have hy := List.all_eq_true.1 (Bool.not_eq_false _ ▸ hc : Desc.keyFit c = true) P hP
  rw [h] at hy
  exact Bool.false_ne_true hy

/-- A record with a plan for the proof that does not fit is refused. -/
theorem proofFit_false_of {c : Configured} {P : Planned} (hP : P ∈ c.proof)
    (h : P.plan.fit = false) : Desc.proofFit c = false := by
  by_contra hc
  have hy := List.all_eq_true.1 (Bool.not_eq_false _ ▸ hc : Desc.proofFit c = true) P hP
  rw [h] at hy
  exact Bool.false_ne_true hy

/-- One round whose message has 2^64 bytes: the plan does not fit the format's words. -/
theorem wideWord_no :
    (⟨{}, [{ entry := { name := "", msg := 2 ^ 64 } }]⟩ : Planned).plan.fit = false := by decide

/-- The control: at 2^64 - 1 bytes it fits. -/
theorem wideWord_yes :
    (⟨{}, [{ entry := { name := "", msg := 2 ^ 64 - 1 } }]⟩ : Planned).plan.fit = true := by
  decide

/-- One round whose name is a line feed: the plan does not fit the format's words. -/
theorem badName_no : (⟨{}, [{ entry := { name := "\n" } }]⟩ : Planned).plan.fit = false := by
  decide

theorem keyFit_wide_no (c : Configured) :
    Desc.keyFit { c with key := [⟨{}, [{ entry := { name := "", msg := 2 ^ 64 } }]⟩] } = false :=
  keyFit_false_of (List.mem_singleton.2 rfl) wideWord_no

theorem entryFit_wide_no (c : Configured) :
    Desc.entryFit { c with entry := ⟨{}, [{ entry := { name := "", msg := 2 ^ 64 } }]⟩ } = false :=
  wideWord_no

theorem proofFit_wide_no (c : Configured) :
    Desc.proofFit { c with proof := [⟨{}, [{ entry := { name := "", msg := 2 ^ 64 } }]⟩] } =
      false :=
  proofFit_false_of (List.mem_singleton.2 rfl) wideWord_no

theorem keyFit_wide_yes (c : Configured) :
    Desc.keyFit { c with key := [⟨{}, [{ entry := { name := "", msg := 2 ^ 64 - 1 } }]⟩] } =
      true :=
  List.all_eq_true.2 fun P hP => by
    rw [List.mem_singleton.1 hP]
    exact wideWord_yes

/-- A record with no plan for the key passes. -/
theorem keyFit_none_yes (c : Configured) : Desc.keyFit { c with key := [] } = true := rfl

end VerifiableInference.Number

#print axioms VerifiableInference.Number.chainOk_false_of_round
#print axioms VerifiableInference.Number.chainOk_false_of_work
#print axioms VerifiableInference.Number.chainOk_false_of_target
#print axioms VerifiableInference.Number.chainOk_false_of_side
#print axioms VerifiableInference.Number.deepPositions_no
#print axioms VerifiableInference.Number.moreNonzero_no
#print axioms VerifiableInference.Number.target127_no
#print axioms VerifiableInference.Number.fullError_no
#print axioms VerifiableInference.Number.fullError_not_priced
#print axioms VerifiableInference.Number.oneBit_no
#print axioms VerifiableInference.Number.oneBit_yes
#print axioms VerifiableInference.Number.empty_yes
#print axioms VerifiableInference.Number.zeroError_yes
#print axioms VerifiableInference.Number.allWork_yes
#print axioms VerifiableInference.Number.allWork_no
#print axioms VerifiableInference.Number.allWork_equal
#print axioms VerifiableInference.Number.idle_at_128
#print axioms VerifiableInference.Number.keyFit_false_of
#print axioms VerifiableInference.Number.proofFit_false_of
#print axioms VerifiableInference.Number.wideWord_no
#print axioms VerifiableInference.Number.wideWord_yes
#print axioms VerifiableInference.Number.badName_no
#print axioms VerifiableInference.Number.keyFit_wide_no
#print axioms VerifiableInference.Number.entryFit_wide_no
#print axioms VerifiableInference.Number.proofFit_wide_no
#print axioms VerifiableInference.Number.keyFit_wide_yes
#print axioms VerifiableInference.Number.keyFit_none_yes
