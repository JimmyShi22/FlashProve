-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/FileOk.lean: a key file's description passes its test on the file (fileOk: 63
named clauses and openedInBlocks; Johnson/Desc/Key/FileOk.lean, Desc.lean), under Pins and four
premises on parts of X.

The premises beside Pins, and why they are no written values.
  hread: the three chains' values are what the program's reader returns on some three strings of
  bytes. It gives the clauses "setting", "read", the halves of "codes" and "shape" on the items'
  bytes, and shapeClauses' tenth (laws: KB9/FileRead.lean).
  hcfg: the digest as read is not 32 zero bytes: the clause "digest" in its own words.
  hmade: the clause "made" in its own words (a law that ends in it: KB9/FileMade.lean).
  hunits: the clause "weights" in its own words (KB9/FileWeights.lean).
How each other clause is had. Carried from the written slim values, where Lean's kernel has
evaluated it (CFile.lean; Slim.lean): 23 of sourceClauses' 30, 10 of shapeClauses' 12, planClauses'
9. By rewriting with Pins to a closed fact: "ranges" (admitted_full), the program's own Key.admitted
(keyOk_full), "prices" (keyAll_full), "opened" (COpened.lean), the four "stages" and the three "k12"
(CFile.lean). By rewriting alone: "priced". From the three equations of CRounds.lean: "declared".

Main names: source_of, shape_of, plan_of, clauses_of, fileOk_of.
Limits. That the premises can be met together is shown nowhere here: hread is had only where the
planner's bytes are read back. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Pins
import Johnson.HB.LLHARD.KB4.COpened
import Johnson.HB.LLHARD.KB4.CRounds
import Johnson.HB.LLHARD.KB9.FileRead
import Johnson.Goal.PlanValues.KeyOkFull
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)
open VerifiableInference.Number.ByRuns (keyThree)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {b₁ b₂ b₃ : ByteArray}

theorem ranges_of (h : Pins X N P) : Wf.admitted X.Y.k.oneTime.codes X.Y.k.oneTime.ranges
    (Wf.matrixOf X.Y.k.oneTime.lin) = true := by
  rw [h.codes₁, h.ranges, h.lin₁]
  exact Lk6.AtPlan.admitted_full

theorem admitted_of (h : Pins X N P) : OnBytes.Key.admitted X.Y.k.oneTime = true := by
  unfold OnBytes.Key.admitted
  rw [h.codes₁, h.lin₁, h.idx, h.ranges, h.binding]
  exact Lk6.AtPlan.keyOk_full

theorem source_of (h : Pins X N P) (hread : KeyChains.read b₁ b₂ b₃ = some X.Y.k)
    (hmade : madeAgainOk X.Y = true)
    (hunits : weightsCovered X.Y.units X.Y.k.oneTime.ranges = true) :
    (sourceClauses X.Y).all (·.2) = true :=
  all_of_carries
    (carries_source X.Y (Johnson.KB9.setting_ok hread)
      (Johnson.KB9.codes_ok hread (h.codes₁.trans h.codes₂.symm))
      (Johnson.KB9.shape_ok hread (h.lin₁.trans h.lin₂.symm)) (Johnson.KB9.read_ok hread) hmade
      (ranges_of h) hunits)
    (by rw [slimY_of h]; exact source_W)

theorem shape_of (h : Pins X N P) (hread : KeyChains.read b₁ b₂ b₃ = some X.Y.k) :
    (shapeClauses X.Y.k X.chains.made.sized.key.once.shape).all (·.2) = true :=
  all_of_carries (carries_shape _ _ (admitted_of h) (Johnson.KB9.read_guard hread))
    (by rw [slimK_of h, h.sized]; exact shape_W)

theorem plan_of (h : Pins X N P) : (planClauses X.Y.k declKeyFull.1.length declKeyFull.2.1.length
    declKeyFull.2.2.length).all (·.2) = true := by
  rw [plan_slim, slimK_of h]
  exact plan_W

theorem prices_of (h : Pins X N P) : VerifiableInference.Desc.keyOk X.chains.made = true := by
  have a := VerifiableInference.Number.ByRuns.keyAll_full
  unfold VerifiableInference.Desc.keyOk
  rw [h.plans]
  show (chainAll 32 keyThree.A.plan && chainAll 32 keyThree.B.plan &&
    chainAll 32 keyThree.C.plan) = true
  rw [a.1, a.2.1, a.2.2]
  rfl

theorem priced_of (h : Pins X N P) : decide (X.chains.made.key.map (·.plan.entries) =
    [X.Y.k.oneTime.given.plan.entries, X.Y.k.shared.given.plan.entries,
      X.Y.k.second.given.plan.entries]) = true := by
  rw [h.plans, h.plan₁, h.plan₂, h.plan₃]
  exact decide_eq_true rfl

theorem opened_of (h : Pins X N P) : openedAsTold X.Y = true := by
  rw [opened_slim, slimY_of h]
  exact opened_full

theorem declared_of (h : Pins X N P) :
    (decide (X.Y.D.1.map (·.entry) = X.Y.k.oneTime.given.rounds) &&
      decide (X.Y.D.2.1.map (·.entry) = X.Y.k.shared.given.rounds) &&
      decide (X.Y.D.2.2.map (·.entry) = X.Y.k.second.given.rounds)) = true := by
  unfold Given.rounds
  rw [h.D, h.plan₁, h.plan₂, h.plan₃, decide_eq_true rounds₁, decide_eq_true rounds₂,
    decide_eq_true rounds₃]
  rfl

/-- **All 63 named clauses.** -/
theorem clauses_of (h : Pins X N P) (hread : KeyChains.read b₁ b₂ b₃ = some X.Y.k)
    (hcfg : (X.Y.k.oneTime.given.cfg != Fmt.zero32) = true) (hmade : madeAgainOk X.Y = true)
    (hunits : weightsCovered X.Y.units X.Y.k.oneTime.ranges = true) :
    (fileClauses X N P declKeyFull.1.length declKeyFull.2.1.length
      declKeyFull.2.2.length).all (·.2) = true := by
  unfold fileClauses
  refine all4 (source_of h hread hmade hunits) (shape_of h hread) (plan_of h) ?_
  refine allCons (prices_of h) (allCons (priced_of h) (allCons (opened_of h)
    (allCons (declared_of h) (allCons ?_ (allCons ?_ (allCons ?_ (allCons ?_ (allCons hcfg
    (allCons ?_ (allCons ?_ (allCons ?_ rfl)))))))))))
  · show stagesAsSized X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.stages N = true
    rw [h.codes₁, h.ranges, h.N]
    exact stages_rng
  · show stagesAsSized X.Y.k.shared.codes X.Y.k.shared.lin.testU P.U = true
    rw [h.codes₂, h.lin₂, h.P]
    exact stages_U
  · show (match P.O with
      | some nO => stagesAsSized X.Y.k.shared.codes X.Y.k.shared.lin.testOmega nO
      | none => X.Y.k.shared.lin.testOmega.isEmpty) = true
    rw [h.codes₂, h.lin₂, h.P]
    exact stages_O
  · show stagesAsSized X.Y.k.shared.codes X.Y.k.shared.lin.testOwn P.W = true
    rw [h.codes₂, h.lin₂, h.P]
    exact stages_own
  · show asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) = true
    rw [h.P]
    exact k12_U
  · show (match P.O with
      | some nO => asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      | none => true) = true
    rw [h.P]
    exact k12_O
  · show asksOnPlan (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) = true
    rw [h.P]
    exact k12_own

/-- **The test on the file.** -/
theorem fileOk_of (h : Pins X N P) (hread : KeyChains.read b₁ b₂ b₃ = some X.Y.k)
    (hcfg : (X.Y.k.oneTime.given.cfg != Fmt.zero32) = true) (hmade : madeAgainOk X.Y = true)
    (hunits : weightsCovered X.Y.units X.Y.k.oneTime.ranges = true) :
    (descriptionFromSource X N P).fileOk = true := by
  show ((fileClauses X N P (descriptionFromSource X N P).roundsDeclaredByBlocks.1.length (descriptionFromSource X N P).roundsDeclaredByBlocks.2.1.length
    (descriptionFromSource X N P).roundsDeclaredByBlocks.2.2.length).all (·.2) &&
      openedInBlocks (descriptionFromSource X N P).roots (descriptionFromSource X N P).roundsDeclaredByBlocks) = true
  rw [decl_of (chainPins_of h), roots_of (chainPins_of h),
    clauses_of h hread hcfg hmade hunits, openedIn_full]
  rfl

end Johnson.KB4

#print axioms Johnson.KB4.ranges_of
#print axioms Johnson.KB4.admitted_of
#print axioms Johnson.KB4.source_of
#print axioms Johnson.KB4.shape_of
#print axioms Johnson.KB4.plan_of
#print axioms Johnson.KB4.prices_of
#print axioms Johnson.KB4.priced_of
#print axioms Johnson.KB4.opened_of
#print axioms Johnson.KB4.declared_of
#print axioms Johnson.KB4.clauses_of
#print axioms Johnson.KB4.fileOk_of
