-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/StepSide15At.lean: THE STEP AT k = 15 OF THE TABLES' FILES' FOLD OF THE STATE's SIDE OF THE PROMISE ALONG THE FIRST CHAIN's HISTORY, AT THOSE FILES' OWN DEFINITIONS AND IN THE LETTER OF THE FIELD Gaps.g15 (Johnson/Top/Fire/Code/KeyASideAtFk.lean). Two statements; each proof is a call.
OBJECT. LPFD.StepInv (Johnson/Top/Fire/Code/ReachedInv.lean) · Johnson.RunOne.KeyRows1.ASide (Johnson/RunOne/KeyASide.lean) · the block at (Fk X N P).first.blocksInOrder[15]. USER. aSide_of_hist (Johnson/Top/Fire/Code/KeyASideAtFk.lean): its premise G : Gaps X N P at_, field g15.
LETTERS. X N P at_: free. PREMISES: hpl : (descriptionFromSource X N P).planOk = true · hl : the plan has two lookups · hft : N.nums.firstTree = 0 (the maker of the place's numbers lays 0; numbers_parts, K12Facts15A.lean, has it off rangesNumbers m = .ok N).
  aSide_is: StepSide15.lean's ASide IS that of Johnson/RunOne/KeyASide.lean: by rfl. g15: the field.
Limits. A block that says no to all meets the statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.StepSide15
import Johnson.RunOne.Law.K12Facts15
import Johnson.RunOne.KeyASide
import Johnson.Top.Fire.Code.ReachedInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.StepSide15At
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim)
open Johnson.RunOne.KeyRows23 (Fk oneAt)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.Law.StepSide15 (step_15)
open Johnson.RunOne.Law.K12Facts15 (rng_plan)
open Johnson.RunOne.Law.K12Join15 (stages_of_fileOk lengths_of_fileOk)

/-- StepSide15.lean's text of the state's side is that of Johnson/RunOne/KeyASide.lean. -/
theorem aSide_is (one : OneTime) (at_ : Where) (k : Nat) (s : FirstState) :
    Johnson.RunOne.Law.StepSide15.ASide one at_ k s = Johnson.RunOne.KeyRows1.ASide one at_ k s := rfl

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (at_ : Where)

/-- **The field Gaps.g15 (Johnson/Top/Fire/Code/KeyASideAtFk.lean).** -/
theorem g15 (hpl : (descriptionFromSource X N P).planOk = true) (hl : (lookupsOf X.Y.k.oneTime).length = 2) (hft : N.nums.firstTree = 0) :
    ∀ b, (Fk X N P).first.blocksInOrder[15]? = some b →
      LPFD.StepInv b (Johnson.RunOne.KeyRows1.ASide (oneAt X) at_ 15) (Johnson.RunOne.KeyRows1.ASide (oneAt X) at_ 16) := by
  intro b hb
  have hat : (descriptionFromSource X N P).first.blocksInOrder[2 + 6 * (lookupsOf X.Y.k.oneTime).length + 1]? =
      some (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N)) := Johnson.RunOne.Sound.fk_rng_at X N P
  rw [hl] at hat
  have hb' : (descriptionFromSource X N P).first.blocksInOrder[15]? = some b := hb
  obtain rfl : bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N) = b := Option.some.inj (hat.symm.trans hb')
  have hf := (((descriptionFromSource X N P).planOk_ok).1 hpl).fileOk
  exact step_15 X.Y.k.oneTime N at_ (rng_plan X N P hpl) (stages_of_fileOk X N P hf) hft (lengths_of_fileOk X N P hf) _ rfl

end Johnson.RunOne.Law.StepSide15At

#print axioms Johnson.RunOne.Law.StepSide15At.aSide_is
#print axioms Johnson.RunOne.Law.StepSide15At.g15
