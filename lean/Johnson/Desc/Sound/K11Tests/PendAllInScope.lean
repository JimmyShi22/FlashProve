-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/PendAllInScope.lean: THE CLOSED TEST pendAllB
(Johnson/Top/H0/MergeLaw/PendOfAll.lean: the routine that makes the pending row returns at
the claim of zeros on each unit of the committed table's layout) SAYS YES AT ALL PUBLIC FILES IN
THE GOALS' SCOPE, UNDER THE FIRST ENTRY PIN. It is the one closed test that other files' theorem
on the merge of the claims on the committed table (kind K11; Johnson/K11R/) still has beside its
head. Statements and proofs. Three closed facts are by Lean's kernel.

The test as it stands ("heavy") runs wsPending, which lays an
array of up to 3,076,096 entries for each of 386 units: Lean's kernel does not carry that.
Johnson/Road/K4/PendLight.lean and PendLightBack.lean show, for the like test of the layers'
sub-protocol, that wsPending returns at a leaving of zeros JUST WHERE a "light" test accepts that
walks no array (Johnson/Road/K4/PendLightDefs.lean: arithmetic on the layout's units). Here: this
test's leaving of zeros and the one there are one term; so the heavy test IS the light one; and the
kernel carries the light one.

  (A) skelFac_is · skelClaim_is · leaving_one   the two leavings of zeros are equal
      pendB_eq_light   heavy lay uis n S = light lay uis n S: AT EVERY lay, uis, n, S: NO PREMISE
  (B) lightAllB        the light test at every unit of the layout
      pendAll_eq_light pendAllB lay S = lightAllB lay S
      lightAll_full    at the written sizes' layout and the written shape it says yes: by the kernel
      rows_bent        a negative twin: with one row more in the shape it says no (a first guard)
      unit_bent        a negative twin: with one row more in the layout's unit 0 it says no (by an
                       evaluation, no theorem: of the light test's guards unitOkB alone says no
                       there: 321 rows against 320 coefficients; the other 385 units still pass)
      NO NEGATIVE TWIN HERE REACHES THE LAST GUARD, coverB.
  (C) wsLay_in_scope_O the committed table's layout is the written sizes', at every o : SecondHashFunctionArgument
      pendAll_in_scope MAIN

hy IS A PREMISE: the first entry pin (in the entry tests' first thirteen rows). It is not paid here.

Limits. That the premises can be met together is not shown here. The full size alone. Nothing on a
verifier's state. Nothing on soundness.

-/
import Johnson.Road.K4.PendLight
import Johnson.Road.K4.PendLightBack
import Johnson.Top.H0.MergeLaw.PendOfAll
import Johnson.Top.H0.MergeLaw.PlanNumsAt
import Johnson.Top.H0.Fill.D1At
import Johnson.Goal.Numbers.KeyPlansAtPure
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open OnBytes OnBytes.Model
open OnBytes.Params (recordLines)
open Lk6.AtPlan Johnson.G
open VerifiableInference.PlanWritten
open VerifiableInference.PlanWritten.Joined (first_written_in_scope)
open VerifiableInference.Desc.First (FillP1.d1At)
open VerifiableInference.Desc.First.MergeLaw (pendAllB skelFac skelClaim skelRec skelOut hlay_at)
open OnBytes.Desc.First.K4.Total (zeroFac zeroClaim planWoOf)
open OnBytes.Road.K4.Pend (pend_returns pend_back)

/-! ## (A) The two tests are one -/

theorem skelFac_is (g : WsGrp) : skelFac g = zeroFac g := rfl

theorem skelClaim_is (lay : WsLay) (ui : ℕ) : skelClaim lay ui = zeroClaim lay ui := by
  unfold skelClaim zeroClaim
  cases lay.U[ui]? <;> rfl

/-- **The two leavings of zeros are one term.** -/
theorem leaving_one (lay : WsLay) (uis : List ℕ) :
    skelOut lay.lk (uis.map (skelRec lay)) = planWoOf lay uis := by
  unfold skelOut planWoOf
  congr 1
  exact List.map_congr_left fun ui _ => by unfold skelRec; rw [skelClaim_is]

/-- **THE HEAVY TEST IS THE LIGHT ONE.** -/
theorem pendB_eq_light (lay : WsLay) (uis : List ℕ) (n : ℕ) (S : Params.LinShape) :
    VerifiableInference.Desc.First.MergeLaw.pendB lay uis n S =
      OnBytes.Road.K4.Pend.pendB lay uis n S := by
  unfold VerifiableInference.Desc.First.MergeLaw.pendB
  rw [leaving_one, Bool.eq_iff_iff]
  constructor
  · intro h
    refine pend_back ?_
    cases hw : wsPending lay (planWoOf lay uis) n S with
    | ok w => rfl
    | error e => rw [hw] at h; cases h
  · intro h
    have r := pend_returns h
    cases hw : wsPending lay (planWoOf lay uis) n S with
    | ok w => rfl
    | error e => rw [hw] at r; cases r

/-! ## (B) The light test at every unit, and the kernel -/

/-- The light test at every unit of the layout. -/
def lightAllB (lay : WsLay) (S : Params.LinShape) : Bool :=
  (List.range lay.U.size).all fun ui => OnBytes.Road.K4.Pend.pendB lay [ui] 1 S

theorem pendAll_eq_light (lay : WsLay) (S : Params.LinShape) :
    pendAllB lay S = lightAllB lay S := by
  unfold pendAllB lightAllB
  congr 1
  funext ui
  exact pendB_eq_light lay [ui] 1 S

/-- **At the written sizes' layout and the written shape the light test says yes at every unit.** By
the kernel. -/
theorem lightAll_full :
    (match wsLayOf wsFull true recordLines.blockLog with
      | .ok l => lightAllB l proofSizedFull.batch.shape
      | .error _ => false) = true := by decide +kernel

/-- A negative twin: one row more in the shape. By the kernel. -/
theorem rows_bent :
    (match wsLayOf wsFull true recordLines.blockLog with
      | .ok l => lightAllB l { proofSizedFull.batch.shape with
          matrixRows := proofSizedFull.batch.shape.matrixRows + 1 }
      | .error _ => true) = false := by decide +kernel

/-- A negative twin: one row more in the layout's unit 0, the layout's number of rows as it was. By
the kernel. -/
theorem unit_bent :
    (match wsLayOf wsFull true recordLines.blockLog with
      | .ok l => lightAllB { l with U := l.U.modify 0 fun u => { u with rows := u.rows + 1 } }
          proofSizedFull.batch.shape
      | .error _ => true) = false := by decide +kernel

/-! ## (C) In scope -/

section
variable {P : VerifierAndGoals.PublicFiles} {o : ProofFile.SecondHashFunctionArgument}

/-- The committed table's layout is the written sizes', at every function o : SecondHashFunctionArgument. -/
theorem wsLay_in_scope_O {lay : Option ByteArray} {X : Verify.Public}
    (hS : VerifierAndGoals.InScope P = true) (hO : publicOfO o P.pol P.KL lay = .ok X) :
    wsLayOf wsFull true recordLines.blockLog = .ok X.layers.wsLay := by
  obtain ⟨v, hv⟩ := inScope_policy hS
  rw [hv] at hO
  exact (VerifiableInference.Number.ByRuns.args_of_steps (publicSteps_of_O hO)).2

/-- **THE CLOSED TEST SAYS YES IN SCOPE, UNDER THE FIRST PIN.** -/
theorem pendAll_in_scope {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} (hS : VerifierAndGoals.InScope P = true)
    (h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G₀) :
    pendAllB (K11.parOf Z G₀).lay (FillP1.d1At Z).lin = true := by
  have hl := wsLay_in_scope_O hS (ProofFile.Law.pub_public h)
  have hf := lightAll_full
  rw [hl] at hf
  rw [← hlay_at hG, pendAll_eq_light]
  show lightAllB Z.p.X.layers.wsLay Z.first.lin = true
  rw [(first_written_in_scope hS h hy).2.1]
  exact hf

end

end LT28.K11Tests

#print axioms LT28.K11Tests.skelFac_is
#print axioms LT28.K11Tests.skelClaim_is
#print axioms LT28.K11Tests.leaving_one
#print axioms LT28.K11Tests.pendB_eq_light
#print axioms LT28.K11Tests.pendAll_eq_light
#print axioms LT28.K11Tests.lightAll_full
#print axioms LT28.K11Tests.rows_bent
#print axioms LT28.K11Tests.unit_bent
#print axioms LT28.K11Tests.wsLay_in_scope_O
#print axioms LT28.K11Tests.pendAll_in_scope
