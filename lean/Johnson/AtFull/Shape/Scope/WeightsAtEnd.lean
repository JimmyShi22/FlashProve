-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/WeightsAtEnd.lean: THE PENDING ROWS' WEIGHTS PASS THE DOOR's TEST ON THEIR FORM AT A STATE REACHED OVER THE
FIRST CHAIN: AtPublicFiles.AtFiles.weightsB at (p14At Z).S: from the verifier's own fold: no thread, no prover, no coin.

  LowRows lin₀ s     every weight of every row on the table lies below lin₀'s rows (AtPublicFiles.AtFiles.Low)
  lowRows_law        the sentence meets PileLawAt lin₀: pendingRowO_low, AtPublicFiles.AtFiles.batt_low
  weights_at_reached **at every state reached at 358**

Limits. At the full size, under the head, at 358. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.PileAt
import Johnson.AtFull.Shape.Scope.WeightsLow
import Johnson.LTPileR.WeightsFold
import Johnson.IMR.CodesSeat
import Johnson.IMR.ListsEnds
import Johnson.IMR.RecRun
import Johnson.P5T.FenceAtMg
import Johnson.Top.H0.Walk.ReachCut
import Johnson.AtFull.Shape.PlansAtHead
import Johnson.ToldDescR.RcLastCode
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Door.PileAt

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)
open Meaning.K2
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Tied (Reach)
open AtPublicFiles.AtFiles (Low batt_low weightsB_of_low)
open Johnson.AtFull.Shape.Scope (pendingRowO_low)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open VerifiableInference.PlanWritten (proofSizedFull)

/-- Every weight of every row on the table lies below the rows of lin₀. -/
def LowRows (lin₀ : Params.LinShape) (s : S) : Prop :=
  ∀ r ∈ s.rows, ∀ t ∈ r.g, Low lin₀.kRow lin₀.matrixRows t

theorem lowRows_law (lin₀ : Params.LinShape) : PileLawAt lin₀ (LowRows lin₀) where
  same := fun _ _ q hw r hr => hw r (by rw [← q.1]; exact hr)
  zero := fun _ _ _ _ _ h hw r hr => hw r (by rw [← (openLayZero_rows h).1]; exact hr)
  push := fun X counts left lay s t h hw r' hr' => by
    rcases clearWith_cases h with q | ⟨w, r, os, hr, e, -⟩
    · exact hw r' (by rw [← q.1]; exact hr')
    · rw [e] at hr'
      rcases List.mem_append.1 hr' with a | a
      · exact hw r' a
      · obtain rfl := List.mem_singleton.1 a
        exact pendingRowO_low hr
  batch := fun _ _ _ _ _ h hw r hr => by
    obtain ⟨out, hb, e, e'⟩ := K13.Law.atM3_ok h
    rw [e'] at hr
    obtain rfl := List.mem_singleton.1 hr
    exact batt_low _ _ _ _ _ _ _ _ hb (by rw [← e]; exact hw)

/-- The chain's start holds no row. -/
theorem rows_start {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) : (ProofFile.startS Z p).rows = [] := by
  have e : Z.s₀.rows = [] := by
    have k := pub_start h
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the last chain's shape is the first chain's lin, and both are written. -/
theorem lin_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    Zp.first.lin = proofSizedFull.batch.shape ∧
      Zp.p.chains.made.sized.proof = proofSizedFull :=
  ⟨(VerifiableInference.PlanWritten.first_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.first_of_made
        (VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true])))).2.1,
    VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made
        (VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true])))⟩

set_option maxRecDepth 100000 in
/-- The written shape's two bounds. A closed fact. -/
theorem written_bounds :
    proofSizedFull.batch.shape.kRow ≤ (linLayOmega proofSizedFull.codes proofSizedFull.batch.shape).bits ∧
      (linLayOmega proofSizedFull.codes proofSizedFull.batch.shape).bits ≤ 63 := by
  decide +kernel

/-- **AT EVERY STATE REACHED AT 358.** -/
theorem weights_at_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) (s : S)
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 358 (z, s)) :
    ∀ q ∈ s.rows, AtPublicFiles.AtFiles.weightsB (ToldDesc.p14At Zp).S
      (linLayOmega s.st.codes (ToldDesc.p14At Zp).S) q.g = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hlin, hsz⟩ := lin_at_head h
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := O.pub
  have eS : (ToldDesc.p14At Zp).S = proofSizedFull.batch.shape := by
    show Zp.p.chains.made.sized.proof.batch.shape = _
    rw [hsz]
  obtain ⟨rs, cols, hf, hcut⟩ := hr.cuts
  obtain ⟨t₂, r₂, c₂, -, f₂⟩ := hcut 2 (by omega)
  have hq := start_real h.scope h.reads O f₂
  have ec : s.st.codes = proofSizedFull.codes := by
    have c1 : s.st.codes = (ProofFile.startS Zp z).st.codes :=
      open_fold_all seatKeeps_codes seatBack_codes O trivial (fun _ _ _ => trivial)
        (Johnson.AtFull.Shape.plans_at h) 358 hf
    exact c1.trans ((recAll_startS hZ hq).codes.trans
      (VerifiableInference.PlanWritten.first_in_scope h.scope h.laid.pub
        (VerifiableInference.PlanWritten.first_of_made
          (VerifiableInference.PlanWritten.pinnedAt_of_row
            (by rw [h.toAtMg.pins.1, Bool.or_true])))).1)
  have hlow : LowRows proofSizedFull.batch.shape s :=
    rides_fold (lowRows_law _) O hlin (Johnson.AtFull.Shape.plans_at h) 358 0 hf
      (fun q hq' => by rw [rows_start hZ z] at hq'; cases hq')
  intro q hqs
  rw [eS, ec]
  exact weightsB_of_low _ _ q.g (hlow q hqs) written_bounds.1 written_bounds.2

end Johnson.AtFull.Shape.Door.PileAt

#print axioms Johnson.AtFull.Shape.Door.PileAt.weights_at_reached
