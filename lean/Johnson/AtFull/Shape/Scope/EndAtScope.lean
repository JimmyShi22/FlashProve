-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/EndAtScope.lean: AT THE BORDERS OUTSIDE THE ATTENTION LINKS THE STATE's SHAPE AT ANY
Z IS THE SHAPE AT THE STORED FILES; SO WHAT THE THIRD CHAIN's START ASKS OF THE FIRST CHAIN's END
FOLLOWS FROM ONE BOOL AT THE WRITTEN BORDER. A joining; nothing is evaluated.

* shape_at_border: under the head at any Z, where oddAt b = false and the run at the stored files
  returns c at b, a state at which the family shapeJ holds at b has the shape c.
* sized_at_head: under the head at any Z the planner's sizes of the proof file are the written ones:
  so the LinShape that the third chain reads at Zp is proofSizedFull.batch.shape at every Z.
* first_out_at_end: at b = 358, from endOk at that written shape, one Bool: EndLaws.lean's conclusion
  at that state.

Limits. hc and hcl are closed facts at the stored files, owed by the caller; the family shapeJ at
the state is the caller's. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.YesAll
import Johnson.AtFull.Shape.Scope.EndLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Third (firstOutFrom firstOfS)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (shapeJ)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **Outside the attention links the state's shape at any Z is the stored files' border.** -/
theorem shape_at_border (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {b : Nat} (hb : b ≤ 358) (hO : oddAt b = false) {c : ShA}
    (hc : (shapeL (LWn X₀)).run b startShA = .ok c) {s : S}
    (hJ : shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA b s) : shA s = c := by
  rcases run_at_scope h hB hX₀ b hb with ⟨c1, c2, e1, e2, q⟩ | ⟨-, n2⟩
  · have e : c2 = c := Except.ok.inj (e2.symm.trans hc)
    subst e
    have q' : c1 = c2 := by
      unfold RelAt at q
      rw [hO] at q
      exact q
    have e3 : shA s = c1 := Except.ok.inj (Eq.trans (Eq.symm hJ) e1)
    exact e3.trans q'
  · rw [hc] at n2
    cases n2

/-- **Under the head at any Z the planner's sizes of the proof file are the written ones.** -/
theorem sized_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
  VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
    (VerifiableInference.PlanWritten.sized_of_made
      (VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true])))

/-- **The first chain's end, from one Bool at the written border.** -/
theorem first_out_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {c : ShA} (hc : (shapeL (LWn X₀)).run 358 startShA = .ok c)
    (hcl : endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape c = true) {s : S}
    (hJ : shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA 358 s) :
    s.noneWaits = true ∧ ∃ f, firstOfS s = some f ∧
      ∃ o, firstOutFrom Zp.p.chains.made.sized.proof.batch.shape f.st f.book f.roots f.w f.own f.mask
        f.pending = some o := by
  rw [sized_at_head h]
  have e := shape_at_border h hB hX₀ (le_refl _) (oddAt_behind (by omega)) hc hJ
  rw [← e] at hcl
  exact firstOut_of_endOk hcl

/-- The third chain's shape at the public part is the planner's. -/
theorem pAt_S (Zp : ProofFile.Pub) : (ProofFile.pAt Zp).S = Zp.p.chains.made.sized.proof.batch.shape := rfl

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.pAt_S
#print axioms Johnson.AtFull.Shape.Scope.shape_at_border
#print axioms Johnson.AtFull.Shape.Scope.sized_at_head
#print axioms Johnson.AtFull.Shape.Scope.first_out_at_end
