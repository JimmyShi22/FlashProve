-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/YesSize.lean: table_yes_in_scope (Scope/Join.lean) with hsz paid by the side
library's lay_size (AtFullSide/Layout/Size.lean). One theorem; nothing is evaluated.

Limits. The steps' relation and RunsAll's pieces stay premises. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Scope.Join
import AtFullSide.Layout.Size

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- table_yes_in_scope, with no premise on the layout file's size. -/
theorem table_yes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hS : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      SameRead Zp.p.X X₀ → ∀ n, n < 358 →
        CellRel Zp.p.X X₀ n (TabL.cells (LW Zp.p.X) n) (TabL.cells (LW X₀) n))
    (len : Nat → Nat) (c : Nat → ShA) (K : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = 358) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true :=
  table_yes_in_scope Johnson.Unfolds.Layout.lay_size h hB hS len c K hp h0 hK

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.table_yes
