-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: A COUNT OF THE VERIFIER's CHALLENGES ALONE: no prover, no filling, no run and no coin is read.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupMarksPayTheFallsPremise.lean: the kind "lookup" (K3): THE PREMISE hK3 OF
THE SMALLNESS TEST's AUTHORS' BOUND ON THE FALLS' MEASURE (their fallSmall_k9_least,
Johnson/P1K8R/FallSmallK9Least.lean [not in this library]; not
imported), IN THE TEXT THAT THEY GAVE US IN A LETTER, with the written number `shareOfOneValue 36`
(LookupMarksPayAtAWrittenNumber.lean in this folder) for their open letter kapL. One theorem: one
call of `lookupMarksPayAtAWrittenNumber`, at the condition "true" on the challenges in front and at
the ground of a base.

Limits. Those of LookupMarksPayAtAWrittenNumber.lean. Conditional on the library's head and the cut. THE END IS TYPED
AFTER A LETTER: only a call in Lean over both files shows that it fits their binder.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupMarksPayAtAWrittenNumber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open scoped ENNReal
open VerifiableInference.Desc (Block Chain)
open _root_.Run (ckP)
open OnBytes.Maker (RDT WholeD)
open ProofFile.Honest (Mark MarkDebt KindFits)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The premise hK3, at kapL := `shareOfOneValue 36`.** Conditional on the head and the cut alone. -/
theorem lookupMarksPayTheFallsPremise (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    {pre₁ : List (Block P5J.TS ProofFile.Cl)} {e₁ : Block P5J.TS ProofFile.Cl} (cut : cF.blocksInOrder = pre₁ ++ [e₁]) :
    ∀ A b b' Bt, pre₁ = A ++ b :: b' :: Bt →
      ∀ mk ∈ (ProofFile.Honest.K3.Good.k3Marks Zp Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (ckP .two) mk dsb (fun _ => True) ((mk.share.num : ℝ≥0∞) * shareOfOneValue 36) :=
  lookupMarksPayAtAWrittenNumber h (G₀ := Bs.G₀) cut (PM := fun _ _ => True)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupMarksPayTheFallsPremise
