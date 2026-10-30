-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/SeatsOneTest.lean: hS, IN SCOPE, UNDER ONE NAMED TEST ON THE PLAN: `hS_in_scope`
(SeatsInScope.lean) with its premise hB struck. Statements with their proofs; no definition.
Two named tests on one plan stand behind hS; what would
close the question is that the one gives the other at the same arguments.

Main names (namespace `Meaning.K2`).
  `madeRow_in_scope`: in scope, at the computed public part: `madePinnedAt Z.p.X.P Z.p.chains.made
    Z.first Z.made = true → madeRow Z = true`. By `pinnedAt_row`
    (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean: the first test IS "if the key is the full size's
    then madeRow Z else true", by rfl, at these very arguments) and `key_in_scope_pure`
    (Johnson/Goal/Numbers/KeyInScope.lean).
  **`hS_one_test`**: `hS_in_scope` WITHOUT hB: by `hB_paid`
    (Johnson/IMR/EndFiveMade.lean) at `madeRow_in_scope`. LEFT: scope · the opening · `F.planOk` ·
    hy (`madePinnedAt …`: the ONE named test) · hl (`proofDataAndDecisionOfPublicFiles`'s return).

Limits. NO MEMBER by theorem: that hy is met at the release's files is an evaluation's matter. At o
:= `OnBytes.secondHashFunction`; the full size alone. Nothing on soundness or on hiding.

-/
import Johnson.LTPileR.SeatsInScope
import Johnson.IMR.EndFiveMade
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Goal.Numbers.KeyInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.PlanWritten (madePinnedAt madeRow pinnedAt_row key_in_scope_pure)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (EndAt₁)

/-- **In scope the one named test gives the other**, at the same arguments. -/
theorem madeRow_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) : madeRow Z = true := by
  rw [pinnedAt_row, if_pos (key_in_scope_pure hW h)] at hy
  exact hy

/-- **hS, IN SCOPE, UNDER ONE NAMED TEST.** -/
theorem hS_one_test {P : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL = .ok (D, r)) (Np : H2U.Places4)
    (Pp : ProofFile.InstPub → Prop) (Oc : ProofFile.InstPub × S → Strs → Prop) :
    ∀ q y, Oc q y → (EndAt₁ (ProofFile.seatedAt OnBytes.secondHashFunction Z Np c) q ∧ Pp q.1) →
      q.2.failed = none → ∀ f, firstOfS q.2 = some f →
        LLT25.SeatsNumber ((P5T.planSeats Z Z.D.1).map fun p => (p.j, p.t)) f.book :=
  hS_in_scope hS O hF (hB_paid hS hF (madeRow_in_scope hS O.pub hy) Bs base A B O) hy hl Np Pp Oc

#print axioms madeRow_in_scope
#print axioms hS_one_test

end Meaning.K2
