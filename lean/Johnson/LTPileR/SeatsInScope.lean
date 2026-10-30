-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/SeatsInScope.lean: hS AT THE TABLES' OWN LIST OF SEATS (P5T.planSeats), IN SCOPE:
`hS_at_end` (SeatsAtEnd.lean) with two of its three premises on the plan paid by
theorems in scope. One statement with its proof; no definition.

Main name (namespace `Meaning.K2`).
  **`hS_in_scope`**: in scope, at an opening's own chain (at the public files' own layout), where
    `F.planOk` accepts, under hB (`K12.Door.sendsAreB …`), hy (`madePinnedAt …`: a named test on the
    plan) and hl (`proofDataAndDecisionOfPublicFiles`'s return): inside any condition Oc, at `EndAt₁ (ProofFile.seatedAt secondHashFunction Z Np
    c)` with any rider Pp on the public part, without a mark: for every f that `firstOfS` hands on:
    `LLT25.SeatsNumber ((P5T.planSeats Z Z.D.1).map fun p => (p.j, p.t)) f.book`. NO L AND NO seats
    IS A LETTER ANY MORE: the list of places is the written one.

By: `Second.Seam.laidAtCodes_in_scope` (hL, at L := the written list) and
`Second.Seam.seats_places_in_scope` (hs), both at the opening's own `pub`.
Limits. NO MEMBER by theorem. hB stays: its payer (`hB_paid`, Johnson/IMR/EndFiveMade.lean, under
another named test) is not called here. At o := `OnBytes.secondHashFunction`;
the full size alone. Nothing on soundness or on hiding.

-/
import Johnson.LTPileR.SeatsAtEnd
import Johnson.Second.Seam.SeatsPlacesInScope
import Johnson.Second.Seam.CodesOneInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.PlanWritten (madePinnedAt)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (EndAt₁)

/-- **hS, IN SCOPE, AT THE PLAN's OWN SEATS.** -/
theorem hS_in_scope {P : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hB : K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL = .ok (D, r)) (Np : H2U.Places4)
    (Pp : ProofFile.InstPub → Prop) (Oc : ProofFile.InstPub × S → Strs → Prop) :
    ∀ q y, Oc q y → (EndAt₁ (ProofFile.seatedAt OnBytes.secondHashFunction Z Np c) q ∧ Pp q.1) →
      q.2.failed = none → ∀ f, firstOfS q.2 = some f →
        LLT25.SeatsNumber ((P5T.planSeats Z Z.D.1).map fun p => (p.j, p.t)) f.book :=
  hS_at_end hS O hF hB (Second.Seam.laidAtCodes_in_scope hS O.pub hy hl) _
    (Second.Seam.seats_places_in_scope hS O.pub hy hl) Np Pp Oc

#print axioms hS_in_scope

end Meaning.K2
