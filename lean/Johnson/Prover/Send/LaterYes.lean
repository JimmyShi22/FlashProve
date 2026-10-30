-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Send/LaterYes.lean: a segment's later moment of the kind K1 (K1.laterAt,
Johnson/Desc/K1/Places.lean: a commitment at a place's parameters) RETURNS on two rounds that fit
the kind's rounds, where the commitment's step on the SHAPE of the verifier's state returns. One
statement: three calls.

Main names (namespace Johnson.Prover.Send).
  later_yes_of_shape: roundsFit at the place's rounds, and commitG at the shape of the state returns
    t: then the member's own decision returns some m, whose shape is t.

By: commit_returns (Johnson/Desc/First/Shape/Commit.lean): the same from "no seed's factor is 0" and
"round 2 holds as many answers as the place counts" · factors_of_fit (Johnson/Prover/Send/Form.lean)
and K1.answers_len (Johnson/Desc/K1/Law/When.lean): these two from roundsFit.

Limits. THE WEIGHT LIES IN THE PREMISE ON THE SHAPE: that commitG returns at any state is shown
nowhere. It is the member's decide, not its step; bare: nothing on the member as a chain seats it,
or with a step without a round joined behind it. Nothing on what is sent. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Send.Form
import Johnson.Desc.First.Shape.Commit
import Johnson.Desc.K1.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (commitG chainSh ChainSh commit_returns)

/-- **A segment's later moment returns where its step on the shape does**, on rounds that fit. -/
theorem later_yes_of_shape {q : OnBytes.Params.First} {gp : _root_.Desc.Plain.GPar}
    {link piece moment : Nat} {arrays : Option (List Nat)} {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {t : ChainSh}
    (hfit : roundsFit (K1.rounds (K1.parLater q gp link piece moment)) [r₁, r₂] = true)
    (hg : commitG (K1.parLater q gp link piece moment) link moment arrays (chainSh s) = some t) :
    ∃ m, (K1.laterAt (Cl := Unit) q gp link piece moment arrays).decide s [r₁, r₂] gs = .ok m ∧
      chainSh m = t :=
  commit_returns hg (factors_of_fit _ r₁ r₂ hfit) (K1.answers_len _ r₁ r₂ hfit)

end Johnson.Prover.Send

#print axioms Johnson.Prover.Send.later_yes_of_shape
