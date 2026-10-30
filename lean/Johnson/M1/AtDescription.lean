-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/AtDescription.lean: M1's clause (A3), and the conjunction of all clauses BUT (A4), the lent coins. Statements without
proofs: each a `def … : Prop`.
The head, the plain lines and the names with their places: Johnson/M1/Statement.lean.
-/
import Johnson.M1.Statement
import Johnson.SendSim.Seat.ReadsAtLive

set_option autoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

/-- (A3) AT THE DESCRIPTION THAT verify IS COMPILED FROM: in the goals' scope, where the gate accepts, at every opening of the
maker's value: what the description's own rounds read of sending i's trees, at every due list of challenges, is within the
bound. bud_of_live's form, at all 82 in place of the 52 jobs. -/
def Spec.atDescription : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles), VerifierAndGoals.InScope P = true → FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true →
  ∀ (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
    (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
    IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B →
    ∀ i < 82, ReadsWithin F (parAt i) (treesBefore i)

/-- The written rounds of Johnson/M1/Numbers.lean are the library's own written value, at which its theorems on the description
speak (D_in_scope; drawnW). -/
def Spec.sameRounds : Prop := declW = Johnson.AtFull.Pub.DW

/-- `Spec.M1BareWithoutLent` with (A3), the count at the description. STILL WITHOUT (A4), `Spec.lent` (Johnson/M1/Numbers.lean): that
each coin which a later part spends is charged once, at the real book. So this is NOT the lemma M1 whole. -/
def Spec.M1WithoutLent : Prop := Spec.M1BareWithoutLent ∧ Spec.sameRounds ∧ Spec.atDescription

end OnBytes.M1
