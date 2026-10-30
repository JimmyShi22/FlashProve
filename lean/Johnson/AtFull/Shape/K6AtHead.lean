-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K6AtHead.lean: THE OUTPUT HEAD's OWN ROUNDS (the place H:4, the kind K6; member
341 of the flat list) AT ITS SEAT IN THE PROOF FILE's OWN FIRST CHAIN: the member has one step on
the chain's shape, with both laws at the seated block's own decision. Under the head P5J.AtMgA; a
joining of laws; nothing is evaluated.
  `k6GS h`: the step at the seat: no mark; then k6G h (Johnson/Desc/First/Shape/HeadOwnStep.lean).
  **`k6_at`**: the member b at number 341 of cF.blocksInOrder is such that, at the step k6GS (P5J.At.X
    Zp).hS: where b says yes and the step returns, it returns the shape behind, and the statement is
    as it was (so the makes of its rows stay); and b says yes, at what its step shows it, wherever
    the state in front is ready (another house's K6Front) and the rounds and columns pass the step's
    own tests on form (Block.Fits). THE STEP's ONE PARAMETER IS A FUNCTION OF THE PUBLIC PART.
By another house's laws, called: P4.k6_member_at_mg (Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean: the
member's form, at the full size), K6MemberIs.decide_iff (Law/K6WayUp.lean), member_returns
(Johnson/Desc/K6/Honest/Law/Returns.lean); and k6_carries (HeadOwnStep.lean), k6_shapes
(HeadOwnRounds.lean).
Limits. "Carries" is under the step's own return. "RETURNS" TAKES A PREMISE ON THE STATE BEYOND ITS
SHAPE: of K6Front's clauses two cannot be read off the chain's shape: the state's own test on the
request's words, and that each call's key point ends as the lookup's point does (an equality of
field elements in the carried record); the others (no mark; the head's link opened; the points laid;
a token heard; lengths; the ledger's sizes; room) are not tied here to the step's return either: the
second law does not speak of the step. UNDER THE HEAD: that it has a member is shown in scope, where
the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these
three hold together, at two named sets of public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side
library (AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). Of the head the proof spends
h.toAtMg alone. "The statement is as it was" stands under the step's return, though the proof draws
it from the yes alone. NO STATE IS SHOWN AT WHICH THE STEP RETURNS. At the earlier hash
OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.HeadOwnStep
import Johnson.Desc.K6.Honest.Law.Returns
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName OpenedColumn noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Kinds.Head.Law (K6Front K6MemberIs)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **The step at the seat**: no mark; then k6G (Johnson/Desc/First/Shape/HeadOwnStep.lean). -/
def k6GS (h : Model.Head.Shape) (a : ChainSh) : Option ChainSh :=
  if a.marked then none else k6G h a

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k6_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[341]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t → k6GS (P5J.At.X Zp).hS (chainSh s) = some u →
        u = chainSh t ∧ t.st = s.st) ∧
      ∀ s ft rs cols m, K6Front (P5J.At.X Zp) m s → b.Fits ft rs cols →
        ∃ t, b.decide s (rs.map noDigest) (b.shown ft rs cols) = .ok t := by
  obtain ⟨b, q, M⟩ := P4.k6_member_at_mg h.toAtMg
  have hk : IM.k6Place.kind ≠ KindName.K7 := by decide
  have hsm : ∀ s t : S, t.out.reply = s.out.reply → ProofFile.sameReply s t = true := by
    intro s t e
    unfold ProofFile.sameReply
    rw [e]
    exact beq_self_eq_true _
  refine ⟨b, q, fun s rs gs t u hd hg => ?_, fun s ft rs cols m R hF => ?_⟩
  · obtain ⟨h1, -⟩ := (M.decide_iff hk hsm s t rs gs).1 hd
    unfold k6GS at hg
    split at hg
    · cases hg
    · refine ⟨k6_carries _ _ _ _ h1 hg, ?_⟩
      obtain ⟨o, g, F1, X, Q, -, -, -, rfl, -⟩ := k6_shapes _ _ _ _ h1
      rfl
  · obtain ⟨t, -, -, ht, -⟩ := VerifiableInference.Desc.Kinds.Head.Law.member_returns M hk hsm ft R
      rs cols hF
    exact ⟨t, ht⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.k6_at
#print axioms Johnson.AtFull.Shape.k6GS
