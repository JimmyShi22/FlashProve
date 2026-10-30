-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BattAtHead.lean: THE BATCHING OF THE PILE's ROWS (the place M:3, the kind K13;
member 355 of the flat list) AT ITS SEAT IN THE PROOF FILE's OWN FIRST CHAIN: the member has one
step on the chain's shape, with both laws at the seated block's own decision. Under the head
P5J.AtMgA; a joining of laws; nothing is evaluated.
  `battGS P`: the step at the seat: no mark; then battG P (Johnson/Desc/First/Shape/Batching.lean).
  **`batt_at`**: the member b at number 355 of cF.blocksInOrder is such that, at the step battGS (K13.whereOf
    Zp): behind a yes of b the step returns the shape behind (the strong form), and the makes of the
    statement's rows stay; and where the step returns, b says yes on every list of rounds that fits
    the kind's own rounds (K13.battRounds (K13.whereOf Zp)), shown without the sealed digest. THE
    STEP's ONE PARAMETER IS A FUNCTION OF THE PUBLIC PART.
By IM.back_of and IM.back_numbers (Johnson/IMR/BackSeat.lean: behind the links the third block is
the kind's own at the plan's numbers, alone; its number in the flat list), IM.yes_alone
(Johnson/IMR/SeatForm.lean), batt_carries, batt_leaves, batt_returns (Batching.lean).
Limits. "Returns" takes one premise, on the rounds' form; no test on values. UNDER THE HEAD: that it
has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files
(`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library (AtFullSide/Top/HeadMemberAtFull.lean,
HeadMemberAtGap.lean). Of the head the proof spends h.scope, h.reads and h.laid.opened alone. NO
STATE IS SHOWN AT WHICH THE STEP RETURNS. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness,
completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.Batching
import Johnson.IMR.BackSeat
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **The step at the seat**: no mark; then battG (Johnson/Desc/First/Shape/Batching.lean). -/
def battGS (P : VerifiableInference.Desc.K13.Where) (a : ChainSh) : Option ChainSh :=
  if a.marked then none else battG P a

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem batt_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[355]? = some b ∧
      b.rounds = VerifiableInference.Desc.K13.battRounds
        (VerifiableInference.Desc.K13.whereOf Zp) ∧
      (∀ s rs gs t, b.decide s rs gs = .ok t →
        battGS (VerifiableInference.Desc.K13.whereOf Zp) (chainSh s) = some (chainSh t) ∧
        formsOf t.st = formsOf s.st) ∧
      ∀ s rs gs u, battGS (VerifiableInference.Desc.K13.whereOf Zp) (chainSh s) = some u →
        roundsFit (VerifiableInference.Desc.K13.battRounds
          (VerifiableInference.Desc.K13.whereOf Zp)) rs = true →
        ∃ t, b.decide s (rs.map noDigest) gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, ⟨b, b', eb, -, rfl, la⟩, -⟩ := IM.back_of O
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := (IM.back_numbers h.scope h.reads O).1 2 b eb
  refine ⟨_, q, ?_, fun s rs gs t hd => ?_, fun s rs gs u hg hr => ?_⟩
  · show b.rounds = _
    rw [IM.alone_rounds la]
    show ([] ++ VerifiableInference.Desc.K13.battRounds
      (VerifiableInference.Desc.K13.whereOf Zp)) ++ [] = _
    rw [List.append_nil, List.nil_append]
  · obtain ⟨h1, h2, -⟩ := (hy s t rs gs).1 hd
    have h1' : (VerifiableInference.Desc.K13.atM3 (Cl := Unit)
        (VerifiableInference.Desc.K13.whereOf Zp)).decide s rs gs = .ok t := h1
    obtain ⟨k1, -, k3⟩ := batt_leaves h1'
    refine ⟨?_, k3⟩
    unfold battGS
    have hm : (chainSh s).marked = false := by
      show s.failed.isSome = false
      rw [← k1, h2]
      rfl
    rw [hm]
    exact batt_carries h1'
  · unfold battGS at hg
    split at hg
    · cases hg
    · rename_i hm
      obtain ⟨t, ht⟩ := batt_returns hg rs hr gs
      obtain ⟨k1, k2, -⟩ := batt_leaves ht
      have hf : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hm
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      refine ⟨t, (hy s t _ gs).2 ⟨ht, k1.trans hf, ?_⟩⟩
      unfold ProofFile.sameReply
      rw [k2]
      exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.batt_at
#print axioms Johnson.AtFull.Shape.battGS
