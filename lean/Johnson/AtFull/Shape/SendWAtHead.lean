-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SendWAtHead.lean: W's SENDING AT THE MEMORY (the place M:4; member 356 of the
flat list of the proof file's own first chain): WHAT THE SEAT HOLDS, HALF BY HALF, BOTH WAYS. Under
the head P5J.AtMgA; a joining of laws; nothing is evaluated.
  `wPar Zp msg`: the parameters of K1's sending there, off the public part: K1.parW at the first
    chain's parameters, the public part's numbers of samples and of the first tree, piece 4, and the
    messages msg.
  **`sendW_at`**: with msg what linMessageW reads off the first chain's parameters: the member b at
    number 356 of cF.blocksInOrder says yes from s to t just if K1's own sending (K1.sendAtS (wPar Zp msg),
    Johnson/Desc/K1/AtS.lean) says yes from s to some m on the first two rounds, kind K13's quiet
    sub-protocol behind it (K13.rowsB K13.atS (K13.whereOf Zp), Johnson/Desc/K13/Kind.lean: the
    request's own group and the row (Eval)) says yes from m to t, t bears no mark, and t has s's
    reply. EVERY LETTER IS NAMED: b by its number, msg by its reader.
By IM.back_of and IM.back_numbers (Johnson/IMR/BackSeat.lean: behind the links the fourth block is
K13.atM4 at K13.wBlock's block, alone; its number in the flat list), IM.yes_alone
(Johnson/IMR/SeatForm.lean), and the texts of K13.wBlock (Johnson/Desc/ProofFile/Lot/K13At4.lean),
K1.wAt (Johnson/Desc/K1/Places.lean), K13.atM4 (Johnson/Desc/K13/AtS.lean) and Block.andThen.
Limits. NO STEP ON THE CHAIN's SHAPE IS LAID HERE: the first half has one at the bare block (wG,
sendW_carries, sendW_returns: Johnson/Desc/First/Shape/SendW.lean); the second half has one in
Johnson/Desc/First/Shape/RowsBehindW.lean (rowsBG, with "carries" alone); SendWStepAtHead.lean joins
the two, with two further tests in front of rowsBG. UNDER THE HEAD: that it has a member is shown in
scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean);
that these three hold together, at two named sets of public files (`VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap`), in a side library (AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). Of
the head the proof spends h.scope, h.reads and h.laid.opened alone. At the earlier hash
OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.SendW
import Johnson.IMR.BackSeat
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The parameters of W's sending at the memory, off the public part. -/
def wPar (Zp : ProofFile.Pub) (msg : Array OracleNotice) : VerifiableInference.Desc.K1.Par :=
  VerifiableInference.Desc.K1.parW Zp.first
    { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg

theorem sendW_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (b : Block S ProofFile.Cl) (msg : Array OracleNotice),
      linMessageW Zp.first.lin = some msg ∧ cF.blocksInOrder[356]? = some b ∧
      ∀ s t rs gs, b.decide s rs gs = .ok t ↔
        (∃ m, (VerifiableInference.Desc.K1.sendAtS (Cl := Unit) (wPar Zp msg)).decide s
            (rs.take 2) (gs.take (VerifiableInference.Desc.K1.sendAtS (Cl := Unit)
              (wPar Zp msg)).openings) = .ok m ∧
          (VerifiableInference.Desc.K13.rowsB (Cl := Unit) VerifiableInference.Desc.K13.atS
            (VerifiableInference.Desc.K13.whereOf Zp)).decide m (rs.drop 2)
            (gs.drop (VerifiableInference.Desc.K1.sendAtS (Cl := Unit)
              (wPar Zp msg)).openings) = .ok t) ∧
        t.failed = none ∧ ProofFile.sameReply s t = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, -, b, b', w, eb, -, hw, rfl, la⟩ := IM.back_of O
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := (IM.back_numbers h.scope h.reads O).1 3 b eb
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hw
  refine ⟨_, msg, hm, q, fun s t rs gs => ?_⟩
  show b.decide s rs gs = .ok t ↔ _
  rw [hy s t rs gs]
  refine and_congr_left fun _ => ?_
  show ((VerifiableInference.Desc.K1.sendAtS (Cl := Unit) (wPar Zp msg)).decide s _ _).bind _ =
    .ok t ↔ _
  constructor
  · intro hd
    obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 hd
    exact ⟨m, h1, h2⟩
  · rintro ⟨m, h1, h2⟩
    exact (VerifiableInference.Desc.K1.bind_ok _ _ _).2 ⟨m, h1, h2⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sendW_at
#print axioms Johnson.AtFull.Shape.wPar
