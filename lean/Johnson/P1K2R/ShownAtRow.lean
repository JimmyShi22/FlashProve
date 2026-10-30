-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/ShownAtRow.lean: code switching (K2): THE CLAUSE «shownAll» ON THE PIECE (behind the
piece every member whose tree the piece's stretch sends is shown: Piece.ShownAll,
Johnson/Desc/Sound/ShownOfData.lean) AT EVERY PIECE OF THE ROW (h.row L, at the closed
constant), FROM ONE PREMISE: SeatFits. Free of any kind. Every step a call. NO BLOCK IMPORTS THIS
FILE.
  shownAll_at_row   (h.row L)[i]? = some q · SeatFits (F0T secondHashFunction Zp Np cF) cs m seat ⟹ q.ShownAll
                    (F0T secondHashFunction Zp Np cF) cs m seat
HOW. shownOfData asks five things: the data of the written rounds (as in P5J.AtMg.ofDesc)
· F.sentFit (sentFit_of_planOk) · the two counts of told oracles
(Desc.K14.Law.Fence.counts_of_planOk) · SeatFits · Three.IsCut of the rows' maker: the maker
piecesAt IS Three.ofCuts by its text, and that is a cut by ofCuts_isCut (rfl three times). No
example. No soundness is claimed.
-/
import Johnson.P1K2R.PieceAtRow
import Johnson.Desc.Sound.ShownOfData
import Johnson.Desc.Sound.OraclesAre
import Johnson.Desc.Sound.SeamDesc
import Johnson.Desc.Sound.TilesMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Maker OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (SeatFits shownOfData ofCuts_isCut sentFit_of_planOk held
  restCap sealRound besideAt allOf)

theorem shownAll_at_row {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (i : Nat)
    (q) (hq : (h.row L)[i]? = some q) {cs : Codes} {m : List (OracleShape × Nat)}
    {seat : Fin m.length → Nat × Nat}
    (hS : SeatFits (P5J.F0T OnBytes.secondHashFunction Zp Np cF) cs m seat) :
    q.ShownAll (P5J.F0T OnBytes.secondHashFunction Zp Np cF) cs m seat := by
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth h.scope h.laid]
    exact h.laid.data
  obtain ⟨c1, c2⟩ := Desc.K14.Law.Fence.counts_of_planOk (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
    "proof file" (D.at frS.P.T.a) h.laid.planOk hD
  have hc := ofCuts_isCut (ckP .two) (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) 0 0
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber (held L.c₁) (L.k₁.map held) (held L.c₂)
    (L.k₂.map held) (held L.c₃) (L.k₃.map held) (restCap L.e₁) (restCap L.e₂) (restCap L.e₃)
    sealRound (besideAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) L.dW L.wEnd)
  exact (shownOfData _ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) "proof file" (D.at frS.P.T.a) hD
    (sentFit_of_planOk _ h.laid.planOk) c1 c2 cs m seat hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ hc).1 q (List.mem_of_getElem? hq)

end P1K2

#print axioms P1K2.shownAll_at_row
