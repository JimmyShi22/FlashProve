-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/First/Att/Door/Law/K5PieceAll.lean: kind K5: **THE PIECE, THE PLAN AND THE BOOK AT THE COMPOSED MEANING's CLOSED CONSTANT**: what the kind's law at the table asks of the description's piece
q := (h.toAtMg.row 𝔏)[14 (2 g + 1) + 4], of the plan At.X Zp and of the table's numbers At.N Zp cF, from the one head AtMgA and the three flat lists' heads. The facts on the piece are the kind-free
lemmas at the head (atRow_more · atRow_lift · atRow_in · atRow_blocks, Johnson/Desc/Kinds/Law/RowAtConst.lean · RowLenAtConst.lean); what sits at the number and the plan's facts: k5_seat_of_open (Johnson/H2K5R/SeatAtOpen.lean) at the head's own
opening (LaidAt.opened); the book: k5Book_full (Door/Law/K5BookAt.lean). AND: the piece's base is a number off the description's own list (seated_base, Johnson/Desc/Sound/PieceSeated.lean): so what the law asks «below the base» reads no piece.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)

Typed by reading P5J/LaidOpens.lean · AtMg.lean · LettersAt.lean (N · told · ps) · RowAtConst.lean ·
RowLenAtConst.lean.

Main name: k5_piece_all: it pays, of K5LeftAt's fields (Door/Law/K5LeftAt.lean): back · err · rounds · seatOf · runs [Q: all five] · planIs · p4 · planAt · lookC · lookD · plan [N: all six] · book [B]; and of K5Rest's: seated ·
seatedOk · guard [P]: at the letters blk · E · a · x₁ · xd THAT IT FINDS, before := (H2K5.k5Before? Zp ("A" ++ toString g)).getD [], hS := a.seam.tl.f9, kr := slotsOf (script a.own) + Forest.elems a.seam.tl.f9.
IS IT EMPTY HERE? Under the head: A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction;
SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05LawR
import Johnson.Desc.First.Att.Door.Law.K5BookAt
import Johnson.Desc.Kinds.Law.RowAtConst
import Johnson.Desc.Kinds.Law.RowLenAtConst
import Johnson.H2K5R.SeatAtOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker OnBytes.Flat OnBytes.Slice Johnson.Pack KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more atRow_lift atRow_in atRow_blocks)
open P5J (AtMg AtMgA mgAtAll F0T TS Free)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)

/-- **The piece, the plan and the book at the kind's place of group g, at the closed constant.** -/
theorem k5_piece_all (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {g : ℕ} (hg : g < 12)
    {q : Piece (ckP .two) (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (ProofFile.InstPub × TS) ProofFile.Cl
      (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)}
    (hq : (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q) :
    ∃ (blk E : Block First.S Claim) (a : Attention.Plan) (x₁ xd : Look.Place),
      PlanIs (P5J.At.X Zp) ∧ (P5J.At.X Zp).p4 = true ∧ (P5J.At.X Zp).A[g]? = some a ∧ lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ ∧
      lookAt (P5J.At.X Zp) (2 * g + 1) true = some xd ∧
      K5Plan (parO (P5J.At.X Zp) (2 * g + 1) a ((H2K5.k5Before? Zp ("A" ++ toString g)).getD [])).own (2 * g + 1)
        (Look.P.ofPlace (Params.settingOf (P5J.At.X Zp).P.frame) false x₁) (Look.P.ofPlace (Params.settingOf (P5J.At.X Zp).P.frame) true xd)
        a.seam.tl.f9 (Forest.elems a.fs) (slotsOf (script a.own) + Forest.elems a.seam.tl.f9) a.ns ∧
      k5AtN (P5J.At.X Zp) (2 * g + 1) g ((H2K5.k5Before? Zp ("A" ++ toString g)).getD []) = some blk ∧ blk.planOk = true ∧
      k5GuardN (P5J.At.X Zp) (2 * g + 1) g = true ∧
      q.back = [] ∧ q.err = Iop.Err.cap 128 (uLT (ckP .two) q.ds) ∧
      List.Forall₂ RoundAsG q.ds (rounds (parO (P5J.At.X Zp) (2 * g + 1) a ((H2K5.k5Before? Zp ("A" ++ toString g)).getD []))) ∧
      SeatOf blk E ∧ q.b = (below E).lift Prod.snd (fun t s => (t.1, s)) ∧
      K5Book (P5J.At.N Zp cF) ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩ ∧
      q.base = (oraclesOf (cF.blocksInOrder.take (14 * (2 * g + 1) + 4))).length := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  obtain ⟨blk, E, a, x₁, xd, hfl, ho, er, hSe, H⟩ := k5_seat_of_open h.scope h.reads O h.laid.planOk h.laid.asks hg
  rw [hW] at er H
  obtain ⟨hP, h4, ea, hx, hxd, Pn, hat, hok, hG⟩ := H
  obtain ⟨hm, he⟩ := atRow_more h.toAtMg 𝔏 q₁ q₂ q₃ _ q hq (atRow_in h.toAtMg _ (by omega))
  have hb := atRow_lift h.toAtMg 𝔏 q₁ q₂ q₃ _ q E hq hfl
  have er' : q.b.rounds = rounds (parO (P5J.At.X Zp) (2 * g + 1) a ((H2K5.k5Before? Zp ("A" ++ toString g)).getD [])) := by
    rw [hb]
    exact er
  have hds : List.Forall₂ RoundAsG q.ds (rounds (parO (P5J.At.X Zp) (2 * g + 1) a ((H2K5.k5Before? Zp ("A" ++ toString g)).getD []))) := by
    rw [← er']
    exact List.Forall₂.imp (fun _ _ h' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.2.2, h'.2.2.2.1⟩) hm.rounds
  have ht : (P5J.At.told cF)[14 * (2 * g + 1) + 4]? = some [] := by
    show (cF.blocksInOrder.map fun b => b.oracles.flatMap id)[14 * (2 * g + 1) + 4]? = some []
    rw [List.getElem?_map, hfl]
    show some (E.oracles.flatMap id) = some []
    rw [List.flatMap_id, ho]
  have hbk : blocksOk cF.blocksInOrder = true := by
    have h0 := atRow_blocks h.toAtMg
    rwa [blocksOk_held] at h0
  have hbase : q.base = (oraclesOf (cF.blocksInOrder.take (14 * (2 * g + 1) + 4))).length := by
    rw [seated_base hm hbk, Nat.zero_add]
  exact ⟨blk, E, a, x₁, xd, hP, h4, ea, hx, hxd, Pn, hat, hok, hG, hm.back, he, hds, hSe, hb, k5Book_full _ _ hg ht, hbase⟩

end

end H2K5.Door

#print axioms H2K5.Door.k5_piece_all
