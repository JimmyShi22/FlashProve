-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/PieceAtRow.lean: THE FIELD "piece" OF WHAT IS LEFT IN FRONT OF THE SMALLNESS TEST's
LAW AT THE CLOSED CONSTANT (`K8LeftT`, Johnson/P1K8R/TightAt.lean), AT THE PIECE THAT STANDS AT THE
DRAW's NUMBER IN THE SEATED ROW `h.toAtMg.row L`: FROM THE HEAD `P5J.AtMgA` AND THE THREE FLAT
LISTS' HEADS. A joining of several other files' theorems.
  `k8_kind_full`: a closed fact: at each l ≤ 24 the sub-protocol number 4 (at the output head's
    link: 5) in front of the batching is of the kind K8.
  `draw_at_flat`: in scope, at an opening's letters: number `ixOf l` of the first chain's flat list
    is a sub-protocol with the draw's one round, at the numbers `ProofFile.k8ParW Z Bs.G₀ Xl l`: by
    `IM.k8_alone`, `IM.alone_rounds`, `IM.hear_at_flat` and `IM.flatIx_scope`.
  `k08_piece_at_row`: **the field, to the letter, at the row's own piece**: by
    `k08_piece_at_maker` (Johnson/Desc/First/K8/PieceEq.lean) at the seated term, at the depth
    `frS.P.T.a` and at the rests at the cap.
Limits. At `OnBytes.secondHashFunction` alone. A member of the head `AtMgA` is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/). The other premises here follow from the head; no
file joins them to a member. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.K8.PieceEq
import Johnson.P5J.RowsAtMg
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.IMR.K8Seat
import Johnson.IMR.FlatScope
import Johnson.IMR.RootsWhole
import Johnson.IMR.LinkSeat
import Johnson.P1K8R.Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain Link FileDescription KindName Claim Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open VerifiableInference.Desc.First.K8 (round rdt k08_piece_at_maker)
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

theorem k8_kind_full : ∀ l, l ≤ 24 →
    (kindsBeforeBatching (IM.subAt l) (l == 0))[if l = 24 then 5 else 4]? = some KindName.K8 := by decide

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Number `ixOf l` of the flat list has the draw's one round. -/
theorem draw_at_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l ≤ 24) :
    ∃ b Xl, c.blocksInOrder[ixOf l]? = some b ∧ Bs.G₀.built[l]? = some Xl ∧
      b.rounds = [round (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar] := by
  obtain ⟨Lk, b, Xl, e1, e2, e3, -, hla⟩ := IM.k8_alone O l (IM.subAt l)
    (IM.subs_scope hS hR O l (Nat.lt_succ_of_le hl)) (if l = 24 then 5 else 4) (k8_kind_full l hl)
    (by split <;> decide)
  refine ⟨b, Xl, ?_, e3, (IM.alone_rounds hla).trans rfl⟩
  have h := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O hl] at h
  have e : ixOf l = 14 * l + (if l = 24 then 5 else 4) + 2 := by
    unfold ixOf
    split
    · subst_vars
      rfl
    · rfl
  rw [e]
  exact h

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD "piece", TO THE LETTER, AT THE ROW's OWN PIECE.** -/
theorem k08_piece_at_row (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : OnBytes.Model.Stages.LinkH} (e3 : G.built[l]? = some Xl)
    {q : Piece (Run.ckP .two)
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁)
      (F0T OnBytes.secondHashFunction Zp Np cF).Cl (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)}
    (hq : (h.toAtMg.row L)[ixOf l]? = some q) :
    ∀ B' : Block S Claim,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
          Piece (Run.ckP .two)
            (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) S Claim
            (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)) =
        ⟨below B', q.base, [rdt (ProofFile.k8ParW Zp G Xl l).toPar], [], fun _ _ w => w,
          Iop.Err.cap 128 (uLT (Run.ckP .two) [rdt (ProofFile.k8ParW Zp G Xl l).toPar])⟩ := by
  obtain ⟨Bs, bs, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨b, Xl', hk, e3', hr⟩ := draw_at_flat h.scope h.reads O hl
  obtain rfl : Xl' = Xl := Option.some.inj (e3'.symm.trans e3)
  have hD : (F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth h.scope h.laid]
    exact h.laid.data
  have hs : (F0T OnBytes.secondHashFunction Zp Np cF).sealLast = true := by
    have hp := h.laid.planOk
    unfold FileDescription.planOk at hp
    rw [Bool.and_eq_true] at hp
    exact hp.2
  have hlen : cF.blocksInOrder.length = 358 := Meaning.Carry.flat_len h.scope h.reads O
  have hk1 : ixOf l + 1 < (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length := by
    show ixOf l + 1 < cF.blocksInOrder.length
    rw [hlen]
    unfold ixOf
    split <;> omega
  obtain ⟨q', hq', -, H⟩ := k08_piece_at_maker (C := Run.ckP .two)
    (W := Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT) (F0T OnBytes.secondHashFunction Zp Np cF) "proof file"
    (D.at frS.P.T.a) hD hs L.c₁ L.k₁ L.c₂ L.k₂ L.c₃ L.k₃ q₁ q₂ q₃ (restCap L.e₁) (restCap L.e₂)
    (restCap L.e₃) L.dW L.wEnd (atCap_restCap L.e₁) (ixOf l) b hk hk1 _ hr
  obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
  exact H

end

end P1K8T

#print axioms P1K8T.k8_kind_full
#print axioms P1K8T.draw_at_flat
#print axioms P1K8T.k08_piece_at_row
