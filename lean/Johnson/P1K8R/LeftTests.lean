-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K8R/LeftTests.lean: FOUR CLOSED FACTS INSIDE `K8LeftT` (Johnson/P1K8R/TightAt.lean:
what is left in front of the smallness test's law at the closed constant), EACH AS A TEST WITH CODE
ON PUBLIC DATA, AND FOR EACH TEST THE LEMMA "the test accepts → the field's own sentence". For the
file of evaluations Johnson/L25X/SecK8Left.lean (not in this library), which evaluates them.
  `k8PieceB Zp G fl l`: entry `ixOf l` of the list fl declares just the draw's one round, at the
    numbers `ProofFile.k8ParW Zp G Xl l`, Xl the built link number l; and it is not the list's last.
    `k8Piece_tie`: so the field "piece", to the letter, at the seated row's own piece.
  `k8LinkB Zp l` := `(P5J.At.lk Zp l).isSome`. `k8Link_tie`: the field "link". `k8LinkOfB c l`: the
    same with the value c of `ProofFile.onlineFirstChainAt Zp` handed in; `k8LinkB_eq`: they are one, by rfl.
  `k8FenceB N cut l` := `lowAtB` (Johnson/Top/H0/MergeLaw/FenceAtBase.lean) at the
    items that are open at border `ixOf l` and the number of trees that the rows of cut in front of
    `ixOf l` tell. `k8Fence_tie`: so the fence of the field "blind" (`BlindOwes.fence`,
    Johnson/P1K8R/BlindJoin.lean), AT THE SEATED ROW's OWN PIECE's BASE: by `MergeLaw.base_at`.
  `k8GroupB N l` := `decide (N.groupAt l = l)`. `k8Group_tie`: the field "groupAt".
Limits. The ties stand under the head `P5J.AtMgA`: a member of it is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/). "piece" also
follows from the head alone (Johnson/P1K8R/PieceAtRow.lean). That a test accepts is shown nowhere
here. At `OnBytes.secondHashFunction` alone. Nothing on soundness or on hiding.

-/
import Johnson.P1K8R.PieceAtRow
import Johnson.Top.H0.MergeLaw.FenceAtBase
import Johnson.Goal.Skeleton.TheThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim Wit blocksOk)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Numbers Item flatPlacesOf sampledIn openSets start)
open VerifiableInference.Desc.First.K8 (round rdt k08_piece_at_maker)
open VerifiableInference.Desc.First.MergeLaw (lowAtB low_of_test treesInFront base_at)
open VerifiableInference.PlanWritten (cutOf)
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

/-- The test for "piece". -/
def k8PieceB (Zp : ProofFile.Pub) (G : ProofFile.Ground) (fl : List (Block S Cl)) (l : ℕ) : Bool :=
  match fl[ixOf l]?, G.built[l]? with
  | some b, some Xl =>
    decide (b.rounds = [round (ProofFile.k8ParW Zp G Xl l).toPar]) && decide (ixOf l + 1 < fl.length)
  | _, _ => false

/-- The test for "link". -/
def k8LinkB (Zp : ProofFile.Pub) (l : ℕ) : Bool := (P5J.At.lk Zp l).isSome

/-- The same with the chain's maker's value handed in, so that a run makes that value once. -/
def k8LinkOfB (c : Except String (Chain S Cl)) (l : ℕ) : Bool :=
  (c.toOption.bind fun c => c.links[l]?).isSome

theorem k8LinkB_eq (Zp : ProofFile.Pub) (l : ℕ) : k8LinkB Zp l = k8LinkOfB (ProofFile.onlineFirstChainAt Zp) l := rfl

/-- The items that are open in front of link l's draw. -/
def openAtDraw (l : ℕ) : List Item :=
  (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[ixOf l]?.getD []

/-- The test for the fence of "blind". -/
def k8FenceB (N : Numbers)
    (cut : List (String × Place × ℕ × ℕ × List (ℕ × List VerifiableInference.Desc.Oracle) ×
      List (ℕ × ℕ))) (l : ℕ) : Bool :=
  lowAtB N (openAtDraw l) (treesInFront cut (ixOf l))

/-- The test for "groupAt". -/
def k8GroupB (N : Numbers) (l : ℕ) : Bool := decide (N.groupAt l = l)

theorem k8Group_tie {N : Numbers} {l : ℕ} (t : k8GroupB N l = true) : N.groupAt l = l :=
  of_decide_eq_true t

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **"link", from its test.** -/
theorem k8Link_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ}
    (t : k8LinkB Zp l = true) : ∃ Lk, h.𝔇.lk l = some Lk :=
  Option.isSome_iff_exists.1 t

/-- **"piece", from its test.** -/
theorem k8Piece_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    {G : ProofFile.Ground} {l : ℕ} (t : k8PieceB Zp G cF.blocksInOrder l = true)
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
  unfold k8PieceB at t
  rw [e3] at t
  cases hk : cF.blocksInOrder[ixOf l]? with
  | none =>
    rw [hk] at t
    cases t
  | some b =>
    rw [hk] at t
    have t' : (decide (b.rounds = [round (ProofFile.k8ParW Zp G Xl l).toPar]) &&
      decide (ixOf l + 1 < cF.blocksInOrder.length)) = true := t
    rw [Bool.and_eq_true] at t'
    have hr := of_decide_eq_true t'.1
    have hk1 := of_decide_eq_true t'.2
    have hD : (F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
      rw [P5J.LaidAt.atDepth h.scope h.laid]
      exact h.laid.data
    have hs : (F0T OnBytes.secondHashFunction Zp Np cF).sealLast = true := by
      have hp := h.laid.planOk
      unfold FileDescription.planOk at hp
      rw [Bool.and_eq_true] at hp
      exact hp.2
    obtain ⟨q', hq', -, H⟩ := k08_piece_at_maker (C := Run.ckP .two)
      (W := Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT) (F0T OnBytes.secondHashFunction Zp Np cF) "proof file"
      (D.at frS.P.T.a) hD hs L.c₁ L.k₁ L.c₂ L.k₂ L.c₃ L.k₃ q₁ q₂ q₃ (restCap L.e₁) (restCap L.e₂)
      (restCap L.e₃) L.dW L.wEnd (atCap_restCap L.e₁) (ixOf l) b hk hk1 _ hr
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    exact H

/-- **The fence of "blind", at the row's own piece's base, from its test.** -/
theorem k8Fence_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) {l : ℕ}
    (hk : ixOf l < cF.blocksInOrder.length)
    (t : k8FenceB (P5J.At.N Zp cF) (cutOf cF.blocksInOrder) l = true)
    {q : Piece (Run.ckP .two)
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁)
      (F0T OnBytes.secondHashFunction Zp Np cF).Cl (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)}
    (hq : (h.toAtMg.row L)[ixOf l]? = some q) :
    ∀ y ∈ sampledIn (P5J.At.N Zp cF) ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[ixOf l]?.getD []), y.1 < q.base := by
  have hD : (F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth h.scope h.laid]
    exact h.laid.data
  have Ft := threeCap_fits L.e₁ L.e₂ L.e₃ L.dW L.wEnd hD h.laid.planOk q₁ q₂ q₃
  have hb : blocksOk (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = true := by
    cases hb : blocksOk (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder with
    | true => rfl
    | false =>
      have hp := h.laid.planOk
      simp [FileDescription.planOk, FileDescription.planOkCore, hb] at hp
  have e : q.base = treesInFront (cutOf (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) (ixOf l) :=
    base_at (F0T OnBytes.secondHashFunction Zp Np cF) "proof file" (D.at frS.P.T.a) hD
      (threeCap (F0T OnBytes.secondHashFunction Zp Np cF) (D.at frS.P.T.a) L.c₁ L.k₁ L.c₂ L.k₂ L.c₃ L.k₃ L.e₁
        L.e₂ L.e₃ L.dW L.wEnd)
      (threeCap_ofDesc L.e₁ L.e₂ L.e₃ L.dW L.wEnd hD h.laid.planOk q₁ q₂ q₃)
      Ft.tiled₁ Ft.data₁ Ft.base₁ hb hk hq
  rw [e]
  exact low_of_test t

end

end P1K8T

#print axioms P1K8T.k8Group_tie
#print axioms P1K8T.k8LinkB_eq
#print axioms P1K8T.k8Link_tie
#print axioms P1K8T.k8Piece_tie
#print axioms P1K8T.k8Fence_tie
