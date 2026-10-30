-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BlindOfTest.lean: THE FIELD "blind" OF `K8LeftT` (Johnson/P1K8R/TightAt.lean), TO THE
LETTER, AT THE SEATED ROW's OWN PIECE, AT EACH OF THE 25 LINKS, FROM THE HEAD `P5J.AtMgA`, THE THREE
FLAT LISTS' HEADS AND ONE TEST WITH CODE ON PUBLIC DATA: `k8FenceB`. A joining of our own theorems.
  `blindOwes_of_test`: `BlindOwes h l q.base`: by `blindOwes_of_fence` (WtBack.lean) and
    `k8Fence_tie` (LeftTests.lean); that `ixOf l` is a number of the flat list: in scope the list
    has 358 entries (`Meaning.Carry.flat_len`).
  `blind_of_test`: **the field "blind"**: by `blind_at_const` (BlindJoin.lean).
Limits. That the test accepts is shown nowhere here (it has been evaluated at the stored full-size
public files: true at all 25 links: a run, no proof). A member of the head `AtMgA` is proved at
`storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/).
At `OnBytes.secondHashFunction` alone. Nothing on soundness or on hiding.

-/
import Johnson.P1K8R.WtBack
import Johnson.P1K8R.LeftTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.PlanWritten (cutOf)
open ProofFile (Cl)
open P5J (AtMgA Free F0T mgAtAll)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- What is left of "blind", from the fence's test. -/
theorem blindOwes_of_test (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) {l : ℕ} (hl : l ≤ 24)
    (t : k8FenceB (P5J.At.N Zp cF) (cutOf cF.blocksInOrder) l = true)
    {q : Piece (Run.ckP .two)
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁)
      (F0T OnBytes.secondHashFunction Zp Np cF).Cl (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)}
    (hq : (h.toAtMg.row L)[ixOf l]? = some q) : BlindOwes h l q.base := by
  obtain ⟨Bs, bs, O⟩ := h.laid.opened
  have hk : ixOf l < cF.blocksInOrder.length := by
    rw [Meaning.Carry.flat_len h.scope h.reads O]
    unfold ixOf
    split <;> omega
  exact blindOwes_of_fence h hl q.base (k8Fence_tie h L q₁ q₂ q₃ hk t hq)

/-- **THE FIELD "blind", TO THE LETTER, AT THE ROW's OWN PIECE.** -/
theorem blind_of_test (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) {l : ℕ} (hl : l ≤ 24)
    (t : k8FenceB (P5J.At.N Zp cF) (cutOf cF.blocksInOrder) l = true)
    {q : Piece (Run.ckP .two)
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁)
      (F0T OnBytes.secondHashFunction Zp Np cF).Cl (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)}
    (hq : (h.toAtMg.row L)[ixOf l]? = some q) :
    DrawBlind (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true) (drawAt l)
      q.base (oSAt (P5J.At.N Zp cF) (h.𝔇.Rd l) (4 + oOf l) l) :=
  blind_at_const h hl (blindOwes_of_test h L q₁ q₂ q₃ hl t hq)

end

end P1K8T

#print axioms P1K8T.blindOwes_of_test
#print axioms P1K8T.blind_of_test
