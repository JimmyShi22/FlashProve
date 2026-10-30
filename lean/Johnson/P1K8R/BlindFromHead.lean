-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BlindFromHead.lean: THE FIELD "blind" OF `K8LeftT` (Johnson/P1K8R/TightAt.lean), TO
THE LETTER, AT THE SEATED ROW's OWN PIECE, AT EACH OF THE 25 LINKS, FROM THE HEAD `P5J.AtMgA` AND
THE THREE FLAT LISTS' HEADS ALONE: NO TEST IS LEFT. A joining of several other files' theorems.
  `treesTold_flat`: the trees that the first k sub-protocols tell, counted in two ways (`treesTold`,
    Johnson/Desc/First/BookFit.lean; `treesInFront`, FenceAtBase.lean, below), are as many.
  `k8Fence_at_head`: **the test `k8FenceB` (LeftTests.lean) accepts under the head**, at every l
    with `ixOf l` at most the number of places: by `P5J.AtMg.fence` (Johnson/P5T/FenceAtMg.lean:
    the table's test fenceFit accepts at the constant's numbers, from the head alone),
    `fenceFit_withTold` (Johnson/Desc/First/FenceFitTold.lean: what its yes says),
    `numbers_atAll` (Johnson/P1L20R/FramePaidAll.lean: the constant's numbers are filled off what
    the sub-protocols tell) and `treesInFront_cut` (Johnson/Top/H0/MergeLaw/FenceAtBase.lean).
  `blind_from_head`: **the field "blind"**: by `blind_of_test` (BlindOfTest.lean).
Limits. A member of the head `AtMgA` is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). `P5J.AtMg.fence` stands over the verifier's list of entry tests as this library
has it alone (its own Limits). At `OnBytes.secondHashFunction` alone. Nothing on soundness or on hiding.

-/
import Johnson.P1K8R.BlindOfTest
import Johnson.P5T.FenceAtMg
import Johnson.P1L20R.FramePaidAll
import Johnson.P1L20R.FrameSits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf sampledIn openSets start treesTold
  fenceFit_withTold)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.MergeLaw (lowAtB treesInFront treesInFront_cut toldTrees)
open VerifiableInference.PlanWritten (cutOf)
open ProofFile (Cl)
open P5J (AtMgA Free F0T mgAtAll)

/-- Two counts of the trees that the first k sub-protocols tell. -/
theorem treesTold_flat {T C : Type} (bs : List (Block T C)) (k : ℕ) :
    treesTold (bs.map fun b => b.oracles.flatten) k = treesInFront (cutOf bs) k := by
  rw [treesInFront_cut]
  unfold treesTold toldTrees
  rw [← List.map_take, List.map_map]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  exact List.length_flatten

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The fence's test accepts under the head.** -/
theorem k8Fence_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l ≤ 24) :
    k8FenceB (P5J.At.N Zp cF) (cutOf cF.blocksInOrder) l = true := by
  have hf : VerifiableInference.Desc.First.fenceFit (P5J.At.N Zp cF) linksFull
      (flatPlacesOf linksFull true) = true := h.toAtMg.fence
  have eN : P5J.At.N Zp cF = (P1L20.n0All Zp cF).withTold (flatPlacesOf linksFull true)
      (cF.blocksInOrder.map fun b => b.oracles.flatten) := P1L20.numbers_atAll h
  rw [eN] at hf ⊢
  have H := (fenceFit_withTold _ linksFull (flatPlacesOf linksFull true) _
    P1L20.places_nodup_full).1 hf (ixOf l) (by
      rw [P1L20.places_length_full]
      unfold ixOf
      split <;> omega)
  unfold k8FenceB lowAtB openAtDraw
  refine List.all_eq_true.2 fun y hy => decide_eq_true ?_
  rw [← treesTold_flat]
  exact H y hy

/-- **THE FIELD "blind", TO THE LETTER, FROM THE HEAD ALONE.** -/
theorem blind_from_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) {l : ℕ} (hl : l ≤ 24)
    {q : Piece (Run.ckP .two)
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁)
      (F0T OnBytes.secondHashFunction Zp Np cF).Cl (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)}
    (hq : (h.toAtMg.row L)[ixOf l]? = some q) :
    DrawBlind (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true) (drawAt l)
      q.base (oSAt (P5J.At.N Zp cF) (h.𝔇.Rd l) (4 + oOf l) l) :=
  blind_of_test h L q₁ q₂ q₃ hl (k8Fence_at_head h hl) hq

end

end P1K8T

#print axioms P1K8T.treesTold_flat
#print axioms P1K8T.k8Fence_at_head
#print axioms P1K8T.blind_from_head
