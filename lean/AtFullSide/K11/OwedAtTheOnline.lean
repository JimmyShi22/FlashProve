-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/OwedAtTheOnline.lean: the two statements of AtFullSide/K11/LendsAtTheTerm.lean at the
online prover's filling, which is the base filling read through the table's randomness.

  k11SimulatorOwedOnline    the simulator's statement at the online maker's return
  k11_pays_online            the kind pays at that return
  kindPays_k11_at_return     the same at the return's own first chain
  k11_sender_at_return       a member stands at the kind's place, and the search finds the side
  k11_filter_online          the sides of the kind at that return, as a list, are the kind's side

Limits. Those of the two statements. The library's head and the maker's return are premises.
-/
import AtFullSide.K11.Crossing
import AtFullSide.K11.LendsAtTheTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.Desc (Chain KindName)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS)
open ProofFile.Honest
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling matrixInput tableCoins)
open AtPublicFiles.AtFiles.HonestTerm.K11Term

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {A : OnlineReturn Z}
  {Bs : ProofFile.PureBase}

/-- **The simulator at the online prover.** -/
theorem k11SimulatorOwedOnline : K11SimulatorOwedOnline := by
  intro Z D r Zp Np cF x A Bs hM h hB
  obtain ⟨e1, -⟩ := atPure_ok hM
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  exact k11SimulatorOwed _ _ _ _ _ _ (matrixInput.weights A.Z) Z D r A.Z Np cF x A Bs hM h hB
    (k11_hex_through matrixInput OnBytes.secondHashFunction Sz.ref openHonest (tableCoins Z) matrixInput.dummy
      A.Z A.G)
    (k11_ho_through matrixInput OnBytes.secondHashFunction Sz.ref openHonest (tableCoins Z) matrixInput.dummy
      A.Z A.G)

/-- **The kind pays at the online prover.** -/
theorem k11_pays_online (hM : onlineMaker Z = .ok A) (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    KindPays A.B 0 cF.blocksInOrder A.H.first KindName.K11 := by
  obtain ⟨e1, -⟩ := atPure_ok hM
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  exact k11_pays (weights := matrixInput.weights A.Z) h hM
    (k11_ho_through matrixInput OnBytes.secondHashFunction Sz.ref openHonest (tableCoins Z) matrixInput.dummy
      A.Z A.G)

/-- **The kind pays at a return of the online maker, at the return's own first chain.** -/
theorem kindPays_k11_at_return (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineMaker Z = .ok A) : KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K11 := by
  have eF := (AtFullSide.K14.makers_ahead_at_atPure h hA).2
  rw [eF]
  exact k11_pays_online hA h

/-- **A member of the return's first chain stands at the kind's place, and the search there finds
the kind's side by name**: so the payment does not hold for want of a side. -/
theorem k11_sender_at_return (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineMaker Z = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (∃ b ∈ A.F.first.blocksInOrder, b.place = IM.k11Place) ∧
      (A.H.first.find? fun q => q.place == IM.k11Place) =
        some (k11Side (matrixInput.weights Zp) Zp Bs.G₀) := by
  have eF := (AtFullSide.K14.makers_ahead_at_atPure h hA).2
  obtain ⟨e1, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  obtain ⟨Bs', name, hB', hm⟩ := ProofFile.Honest.K11.headMergeMemberAtFull Z D r A.Z Np cF x h
    (places_nodup h)
  have hfind := (ProofFile.Honest.K11.halfAtAnyFillHead Z D r A.Z Np cF x h _ _ _ _ _ (onlineFilling Z) A
    Bs ProofFile.Honest.K11.headClaimsByPlace (matrixInput.weights A.Z) hB hA
    (k11_hex_through matrixInput OnBytes.secondHashFunction Sz.ref openHonest (tableCoins Z) matrixInput.dummy
      A.Z A.G)
    (k11_ho_through matrixInput OnBytes.secondHashFunction Sz.ref openHonest (tableCoins Z) matrixInput.dummy
      A.Z A.G)).2.2
  refine ⟨?_, hfind⟩
  rw [eF]
  exact ⟨_, List.mem_of_find?_eq_some hm, k11_place_is h hB'⟩

/-- **The sides of the kind at the online prover, as a list: the kind's side, once.** -/
theorem k11_filter_online (hM : onlineMaker Z = .ok A) (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (A.H.first.filter fun g => g.place.kind == KindName.K11) =
      [k11Side (matrixInput.weights Zp) Zp Bs.G₀] := by
  obtain ⟨e1, -⟩ := atPure_ok hM
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  obtain ⟨pre, post, hl, hp, hq⟩ :=
    k11_split matrixInput OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G
  have away : ∀ (l : List (HLot (Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
        (Local AtPublicFiles.AtFiles.FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit)),
      (∀ M ∈ l, ∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11) →
      ∀ M ∈ l.map (HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))),
        ∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11 := by
    intro l hn M hM y hy e
    obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
    obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.1 hy
    exact hn M₀ hM₀ y₀ hy₀ e
  have hl' : (onlineFilling Z).lots =
      pre.map (HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))) ++
        (HLot.byPub matrixInput.weights (LongLots.plain OnBytes.secondHashFunction Sz.ref openHonest).k11).thru
          (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z)) ::
        post.map (HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))) := by
    show (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest).lots.map _ = _
    rw [hl, List.map_append, List.map_cons]
  exact k11_filter_at h hM hB hl'
    (k11_byPub_through matrixInput OnBytes.secondHashFunction Sz.ref openHonest (tableCoins Z) A.Z A.G)
    (away pre hp) (away post hq)

end AtFullSide.K11

#print axioms AtFullSide.K11.kindPays_k11_at_return
#print axioms AtFullSide.K11.k11_sender_at_return
#print axioms AtFullSide.K11.k11_filter_online
#print axioms AtFullSide.K11.k11SimulatorOwedOnline
#print axioms AtFullSide.K11.k11_pays_online
