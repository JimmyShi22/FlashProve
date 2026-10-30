-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Law/KindPaysAtTerm.lean: the kind K13 (the members' batching) pays for
its one side at the maker's return at the online filling of E2E/TheHonestProver.lean, the return from
which that file makes its family of online provers. No definition; one local notation for K13's lot.

  `k13_online_halves`       K13's lot as the online filling holds it lays one side: K13's, at the
                            return's types, by name
  `k13_pair_mem`, `k13_lot_mem`   K13's pair is among the thirteen, and its lot in the base filling
  `kindPays_k13_at_term`    **under the library's head, wherever the maker returns A: every side of
                            kind K13 in A's first chain pays**: one call of
                            `kindPays_online_of_base_lot`
  `k13_member_at_head`      under the head number 355 of the first chain stands at the kind's place
  `k13_find_at_term`        a search of A's first chain at that place finds K13's side
  `k13_sender_at_term`      so that the payment is not met for want of sides: a member stands there,
                            and what is found first there is K13's side by name
  `kindPays_k13_at_return`  the first theorem, at the description that the maker returned
  `kindPays_k13_at_family`  the same at the description that the online provers stand over
  `kindPays_k13_shared`, `kindPays_k13_second`   K13 pays at the other two chains: it has no side there
  `k13_pays_where_files_pass`   payment and sender without the head: at every return of the maker,
                            where the public files pass the library's two tests

What this is. One kind's share of the field `pays₁` of `ReadyDebts` (Honest/Law/ReadyOfSides.lean),
which `ready_of_sides` joins into a return of `ready`: `chainSteps` returns at the member at K13's
side, at every view and every run's coins.

What this is not. It is not acceptance: nothing here says that a part plays, that a round is reached,
or that the verifier's block accepts what K13 sends. It says nothing of the other kinds. It is not the
return of `ready`, whose other debts lie elsewhere.

Why the lot lays a side at all. `k13Lot` lays one half at every public part and ground: no test stands
in front of it, and its place does not read the pile. Two things follow, which are limits and not
comfort. The pile's filler `K13.pileAnyK3` is read only when the side's moves run, and nothing here
looks at what it yields: its silent cases and its placeholders (Honest/K13/PileOfAnySize.lean) are not
touched by a statement that stops at `chainSteps`. The side stands at the kind's place whether or not
the filler yields rows.

The premises. h: the library's head, at the public files Z. hA: the maker returns A. The last theorem
asks no head: scope and hl are tests on the public files.

Limits.
  * Until `MakerReturns` (E2E/TheHonestProver.lean) is shown at this file's maker, hA is a premise, and
    these statements may hold of nothing.
  * That any public files pass the two tests is evaluated, not proved: no theorem here or beneath
    gives such files.
  * The full size and the format's second hash function alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.Law.SidePaysK13
import Johnson.Desc.ProofFile.Honest.K13.FromThreadAt
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnlineForms
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.LPFPol.LiveAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First (blockPlaces)
open VerifiableInference.Desc.K13 (whereOf)
open P5J (AtMgA TS)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open ProofFile.Honest.Term (OnlineReturn onlineMaker matrixInput tableCoins onlineBase onlinePairs onlineLot
  kindPays_online_of_base_lot online_desc_at_head)

/-- K13's lot of the thirteen, at the values that the filling of E2E/TheHonestProver.lean gives. -/
local notation "k13BaseLot" => lotK13 matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- **What that lot lays, as the online filling holds it: one side, K13's, at the return's types.** -/
theorem k13_online_halves (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    (onlineLot files k13BaseLot).halves Zq G =
      [proverSideOfClaimCombination (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles files).EncodingRandomness) (Xi := ProofFile.Inst) (Tr := Cells) (X := Unit)
        (matrixInput.weights Zq) (pileAnyK3 Zq G) (whereOf Zq)] :=
  congrArg (fun g => [g])
    (k13Half_thru (Tr := Cells) (X := Unit) id (tableCoins files) (matrixInput.weights Zq)
      (pileAnyK3 Zq G) (whereOf Zq)).symm

/-- K13's pair is among the thirteen. -/
theorem k13_pair_mem : (k13BaseLot, KindName.K13) ∈ onlinePairs :=
  List.mem_append_left _ (by simp [widerPairs])

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The kind K13 pays at the maker's return**: under the library's head, wherever the maker returns
A, every side of kind K13 in A's first chain pays. It is not acceptance. Conditional: h; hA. -/
theorem kindPays_k13_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first KindName.K13 := by
  obtain ⟨e1, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  refine kindPays_online_of_base_lot hA (L := k13BaseLot) (fun q hq => ?_) (onlyK13 _ _ _ _)
  obtain rfl : q = proverSideOfClaimCombination (matrixInput.weights A.Z) (pileAnyK3 A.Z A.G) (whereOf A.Z) :=
    List.mem_singleton.1 hq
  rw [eZ]
  exact sidePays_k13 h hA _ _

/-- **Under the head number 355 of the first chain stands at the kind's place.** Conditional: h. -/
theorem k13_member_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∃ blk, cF.blocksInOrder[355]? = some blk ∧ blk.place = ⟨1, none, 3, .K13⟩ := by
  have e355 : (blockPlaces cF.blocksInOrder)[355]? = some ⟨1, none, 3, .K13⟩ := by
    rw [P5J.At.places_paid h.scope h.reads h.laid]
    exact m3_place
  unfold blockPlaces at e355
  rw [List.getElem?_map] at e355
  obtain ⟨blk, h355, hbp⟩ := Option.map_eq_some_iff.1 e355
  exact ⟨blk, h355, hbp⟩

/-- K13's lot lies in the base filling. -/
theorem k13_lot_mem : k13BaseLot ∈ onlineBase.lots := by
  rw [fillPairs_lots]
  exact List.mem_map.2 ⟨_, k13_pair_mem, rfl⟩

/-- **What a search of A's first chain finds at the kind's place: K13's side.** Conditional: h; hA. -/
theorem k13_find_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    A.H.first.find? (fun q => q.place == (⟨1, none, 3, .K13⟩ : Place)) =
      some (proverSideOfClaimCombination (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Xi := ProofFile.Inst) (Tr := Cells) (X := Unit)
        (matrixInput.weights Zp) (pileAnyK3 Zp A.G) (whereOf Zp)) := by
  obtain ⟨e1, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  rw [← eZ]
  refine atPure_first_find_kind hA (L := onlineLot Z k13BaseLot)
    (List.mem_map_of_mem k13_lot_mem) (fun M hM => ?_) ?_
  · obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hM
    rcases lot_alone _ _ _ _ (onlyK13 _ _ _ _) A.Z A.G N hN with rfl | hk
    · exact Or.inr rfl
    · refine Or.inl fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hk y hy
  · rw [k13_online_halves]
    exact List.find?_cons_of_pos (beq_self_eq_true (⟨1, none, 3, .K13⟩ : Place))

/-- **K13's sender stands**: a member of the description's list stands at the kind's place, and a
search at that place in A's first chain finds K13's side by name. So the theorem on payment is not met
for want of sides. Conditional: h; hA. -/
theorem k13_sender_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    (∃ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, b.place = ⟨1, none, 3, .K13⟩) ∧
      A.H.first.find? (fun q => q.place == (⟨1, none, 3, .K13⟩ : Place)) =
        some (proverSideOfClaimCombination (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Xi := ProofFile.Inst) (Tr := Cells) (X := Unit)
          (matrixInput.weights Zp) (pileAnyK3 Zp A.G) (whereOf Zp)) := by
  obtain ⟨blk, h355, hbp⟩ := k13_member_at_head h
  exact ⟨⟨blk, List.mem_of_getElem? h355, hbp⟩, k13_find_at_term h hA⟩

/-- **The same at the description that the maker returned.** Conditional: h; hA. -/
theorem kindPays_k13_at_return (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K13 := by
  obtain ⟨-, -, e3, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  rw [eF]
  exact kindPays_k13_at_term h hA

/-- **At the description that the online provers stand over**: at the places and the first chain that
`onlineProver` reads off the maker's public part. Conditional: h; hA. -/
theorem kindPays_k13_at_family (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) {places : H2U.Places4} {firstChain : Chain TS ProofFile.Cl}
    (hPlaces : H2U.placesOfMade A.Z.made = .ok places)
    (hChain : ProofFile.onlineFirstChainAt A.Z = .ok firstChain) :
    KindPays A.B 0 (descZ A.Z places firstChain).first.blocksInOrder A.H.first KindName.K13 := by
  rw [(online_desc_at_head h hA hPlaces hChain).1]
  exact kindPays_k13_at_term h hA

/-- **K13 pays at the shared chain, for want of sides.** Conditional: h; hA. -/
theorem kindPays_k13_shared (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared KindName.K13 :=
  ProofFile.Honest.Term.kindPays_online_shared_none h hA (by decide)

/-- **K13 pays at the second chain, for want of sides.** Conditional: hA. -/
theorem kindPays_k13_second {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    KindPays A.B 2 A.F.second.blocksInOrder A.H.second KindName.K13 :=
  ProofFile.Honest.Term.kindPays_online_second_none hA (by decide)

/-- **Without the head, at every return of the maker**: where the public files are in scope and pass
the library's test, K13 pays at the return, and its sender stands at the kind's place. It is not
acceptance. Conditional: the two tests; hA. That the maker returns is not shown here. -/
theorem k13_pays_where_files_pass (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K13 ∧
      (∃ b ∈ A.F.first.blocksInOrder, b.place = ⟨1, none, 3, .K13⟩) ∧
      A.H.first.find? (fun q => q.place == (⟨1, none, 3, .K13⟩ : Place)) =
        some (proverSideOfClaimCombination (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Xi := ProofFile.Inst) (Tr := Cells) (X := Unit)
          (matrixInput.weights A.Z) (pileAnyK3 A.Z A.G) (whereOf A.Z)) := by
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z scope read hl (P5J.owed_of_live hl)
  obtain ⟨e1, -, e3, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  obtain ⟨hb, hf⟩ := k13_sender_at_term h hA
  refine ⟨kindPays_k13_at_return h hA, ?_, ?_⟩
  · rw [eF]
    exact hb
  · rw [eZ]
    exact hf

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_online_halves
#print axioms ProofFile.Honest.K13.k13_pair_mem
#print axioms ProofFile.Honest.K13.kindPays_k13_at_term
#print axioms ProofFile.Honest.K13.k13_member_at_head
#print axioms ProofFile.Honest.K13.k13_lot_mem
#print axioms ProofFile.Honest.K13.k13_find_at_term
#print axioms ProofFile.Honest.K13.k13_sender_at_term
#print axioms ProofFile.Honest.K13.kindPays_k13_at_return
#print axioms ProofFile.Honest.K13.kindPays_k13_at_family
#print axioms ProofFile.Honest.K13.kindPays_k13_shared
#print axioms ProofFile.Honest.K13.kindPays_k13_second
#print axioms ProofFile.Honest.K13.k13_pays_where_files_pass
