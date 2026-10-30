-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/Law/KindPaysAtTerm.lean: the kind K7 (the next token) pays for its
one side at the maker's return at the online filling of E2E/TheHonestProver.lean, the return from which
that file makes its family of online provers. No definition; one local notation for K7's lot.

  `k7_online_halves`        K7's lot as the online filling holds it lays one side: K7's, by name
  `k7_pair_mem`, `k7_lot_mem`   K7's pair is among the thirteen, and its lot in the base filling
  `k7_link_at_term`         the last built segment of the return's ground is number 24
  `kindPays_k7_at_term`     **under the library's head, wherever the maker returns A: every side of
                            kind K7 in A's first chain pays**: one call of
                            `kindPays_online_of_base_lot`
  `k7_find_at_term`         a search of A's first chain at the kind's place finds K7's side
  `k7_sender_at_term`       so that the payment is not met for want of sides: a member stands there,
                            and what is found first there is K7's side by name
  `kindPays_k7_at_return`   the first theorem, at the description that the maker returned
  `kindPays_k7_at_family`   the same at the description that the online provers stand over
  `kindPays_k7_shared`, `kindPays_k7_second`   K7 pays at the other two chains: it has no side there
  `k7_pays_where_files_pass`   payment and sender without the head: at every return of the maker,
                            where the public files pass the library's two tests

What this is. One kind's share of the field `pays₁` of `ReadyDebts` (Honest/Law/ReadyOfSides.lean): 
`chainSteps` returns at the member at K7's side, at every view and every run's coins.

What this is not. It is not acceptance: nothing here says that a part plays, that a round is reached,
or that the verifier's block accepts what K7 sends. It says nothing of the other kinds. It is not the
return of `ready`, whose other debts lie elsewhere.

The premises. h: the library's head, at the public files Z. hA: the maker returns A. The last theorem
asks no head: scope and hl are tests on the public files.

Limits.
  * hA is a premise here. Honest/Law/KindPaysAtFiles.lean discharges it by `maker_returns`
    (AtFullSide/K12/MakerReturnsAtLive.lean).
  * That any public files pass the two tests is evaluated, not proved: no theorem here or beneath
    gives such files.
  * The full size and the format's second hash function alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.Law.SidePaysK7
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnlineForms
import Johnson.Desc.ProofFile.Honest.Thread.HeadFacts
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.LPFPol.LiveAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K7
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open P5J (AtMgA TS)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open ProofFile.Honest.Term (OnlineReturn onlineMaker matrixInput tableCoins onlineBase onlinePairs onlineLot
  kindPays_online_of_base_lot online_desc_at_head)

/-- K7's lot of the thirteen. -/
local notation "k7BaseLot" =>
  (lotK7 : HLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit)

/-- **What that lot lays, as the online filling holds it: one side, K7's, at the return's types**: the
part reads of its input the public instance alone, so reading it through changes nothing. -/
theorem k7_online_halves (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    (onlineLot files k7BaseLot).halves Zq G =
      [replyHalf (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles files).EncodingRandomness) (Tr := Cells) (X := Unit) (G.built.size - 1) 1
        G.W.hS.V] :=
  rfl

/-- K7's pair is among the thirteen. -/
theorem k7_pair_mem : (k7BaseLot, KindName.K7) ∈ onlinePairs :=
  List.mem_append_left _ (by simp [widerPairs])

/-- K7's lot lies in the base filling. -/
theorem k7_lot_mem : k7BaseLot ∈ onlineBase.lots := by
  rw [fillPairs_lots]
  exact List.mem_map.2 ⟨_, k7_pair_mem, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The last built segment of the return's ground is number 24. Conditional: h; hA. -/
theorem k7_link_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : A.G.built.size - 1 = 24 := by
  obtain ⟨e1, eG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  rw [ProofFile.Honest.FirstFill.built_25 h hG]

/-- **The kind K7 pays at the maker's return**: under the library's head, wherever the maker returns
A, every side of kind K7 in A's first chain pays. It is not acceptance. Conditional: h; hA. -/
theorem kindPays_k7_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first KindName.K7 := by
  refine kindPays_online_of_base_lot hA (L := k7BaseLot) (fun q hq => ?_) (onlyK7 _ _ _ _)
  obtain rfl : q = replyHalf (A.G.built.size - 1) 1 A.G.W.hS.V := List.mem_singleton.1 hq
  rw [k7_link_at_term h hA]
  exact sidePays_k7 h hA _

/-- **What a search of A's first chain finds at the kind's place: K7's side.** Conditional: h; hA. -/
theorem k7_find_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    A.H.first.find? (fun q => q.place == IM.k7Place) =
      some (replyHalf (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Tr := Cells) (X := Unit) 24 1 A.G.W.hS.V) := by
  refine atPure_first_find_kind hA (L := onlineLot Z k7BaseLot)
    (List.mem_map_of_mem k7_lot_mem) (fun M hM => ?_) ?_
  · obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hM
    rcases lot_alone _ _ _ _ (onlyK7 _ _ _ _) A.Z A.G N hN with rfl | hk
    · exact Or.inr rfl
    · refine Or.inl fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hk y hy
  · rw [k7_online_halves, k7_link_at_term h hA]
    exact List.find?_cons_of_pos (beq_self_eq_true IM.k7Place)

/-- **K7's sender stands**: a member of the description's list stands at the kind's place, and a
search at that place in A's first chain finds K7's side by name. So the theorem on payment is not met
for want of sides. Conditional: h; hA. -/
theorem k7_sender_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    (∃ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, b.place = IM.k7Place) ∧
      A.H.first.find? (fun q => q.place == IM.k7Place) =
        some (replyHalf (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Tr := Cells) (X := Unit) 24 1 A.G.W.hS.V) := by
  obtain ⟨blk, h338, hbp⟩ := k7_member_at_head h
  exact ⟨⟨blk, List.mem_of_getElem? h338, hbp⟩, k7_find_at_term h hA⟩

/-- **The same at the description that the maker returned.** Conditional: h; hA. -/
theorem kindPays_k7_at_return (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K7 := by
  obtain ⟨-, -, e3, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  rw [eF]
  exact kindPays_k7_at_term h hA

/-- **At the description that the online provers stand over**: at the places and the first chain that
`onlineProver` reads off the maker's public part. Conditional: h; hA. -/
theorem kindPays_k7_at_family (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) {places : H2U.Places4} {firstChain : Chain TS ProofFile.Cl}
    (hPlaces : H2U.placesOfMade A.Z.made = .ok places)
    (hChain : ProofFile.onlineFirstChainAt A.Z = .ok firstChain) :
    KindPays A.B 0 (descZ A.Z places firstChain).first.blocksInOrder A.H.first KindName.K7 := by
  rw [(online_desc_at_head h hA hPlaces hChain).1]
  exact kindPays_k7_at_term h hA

/-- **K7 pays at the shared chain, for want of sides.** Conditional: h; hA. -/
theorem kindPays_k7_shared (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared KindName.K7 :=
  ProofFile.Honest.Term.kindPays_online_shared_none h hA (by decide)

/-- **K7 pays at the second chain, for want of sides.** Conditional: hA. -/
theorem kindPays_k7_second {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    KindPays A.B 2 A.F.second.blocksInOrder A.H.second KindName.K7 :=
  ProofFile.Honest.Term.kindPays_online_second_none hA (by decide)

/-- **Without the head, at every return of the maker**: where the public files are in scope and pass
the library's test, K7 pays at the return, and its sender stands at the kind's place. It is not
acceptance. Conditional: the two tests; hA. That the maker returns is not shown here. -/
theorem k7_pays_where_files_pass (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K7 ∧
      (∃ b ∈ A.F.first.blocksInOrder, b.place = IM.k7Place) ∧
      A.H.first.find? (fun q => q.place == IM.k7Place) =
        some (replyHalf (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (Tr := Cells) (X := Unit) 24 1 A.G.W.hS.V) := by
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z scope read hl (P5J.owed_of_live hl)
  obtain ⟨-, -, e3, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  obtain ⟨hb, hf⟩ := k7_sender_at_term h hA
  refine ⟨kindPays_k7_at_return h hA, ?_, hf⟩
  rw [eF]
  exact hb

end ProofFile.Honest.K7

#print axioms ProofFile.Honest.K7.k7_online_halves
#print axioms ProofFile.Honest.K7.k7_pair_mem
#print axioms ProofFile.Honest.K7.k7_lot_mem
#print axioms ProofFile.Honest.K7.k7_link_at_term
#print axioms ProofFile.Honest.K7.kindPays_k7_at_term
#print axioms ProofFile.Honest.K7.k7_find_at_term
#print axioms ProofFile.Honest.K7.k7_sender_at_term
#print axioms ProofFile.Honest.K7.kindPays_k7_at_return
#print axioms ProofFile.Honest.K7.kindPays_k7_at_family
#print axioms ProofFile.Honest.K7.kindPays_k7_shared
#print axioms ProofFile.Honest.K7.kindPays_k7_second
#print axioms ProofFile.Honest.K7.k7_pays_where_files_pass
