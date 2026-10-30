-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/KindPaysOnline.lean: how a kind pays at the maker's return at the
online filling (`onlineMaker`, E2E/TheHonestProver.lean). No statement names a kind's laws, though
such laws lie beneath it (K5/Law/ReturnsOf.lean, and what the imports bring). Three abbreviations, the
rest theorems. The lots and their kinds are stated at the base filling in Honest/Law/FillPairs.lean.

  `kindPays_online`           **the form for one lot**, paid at its sides read through
  `kindPays_online_of_base`   the same, paid by a law at the base filling's return
  `kindPays_online_of_base_lots`   **the form for a list of lots**, paid at the base filling's own
                              sides: no equation; K1 has two lots
  `kindPays_online_of_sides`, `kindPays_online_of_lots`   the same with the payment read through
  `kindPays_proverAt`, `kindPays_proverAt_shared`, `kindPays_proverAt_second`   a payment at the
                              return's prover holds at the prover that `onlineProversOfCommitter` reads
  `kindPays_online_all`       the twelve kinds with lots paid: all sixteen pay
  `online_desc_at_head`       under the library's head, the description that the return holds, the one
                              that the family reads and the head's are one
  `kindPays_online_empty`     K9, K14, K15 and the frame lay no side in the first chain: they pay there
  `online_shared_kinds`, `online_second_kinds`   the kinds of the other two chains' sides
  `kindPays_online_shared_none`, `kindPays_online_second_none`   a kind with no side there pays there

A kind supplies: its lot L; the payment; and that its pair is the only one of its kind, which for one
lot is a small computation on `fillPairs` (Honest/Law/FillPairs.lean).

Limits.
  * What is paid is that `chainSteps` returns at the members. Nothing here says that a part plays, or
    that a verifier accepts.
  * Every form is conditional on a return of the maker (hA). That the maker returns at this filling
    (`MakerReturns`, E2E/TheHonestProver.lean) is not shown here: where it does not, all hold of
    nothing.
  * `online_shared_kinds`, `kindPays_online_shared_none` and `online_desc_at_head` are conditional on
    the library's head: the full size and the format's second hash function alone.
  * The list bs is a letter. At a side whose place is no member's in bs, `SidePays` asks nothing: a
    call at a list other than the description's says nothing of `ready`.
  * "Pays for want of sides" says that the filling lays no side of the kind in that chain. It does
    not say that the description has no sub-protocol of the kind there.
  * A kind with sides in the other two chains calls `kindPays_shared_of_through_sides` or its twin
    (SidePaysThrough.lean).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.SidePaysThrough
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.ToldDescR.PureChainOfOpen
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open VerifiableInference.Desc (Block KindName)

/-- **The filling that the online filling reads through.** -/
abbrev onlineBase : OnlineProverParts FullSizeMatrix IndexCommitterCoins Cells Unit Unit :=
  onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- **The pairs of that filling.** -/
abbrev onlinePairs := fillPairs matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- **A lot of that filling as the online filling holds it.** -/
abbrev onlineLot (files : VerifierAndGoals.PublicFiles)
    (L : HLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit) :
    HLot (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst Cells) Unit :=
  L.thru (Local.thru id (tableCoins files)) (Local.thru id (tableCoins files))

variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files} {S Cl : Type}
  {bs : List (Block S Cl)} {κ : KindName}
  {L : HLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit}

/-- **The form for one lot, paid at its sides read through.** A kind supplies its lot L, that each
side of the lot as the online filling holds it pays at the return (hpay), and that its pair is the
only one of its kind (hu). -/
theorem kindPays_online (hA : onlineMaker files = .ok returned)
    (hpay : ∀ q ∈ (onlineLot files L).halves returned.Z returned.G, SidePays returned.B 0 bs q)
    (hu : ∀ M, (M, κ) ∈ onlinePairs → M = L) :
    KindPays returned.B 0 bs returned.H.first κ :=
  kindPays_through id (tableCoins files) matrixInput.dummy hA hpay (lot_alone _ _ _ _ hu _ _)

/-- **The form for one lot, paid by a law at the base filling's return.** hlaw: at every return of
the maker at the base filling, each side of the lot pays. -/
theorem kindPays_online_of_base (hA : onlineMaker files = .ok returned)
    (hlaw : ∀ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = .ok A₀ →
        ∀ q ∈ L.halves A₀.Z A₀.G, SidePays A₀.B 0 A₀.F.first.blocksInOrder q)
    (hu : ∀ M, (M, κ) ∈ onlinePairs → M = L) :
    KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first κ :=
  kindPays_through_of_base id (tableCoins files) matrixInput.dummy hA
    (K5.parts_of_atPure hA).2.range hlaw (lot_alone _ _ _ _ hu _ _)

/-- **The form for a kind with several lots.** H: each side of each pair of kind κ pays when read
through. -/
theorem kindPays_online_of_sides (hA : onlineMaker files = .ok returned)
    (H : ∀ M, (M, κ) ∈ onlinePairs → ∀ x ∈ M.halves returned.Z returned.G,
      SidePays returned.B 0 bs
        (x.thru (Local.thru id (tableCoins files)) (Local.thru id (tableCoins files)))) :
    KindPays returned.B 0 bs returned.H.first κ := by
  refine kindPays_of_through_sides id (tableCoins files) matrixInput.dummy hA
    fun M hM x hx hk => ?_
  rw [fillPairs_lots] at hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  have e := (fillPairs_kinds _ _ _ _ _ _ r hr x hx).symm.trans hk
  subst e
  exact H r.1 hr x hx

/-- **The form for a kind with a list of lots.** Ls: the kind's lots: each pair of kind κ holds one
(hu); each side of each of them, as the online filling holds it, pays at the return (hpay). -/
theorem kindPays_online_of_lots (hA : onlineMaker files = .ok returned)
    (Ls : List (HLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit))
    (hpay : ∀ M ∈ Ls, ∀ q ∈ (onlineLot files M).halves returned.Z returned.G,
      SidePays returned.B 0 bs q)
    (hu : ∀ M, (M, κ) ∈ onlinePairs → M ∈ Ls) :
    KindPays returned.B 0 bs returned.H.first κ :=
  kindPays_online_of_sides hA fun M hM _ hx => hpay M (hu M hM) _ (List.mem_map_of_mem hx)

/-- **The form for a list of lots, paid at the base filling's own sides.** No equation on a lot read
through is asked. -/
theorem kindPays_online_of_base_lots (hA : onlineMaker files = .ok returned)
    (Ls : List (HLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit))
    (hpay : ∀ M ∈ Ls, ∀ x ∈ M.halves returned.Z returned.G, SidePays returned.B 0 bs x)
    (hu : ∀ M, (M, κ) ∈ onlinePairs → M ∈ Ls) :
    KindPays returned.B 0 bs returned.H.first κ :=
  kindPays_online_of_sides hA fun M hM x hx => sidePays_thru _ _ (hpay M (hu M hM) x hx)

/-- **What `onlineProversOfCommitter` hands on.** The online provers read the return's prover through
`Committer.proverAt`, which changes its stored tables and key and leaves its first chain as it is. -/
theorem kindPays_proverAt {W₀ Rc Sd Xc Xi Ky Tr X₀ Xh : Type} (Cm : Committer W₀ Rc Sd Xc Xi Ky)
    (item₀ : Nat) {H : Prover W₀ Rc Xi Ky Tr X₀ Xh} {B : ProverCoinCounts} (hp : KindPays B 0 bs H.first κ) :
    KindPays B 0 bs (Cm.proverAt item₀ H).first κ :=
  hp

/-- The same at the shared chain. -/
theorem kindPays_proverAt_shared {W₀ Rc Sd Xc Xi Ky Tr X₀ Xh : Type}
    (Cm : Committer W₀ Rc Sd Xc Xi Ky) (item₀ : Nat) {H : Prover W₀ Rc Xi Ky Tr X₀ Xh} {B : ProverCoinCounts}
    (hp : KindPays B 1 bs H.shared κ) : KindPays B 1 bs (Cm.proverAt item₀ H).shared κ :=
  hp

/-- The same at the second chain. -/
theorem kindPays_proverAt_second {W₀ Rc Sd Xc Xi Ky Tr X₀ Xh : Type}
    (Cm : Committer W₀ Rc Sd Xc Xi Ky) (item₀ : Nat) {H : Prover W₀ Rc Xi Ky Tr X₀ Xh} {B : ProverCoinCounts}
    (hp : KindPays B 2 bs H.second κ) : KindPays B 2 bs (Cm.proverAt item₀ H).second κ :=
  hp

/-- The kinds of the thirteen pairs, in their order. -/
theorem onlinePairs_kinds :
    onlinePairs.map (·.2) =
      [KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8, .K10, .K12, .K1] := rfl

/-- **The four kinds that no lot lays pay at the first chain, for want of sides.** Conditional: hA. -/
theorem kindPays_online_empty (hA : onlineMaker files = .ok returned)
    (hκ : κ ∈ [KindName.K9, .K14, .K15, .frame]) :
    KindPays returned.B 0 bs returned.H.first κ := by
  refine kindPays_online_of_sides hA fun M hM => absurd ?_ (?_ : κ ∉ onlinePairs.map (·.2))
  · exact List.mem_map.2 ⟨_, hM, rfl⟩
  · rw [onlinePairs_kinds]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl | rfl | rfl <;> decide

/-- **The twelve kinds with lots paid, all sixteen pay at the first chain.** Conditional: hA; H. -/
theorem kindPays_online_all (hA : onlineMaker files = .ok returned)
    (H : ∀ k, k ∉ [KindName.K9, .K14, .K15, .frame] → KindPays returned.B 0 bs returned.H.first k) :
    ∀ k, KindPays returned.B 0 bs returned.H.first k := by
  intro k
  by_cases e : k ∈ [KindName.K9, .K14, .K15, .frame]
  · exact kindPays_online_empty hA e
  · exact H k e

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Under the library's head the three descriptions are one**: the one that the family reads, the
head's and the one that the maker returned. Conditional: h; hA; hPlaces; hChain. -/
theorem online_desc_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {returned : OnlineReturn Z} (hA : onlineMaker Z = .ok returned) {places : H2U.Places4}
    {firstChain : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    (hPlaces : H2U.placesOfMade returned.Z.made = .ok places)
    (hChain : ProofFile.onlineFirstChainAt returned.Z = .ok firstChain) :
    descZ returned.Z places firstChain = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧
      returned.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := by
  obtain ⟨eZ, -⟩ := atPure_at_laid h.laid hA
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : places = Np := Except.ok.inj (hPlaces.symm.trans (atPure_places h.laid hA))
  obtain rfl : firstChain = cF :=
    Except.ok.inj (hChain.symm.trans (eZ ▸ ToldDesc.pureChainAt_of_open O))
  obtain ⟨-, -, e3, -⟩ := atPure_ok hA
  exact ⟨by rw [eZ], Except.ok.inj (e3.symm.trans h.laid.value)⟩

/-- **The base filling's sides of the shared chain stand at places of the kinds K14, K1 and K12.**
Conditional: h. -/
theorem online_shared_kinds (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (G : Ground) :
    ∀ x ∈ onlineBase.shared Zp G,
      x.place.kind = .K14 ∨ x.place.kind = .K1 ∨ x.place.kind = .K12 := by
  have h6 := ProofFile.Honest.K14.nowSharedBy_at_head h (matrixInput.weights Zp)
  intro y hy
  have hy' : y ∈ K12.AtProof.sharedWithUO matrixInput Zp := hy
  rw [K12.AtProof.sharedWithUO_ok matrixInput h6, sharedWithU_ok matrixInput h6] at hy'
  rcases List.mem_append.1 hy' with hy' | hy'
  · rcases List.mem_append.1 hy' with hy' | hy'
    · have q := ProofFile.Honest.K14.six_places (Rc := IndexCommitterCoins) (Ky := OnBytes.TableKey) (X := Unit)
        { S := (VerifiableInference.Desc.K1.qAt Zp Np).S, atPoint := 0, atZeta := 6 }
        { P := VerifiableInference.Desc.K1.qAt Zp Np, atPoint := 0 } (matrixInput.weights Zp)
        (ProofFile.Honest.K14.randNow (VerifiableInference.Desc.K1.qAt Zp Np)) y hy'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at q
      rcases q with e | e | e | e | e | e | e | e <;> rw [e] <;>
        first
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
    · rw [AtFullSide.K12.halfU_place _ _ Zp y hy']
      exact Or.inr (Or.inr rfl)
  · rw [AtFullSide.K12.halfO_place _ Zp y hy']
    exact Or.inr (Or.inr rfl)

/-- **The base filling's sides of the second chain stand at places of the kind K12.** No premise. -/
theorem online_second_kinds (Zq : ProofFile.Pub) (G : Ground) :
    ∀ x ∈ onlineBase.second Zq G, x.place.kind = .K12 := by
  intro y hy
  have hy' : y ∈ (secondW matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Zq G :
      List (Placed _ _ Unit)) := hy
  unfold secondW at hy'
  split at hy'
  · rw [AtFullSide.K12.halfW_place _ _ _ _ _ _ _ _ Zq G y hy']
    rfl
  · cases hy'

/-- **A kind other than K14, K1 and K12 pays at the shared chain, for want of sides.** Conditional: h;
hA; hκ. -/
theorem kindPays_online_shared_none (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {returned : OnlineReturn Z} (hA : onlineMaker Z = .ok returned)
    (hκ : κ ≠ .K14 ∧ κ ≠ .K1 ∧ κ ≠ .K12) : KindPays returned.B 1 bs returned.H.shared κ := by
  obtain ⟨e1, -⟩ := atPure_ok hA
  have eZ : returned.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  refine kindPays_shared_of_through_sides id (tableCoins Z) matrixInput.dummy hA
    fun x hx hk => ?_
  rw [eZ] at hx
  rcases online_shared_kinds h returned.G x hx with e | e | e
  · exact absurd (hk.symm.trans e) hκ.1
  · exact absurd (hk.symm.trans e) hκ.2.1
  · exact absurd (hk.symm.trans e) hκ.2.2

/-- **A kind other than K12 pays at the second chain, for want of sides.** Conditional: hA; hκ. -/
theorem kindPays_online_second_none {returned : OnlineReturn files}
    (hA : onlineMaker files = .ok returned) (hκ : κ ≠ .K12) :
    KindPays returned.B 2 bs returned.H.second κ :=
  kindPays_second_of_through_sides id (tableCoins files) matrixInput.dummy hA fun x hx hk =>
    absurd (hk.symm.trans (online_second_kinds _ _ x hx)) hκ

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.kindPays_online_of_lots
#print axioms ProofFile.Honest.Term.kindPays_online_of_base_lots
#print axioms ProofFile.Honest.Term.kindPays_proverAt
#print axioms ProofFile.Honest.Term.kindPays_proverAt_shared
#print axioms ProofFile.Honest.Term.kindPays_proverAt_second
#print axioms ProofFile.Honest.Term.kindPays_online_all
#print axioms ProofFile.Honest.Term.online_desc_at_head
#print axioms ProofFile.Honest.Term.onlinePairs_kinds
#print axioms ProofFile.Honest.Term.kindPays_online_empty
#print axioms ProofFile.Honest.Term.online_shared_kinds
#print axioms ProofFile.Honest.Term.online_second_kinds
#print axioms ProofFile.Honest.Term.kindPays_online_shared_none
#print axioms ProofFile.Honest.Term.kindPays_online_second_none
#print axioms ProofFile.Honest.Term.kindPays_online
#print axioms ProofFile.Honest.Term.kindPays_online_of_base
#print axioms ProofFile.Honest.Term.kindPays_online_of_sides
