-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/KindHandsIn.lean: K4's hand-in READ FROM THE OTHER
SIDE, in the form of the rule's premises: not «at every row of K4's lot» but «at every list of parts
of a description's three chains at a place of the kind K4». CONDITIONAL: on h, hA and one premise on
the lists G. The pattern is the lookups' (Honest/K3/Term/LookupKindHandsIn.lean).

  `k4_half_no_second_stop`   no part of K4's half has a second stop: the first arm of `PartsHeld`
      (Johnson/FrontRoad/SessionStopsOfParts.lean).
  `noK4PlaceInTheSharedTable`, `noK4PlaceInTheLastTable`, `noK4PlaceInTheLaterChains`   no
      sub-protocol of the shared or of the second chain is at a place of the kind K4.
  `half_at_a_block`, `k4_no_half_in_the_later_chains`   so no half of the kind K4 stands in the
      prover's shared or second chain.
  `sideStandsAtABlock`   a list that has a side is at the place of a sub-protocol of the chain.
  `OnlyK4AtK4Places`   THE ONE PREMISE ON G: a list of G.first at a place of the kind K4 is, its A and
      B forgotten, a row of K4's lot. Its holder is whoever gathers G (IOP's `overlaySlots`).
  `k4KindHandsIn`   **`Good`, at the pre of its place, its chain's face and numbers and the list's own
      On and bud, at every list of the three chains at a place of the kind K4.**

Limits. THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; `Good` at A and B False: the limits of
Law/ExactFresh/HandIn.lean. In the shared and the second chain the sentence holds because no such
list has a side: TRUE AND EMPTY THERE. `OnlyK4AtK4Places` is shown here at no G. No property is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.HandIn
import Johnson.Desc.ProofFile.Honest.Owed
import Johnson.ToldDescR.PlacesAtTable
import Johnson.ToldDescR.LastPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open P5J (AtMgA TS)

/-- **No part of K4's half has a second stop**, whatever the readers. -/
theorem k4_half_no_second_stop {W₀ Rc Xi Tr X : Type} (Q : K4Pub) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    ∀ p ∈ (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts, ∀ u l o,
      p.hid u l o = none := by
  intro p hp
  have e : (k4Sided (Rc := Rc) (X := X) Q cells weights tokens (look Q)).map (·.1) =
      k4Row Q cells weights tokens (look Q) := by
    unfold k4Sided
    refine List.map_fst_zip ?_
    unfold k4Row k4RowIn k4Sims k4Sorts
    cases (Q.g == 0) <;> exact Nat.le_refl _
  have hp' : p ∈ k4Row (Rc := Rc) (X := X) Q cells weights tokens (look Q) := hp
  rw [← e] at hp'
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp'
  exact (k4_sided_no_stop Q cells weights tokens (look Q) hy).2.1

/-- No place of the shared chain's table is of the kind K4. -/
theorem noK4PlaceInTheSharedTable (split : Bool) :
    ∀ p ∈ ToldDesc.sharedList split, p.kind ≠ KindName.K4 := by
  cases split <;> decide

/-- No place of the second chain's table is of the kind K4. -/
theorem noK4PlaceInTheLastTable : ∀ p ∈ ToldDesc.fourPlaces, p.kind ≠ KindName.K4 := by
  decide

/-- **No sub-protocol of the shared or of the second chain is at a place of the kind K4**, at every
description that `onlineDescription` makes and that passes the tests on the plan. -/
theorem noK4PlaceInTheLaterChains {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {Fd : FileDescription Inst} (made : onlineDescription o pol lay KL = .ok Fd) (plan : Fd.planOk = true) :
    (∀ b ∈ Fd.shared.blocksInOrder, b.place.kind ≠ .K4) ∧ ∀ b ∈ Fd.second.blocksInOrder, b.place.kind ≠ .K4 := by
  obtain ⟨_, N, -, -, fits, -⟩ := ToldDesc.shared_fits_descPure made plan
  rw [← ToldDesc.sharedList_eq] at fits
  have shared : Fd.shared.blocksInOrder.map (·.place) = ToldDesc.sharedList N.O.isSome := eq_of_beq fits
  have second := ToldDesc.last_places_descPure made
  exact ⟨fun b inChain => noK4PlaceInTheSharedTable _ b.place
      (shared ▸ List.mem_map.2 ⟨b, inChain, rfl⟩),
    fun b inChain => noK4PlaceInTheLastTable b.place
      (second ▸ List.mem_map.2 ⟨b, inChain, rfl⟩)⟩

/-- A half at a list of halves without strays stands at the place of a sub-protocol of the list. -/
theorem half_at_a_block {S Cl V W Y : Type} {bs : List (Block S Cl)} {hs : List (Placed V W Y)}
    (h : (strays bs hs).isEmpty = true) {g : Placed V W Y} (hg : g ∈ hs) :
    ∃ b ∈ bs, b.place = g.place := by
  by_contra hn
  have hm : g.place ∈ strays bs hs := by
    refine List.mem_map.2 ⟨g, List.mem_filter.2 ⟨hg, ?_⟩, rfl⟩
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro ha
    obtain ⟨b, hb, e⟩ := List.any_eq_true.1 ha
    exact hn ⟨b, hb, beq_iff_eq.1 e⟩
  rw [List.isEmpty_iff] at h
  rw [h] at hm
  cases hm

/-- **No half of the kind K4 stands in the prover's shared or second chain**, at a return of the
maker whose description passes the tests on the plan: at any filling. -/
theorem k4_no_half_in_the_later_chains {W₂ Rc₂ Tr₂ X₂ X₀₂ : Type} {o : SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {P : OnlineProverParts W₂ Rc₂ Tr₂ X₀₂ X₂} {A : OnlineProverWithDescription W₂ Rc₂ Tr₂ X₀₂ X₂}
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) (plan : A.F.planOk = true) :
    (∀ g ∈ A.H.shared, g.place.kind ≠ .K4) ∧ ∀ g ∈ A.H.second, g.place.kind ≠ .K4 := by
  obtain ⟨-, -, s2, s3, -⟩ := atPure_tests hA
  obtain ⟨n2, n3⟩ := noK4PlaceInTheLaterChains (atPure_ok hA).2.2.1 plan
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨b, hb, e⟩ := half_at_a_block s2 hg
    exact e ▸ n2 b hb
  · obtain ⟨b, hb, e⟩ := half_at_a_block s3 hg
    exact e ▸ n3 b hb

/-- A list that has a side is at the place of a sub-protocol of the chain. -/
theorem sideStandsAtABlock {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (L : Lettered Bk S Cl V W Y Pb)
    (blocks : List (Block S Cl)) (falls : List (Fall S)) (σ : Side S Cl V W Y Pb)
    (side : L.side blocks falls = some σ) : ∃ b ∈ blocks, b.place = L.place := by
  unfold Lettered.side Side.seated at side
  obtain ⟨b, found, _⟩ := Option.map_eq_some_iff.1 side
  exact ⟨b, List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Ky Tr X₀ X : Type}

/-- **THE ONE PREMISE ON THE LISTS**: a list of G.first at a place of the kind K4 is, its A and B
forgotten, one of the rows. -/
def OnlyK4AtK4Places {Bk : ProverCoinCounts}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X)
    (rows : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)) :
    Prop :=
  ∀ L ∈ G.first, L.place.kind = .K4 → L.bare ∈ rows

/-- CONDITIONAL: on h, hA and the one premise on the lists. **THE KIND K4 HANDS IN: `Good` AT EVERY
LIST OF THE THREE CHAINS AT A PLACE OF THE KIND K4: THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT
LAW; A' := B' := False.** -/
theorem k4KindHandsIn {W₂ Rc₂ Tr₂ X₂ X₀₂ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₂ Rc₂ Tr₂ X₀₂ X₂} {A : OnlineProverWithDescription W₂ Rc₂ Tr₂ X₀₂ X₂}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B W₀ Rc Ky Tr X₀ X)
    (only : OnlyK4AtK4Places G ((k4SLot cells weights look).rows A.Z A.G)) :
    (∀ L ∈ G.first, L.place.kind = .K4 →
      ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder G.falls₁ = some σ →
        ∃ A' B', Good (preOf 0 0 (earlierOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 0)
            (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder L.place) .own σ A.B
          (orderOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) 0 0 A' B' L.On L.bud) ∧
    (∀ L ∈ G.shared, L.place.kind = .K4 →
      ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder G.falls₂ = some σ →
        ∃ A' B', Good (preOf 1 0 (earlierOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 1)
            (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder L.place) .shared σ A.B
          (orderOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) 1 0 A' B' L.On L.bud) ∧
    ∀ L ∈ G.second, L.place.kind = .K4 →
      ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder G.falls₃ = some σ →
        ∃ A' B', Good (preOf 2 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber
            (earlierOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 2)
            (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder L.place) .own σ A.B
          (orderOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) 2
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber A' B' L.On L.bud :=
  ⟨fun L inFirst ofKind σ side => ⟨_, _,
      k4_good_at_maker h.scope h.reads h.laid hA cells weights look (only L inFirst ofKind) side _
        .own _ 0 0⟩,
    fun L _ ofKind σ side => by
      obtain ⟨b, inChain, e⟩ := sideStandsAtABlock L _ _ σ side
      exact absurd (e ▸ ofKind)
        ((noK4PlaceInTheLaterChains h.laid.value h.laid.planOk).1 b inChain),
    fun L _ ofKind σ side => by
      obtain ⟨b, inChain, e⟩ := sideStandsAtABlock L _ _ σ side
      exact absurd (e ▸ ofKind)
        ((noK4PlaceInTheLaterChains h.laid.value h.laid.planOk).2 b inChain)⟩

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4_half_no_second_stop
#print axioms ProofFile.Honest.K4.ExactFresh.noK4PlaceInTheSharedTable
#print axioms ProofFile.Honest.K4.ExactFresh.noK4PlaceInTheLastTable
#print axioms ProofFile.Honest.K4.ExactFresh.noK4PlaceInTheLaterChains
#print axioms ProofFile.Honest.K4.ExactFresh.k4_no_half_in_the_later_chains
#print axioms ProofFile.Honest.K4.ExactFresh.sideStandsAtABlock
#print axioms ProofFile.Honest.K4.ExactFresh.OnlyK4AtK4Places
#print axioms ProofFile.Honest.K4.ExactFresh.k4KindHandsIn
