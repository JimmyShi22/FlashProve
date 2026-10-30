-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAt2.lean: MORE CLOSED LETTERS AT THE TERM OF THE IOP AS WRITTEN IN LEAN (over
Johnson/P5J/LettersAt.lean; namespace P5J.At): the table's extractor; the data of the proximity
test's public items; the last sub-protocols' numbers; and that the first chain's sub-protocols stand
at the written list of places. A joint build of files of several kinds.

What is said.
  ext       the table of joints' extractor (`extQAt`, Johnson/Desc/Sound/BordersFill.lean) at At's
            letters: cs · G · arr · smp · ms · decT · c₀ · tokOf · N · links · ps · get. It has no
            letter of its own.
  laid?     the seats and the trees' shapes of the proof's first chain, as the program that makes
            the list of rounds lists them, at the first chain's codes: AN OPTION. `laidB`: the test
            "it can be laid". NO DEFAULT ANSWERS IN ITS PLACE: `d12 L` takes the list; `laid_some`
            hands it out where the test accepts.
  d12 L     the data of the proximity test's public items: first tree 0 · L · the shapes of the
            chain's oracle messages, in the order of sending.
  P13       the last sub-protocols' numbers off the list of rounds (`K13.whereOf`).
  chain_places     where the chain's maker returns a chain, the places of its flat list are the
            driver's list at the public parameters' sorts of segments, at one of the two values of
            "several".
  blockPlaces_at   where the IOP's value is opened, the sorts of segments are the written list and
            a sub-protocol of the kind K13 stands in the chain: the sub-protocols' own places ARE
            At.ps: the premise of `N_atBlocks`.
  N_closed  so there N is the table's numbers closed over the sub-protocols.

Limits. (1) `hsub` (the public parameters' sorts of segments are the written list) and `hK` (a
sub-protocol of the kind K13 stands in the chain) are premises on public data. (2) The full size
alone. (3) Definitions and their unfoldings: NO MEMBER. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LettersAt
import Johnson.IMR.SeatOpen
import Johnson.Desc.First.Driver.PlacesLaw
import Johnson.Desc.K12.Door.LaidAt
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.K12.Door.FillK12
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (FileDescription Chain Block Place KindName)
open VerifiableInference.Desc.First (ModelPart flatPlacesOf blockPlaces)
open VerifiableInference.Desc.K12.Door (Laid K12Data laidAtCodes msgsOfChain)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- The seats and the trees' shapes of the proof's first chain, at the first chain's codes. -/
def laid? : Option Laid := laidAtCodes (cs Zp) Zp.made.proof.1

/-- The test: the list can be laid. -/
def laidB : Bool := (laid? Zp).isSome

theorem laid_some (h : laidB Zp = true) : ∃ L, laid? Zp = some L := Option.isSome_iff_exists.1 h

/-- **The data of the proximity test's public items**, at a list that is handed in. -/
def d12 (L : Laid) : K12Data := ⟨0, L, msgsOfChain Zp.made.proof.1⟩

/-- **The last sub-protocols' numbers.** -/
def P13 : VerifiableInference.Desc.K13.Where := VerifiableInference.Desc.K13.whereOf Zp

section Ext
variable {pp : Inst.Model.ScalesAndPolicy}
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
    OnBytes.Flat.numsFull pp))
  (hs : Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
  (lay : ByteArray)

/-- **The table's extractor at sub-protocol number k**, at At's letters. -/
noncomputable def ext {Fr : VerifiableInference.Desc.Sound.Frame} (k : ℕ)
    (a b : (ProofFile.InstPub × TS) × Fr.E.Str)
    (w : VerifiableInference.Desc.Wit (CellsM OnBytes.Flat.numsFull) Tok
      VerifiableInference.Desc.Sound.MsgT) :
    VerifiableInference.Desc.Wit (CellsM OnBytes.Flat.numsFull) Tok
      VerifiableInference.Desc.Sound.MsgT :=
  VerifiableInference.Desc.Sound.extQAt (cs Zp) (G o Zp Np cF) (arr Zp) (smp Zp) (ms Zp lay)
    (decT o Zp Np cF E hs) c₀ tokOf (N Zp cF) links ps get k a b w

end Ext

/-- Where the chain's maker returns a chain, its flat list's places are the driver's. -/
theorem chain_places {Z : ProofFile.Pub} {base : List (Block TS ProofFile.Cl)}
    {fr : List (ProofFile.FrameRole × Block TS ProofFile.Cl)} {road : ProofFile.Gather TS ProofFile.Cl}
    {c : Chain TS ProofFile.Cl} (hc : ProofFile.chainBy Z base fr road = .ok c) :
    ∃ several, c.blocksInOrder.map (·.place) = flatPlacesOf (ProofFile.subsOf Z) several := by
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        exact ⟨_, VerifiableInference.Desc.First.flat_places _ _ _ _ h1⟩

set_option maxRecDepth 100000 in
/-- Without "several" the written list has no place of the kind K13. -/
theorem no_K13 : ∀ p ∈ flatPlacesOf fullLinks false, p.kind ≠ KindName.K13 := by decide

/-- **The sub-protocols' own places are the written list.** -/
theorem blockPlaces_at {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
    {base : List (Block TS ProofFile.Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Zp Bs base cF A B) (hsub : ProofFile.subsOf Zp = fullLinks)
    (hK : ∃ b ∈ cF.blocksInOrder, b.place.kind = KindName.K13) : blockPlaces cF.blocksInOrder = ps := by
  obtain ⟨several, e⟩ := chain_places O.chain
  rw [hsub] at e
  cases several with
  | true => exact e
  | false =>
    obtain ⟨b, hb, hk⟩ := hK
    exact absurd hk (no_K13 b.place (by rw [← e]; exact List.mem_map.2 ⟨b, hb, rfl⟩))

/-- **There N is the table's numbers closed over the sub-protocols.** -/
theorem N_closed {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
    {base : List (Block TS ProofFile.Cl)} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Zp Bs base cF A B) (hsub : ProofFile.subsOf Zp = fullLinks)
    (hK : ∃ b ∈ cF.blocksInOrder, b.place.kind = KindName.K13) :
    N Zp cF = (P5T.numbersOf (pseats Zp)).atBlocks (shape Zp) links cF.blocksInOrder :=
  N_atBlocks Zp cF (blockPlaces_at o Zp cF O hsub hK)

end P5J.At

#print axioms P5J.At.laid_some
#print axioms P5J.At.chain_places
#print axioms P5J.At.no_K13
#print axioms P5J.At.blockPlaces_at
#print axioms P5J.At.N_closed
