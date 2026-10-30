-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsAll.lean: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre»
(Johnson/Desc/Sound/SmpPlaces.lean): THE SUM: 330 OF THE 358 NUMBERS ARE PAID OUTRIGHT
(Johnson/IMR/SendsArms.lean's arms 229 · K7's place 1 · K1's 52 · the batching and behind it at l <
24: 48); K2's 25 ARE PAID UNDER K2Fences (three sentences on reached states, which
Johnson/IMR/MsgsBehind.lean has proved
over another build: fence1_link · fence1_head · fence1_finish); THREE NUMBERS STAY AS DEBTS: the head's link's batching (347) and the sub-protocol behind it (348) · the proximity test (354).
  debts_three       in scope: K2Fences · batch24 · behind24 · k12 ⟹ SendDebts ft Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀.
  seats_three       THE TOP: with them at s₀ := ProofFile.startS Z p, that state without a mark, and the plan's side under the one test with code (sendsAreB): behind the first k sub-protocols, k ≤ 358: K12.Door.atFirstSeats Ld = true (FoldFacts' field's own Bool) · placesAre Ld.places = true.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
What is not claimed. K2Fences in the build on which this file was written · the three debts · the plan's test (evaluated nowhere). No soundness.
-/
import Johnson.IMR.SendsK2
import Johnson.IMR.SendsRest

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (snAt)
open ProofFile (Cl)

set_option maxRecDepth 1000000 in
theorem place_339 : placesW[339]? = some { chain := 1, link := some 24, piece := 2, kind := .K2 } := by
  decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE SUM.** -/
theorem debts_three (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {s₀ : S}
    (K : K2Fences ft Z Bs.G₀ c s₀)
    (batch24 : ∀ Lk : Link S Cl, c.links[24]? = some Lk →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ 347) []
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)))
    (behind24 : ∀ (Lk : Link S Cl) (b : Block S Cl), c.links[24]? = some Lk → b.rounds = [] →
      (∀ s rs gs, b.decide s rs gs = Lk.runBehind s) →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ 348) [] b)
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ 354) (snAt Z Bs.G₀ placesW 354) b') :
    SendDebts ft Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀ := by
  refine debts_left hS hR O ?_ ?_ ?_ ?_ ?_ k12
  · intro l h1 hl b' lot hp
    have hk := first_kind l hl
    rw [if_neg (by omega)] at hk
    exact sends_K2_link lot hp (hear_placeW (by omega) hk) (K.link l (by omega))
  · intro b' lot hp
    exact sends_K2_link lot hp place_339 K.head
  · intro l hl Lk e1
    by_cases h24 : l < 24
    · exact sends_batch hS hR O h24 e1
    · obtain rfl : l = 24 := by omega
      exact batch24 Lk e1
  · intro l hl Lk b e1 hr hd
    by_cases h24 : l < 24
    · exact sends_behind hS hR O h24 e1 hd
    · obtain rfl : l = 24 := by omega
      exact behind24 Lk b e1 hr hd
  · intro b' lot hp
    exact sends_K2_finish lot hp K.finish

/-- **THE TOP.** -/
theorem seats_three (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} (p : ProofFile.InstPub)
    (K : K2Fences ft Z Bs.G₀ c (ProofFile.startS Z p))
    (batch24 : ∀ Lk : Link S Cl, c.links[24]? = some Lk →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder (ProofFile.startS Z p) 347) []
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)))
    (behind24 : ∀ (Lk : Link S Cl) (b : Block S Cl), c.links[24]? = some Lk → b.rounds = [] →
      (∀ s rs gs, b.decide s rs gs = Lk.runBehind s) →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder (ProofFile.startS Z p) 348) [] b)
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder (ProofFile.startS Z p) 354)
        (snAt Z Bs.G₀ placesW 354) b')
    (hu : (ProofFile.startS Z p).failed = none) {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    {k : ℕ} (hk : k ≤ 358) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld out.1 = true ∧
      VerifiableInference.Desc.placesAre Ld.places out.1.st out.1.book = true :=
  seats_under_test hS hR O p (debts_three hS hR O K batch24 behind24 k12) hu hB hLd hk hf

end

end IM

#print axioms IM.debts_three
#print axioms IM.seats_three
