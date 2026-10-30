-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsK12.lean: THE JOIN AT THE ONE NUMBER THAT STAYS (354) of
"seatsCarried" and "placesAre": seats_one's premise k12 (Johnson/IMR/SendsHead.lean), to its letter,
under
two premises on the plan. Statements and proofs.

What is joined.
  the sub-protocol   a sub-protocol of a lot of the seat at the place ⟨1, none, 2, K12⟩ is
                     (K12.atFinish (H2U.p12OfMade Z.made)).retype: lot_of_kind and blocks_mem
                     (Johnson/IMR/LotKinds.lean), as in back_of (Johnson/IMR/BackSeat.lean)
  what it sends      sends_atFinish (Johnson/Desc/K12/Coin/SendsAtFinish.lean): an accepting step
                     keeps the codes, appends sendsFrom π 0 π.nums.stages.tail to the book, and
                     keeps "as many oracle messages as places"
  what the list says snAt_k12 (Johnson/Desc/K12/Door/SentAtPlace.lean): at a place of the kind K12
                     snAt is that very list
  place_354          number 354 of the written list is that place                     [the kernel]
  k12_names          the sub-protocol, named
  k12_sendsAt        SendsAt at the named sub-protocol
  k12_debt           **seats_one's premise k12**, at every fence G (so at ReachedAt … 354)

THE TWO PREMISES, both on the plan alone, both K12's files' to pay (not shown here): hp:
the proximity test's test on the plan accepts at p12OfMade Z.made; ho: nums.ownMask = false there.
Limits. seats_one itself is not called here (Johnson/IMR/SendsHead.lean is not imported): the call
is
seats_one hS hR O p K (k12_debt hp ho) …. Nothing on soundness.

-/
import Johnson.IMR.SendsFold
import Johnson.IMR.LotKinds
import Johnson.IMR.WrittenList
import Johnson.Desc.K12.Coin.SendsAtFinish
import Johnson.Desc.K12.Door.SentAtPlace

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (atFinish proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Door (snAt snAt_k12)
open VerifiableInference.Desc.K12.Coin (sends_atFinish)
open H2K.JointK H2K.Out
open ProofFile (Cl)

/-- Number 354 of the written list is the proximity test's place behind the links. -/
theorem place_354 :
    placesW[354]? = some { chain := 1, link := none, piece := 2, kind := .K12 } := by
  decide +kernel

/-- **The sub-protocol, named.** -/
theorem k12_names {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hL : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (ep : b'.place = { chain := 1, link := none, piece := 2, kind := .K12 }) :
    b' = (atFinish (H2U.p12OfMade Z.made)).retype := by
  obtain ⟨L, hL, hb'⟩ := hL
  obtain rfl : L = VerifiableInference.Desc.K12.lot Z := lot_of_kind hL hb' (by rw [ep]; rfl)
  rcases blocks_mem hb' with ⟨x, hx, rfl⟩ | h'
  · obtain rfl := List.mem_singleton.1 hx
    rfl
  · exact nomatch h'

/-- What the named sub-protocol sends. -/
theorem k12_sendsAt (π : VerifiableInference.Desc.K12.P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true) (ho : π.nums.ownMask = false) (ft : ℕ)
    (codes : Codes) :
    SendsAt ft codes (VerifiableInference.Desc.K12.Coin.sendsFrom π 0 π.nums.stages.tail)
      ((atFinish π).retype : Block S Cl) :=
  fun s s' rs cols n hy hc => sends_atFinish π hp ho ft codes s s' rs cols n hy hc

/-- **seats_one's premise k12.** -/
theorem k12_debt {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {ft : ℕ} {G : S → Prop}
    (hp : (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Blk').planOk = true)
    (ho : (H2U.p12OfMade Z.made).nums.ownMask = false) :
    ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      SendsOn ft Z.first.codes G (snAt Z G₀ placesW 354) b' := by
  intro b' hL ep
  rw [k12_names hL ep, snAt_k12 Z G₀ placesW 354 2 none place_354]
  exact (k12_sendsAt _ hp ho ft Z.first.codes).on

end IM

#print axioms IM.place_354
#print axioms IM.k12_names
#print axioms IM.k12_sendsAt
#print axioms IM.k12_debt
