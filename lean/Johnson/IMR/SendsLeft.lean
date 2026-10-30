-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsLeft.lean: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre»
(Johnson/Desc/Sound/SmpPlaces.lean): WHAT IS LEFT, AFTER THE ARMS (229), K7's PLACE (1) AND K1's 52:
282 OF THE 358 NUMBERS ARE PAID; 76 STAY, IN SIX DEBTS, EACH AT ITS OWN PLACE's LETTERS, AT sn :=
snAt Z Bs.G₀ placesW (Johnson/Desc/K12/Door/SentAtPlace.lean),
codes := Z.first.codes, EACH ASKED AT THE STATES THAT THE FOLD FROM s₀ REACHES IN FRONT OF IT ALONE:
    k2link   (23) K2's code switch at a link's first place, l = 1 … 23: the lot's own sub-protocol at (1, some l, 1, K2).
    k2head   (1)  K2 at the head's link's second place (number 339).
    batch    (25) the chain's own link's batching at the link's own gatherer: sends nothing.
    behind   (25) the sub-protocol behind it: the like.
    k2finish (1)  K2's finish (353).
    k12      (1)  the proximity test (354).
  debts_left        in scope: these six ⟹ SendDebts ft Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀.
  seats_left        THE TOP, IN THE TWO Bools' OWN LETTERS: SendDebts at s₀ := ProofFile.startS Z p (by debts_left: the six) · that state bears no mark · the plan's side hL at the tables' own Ld (the conclusion of seats_side, Johnson/Desc/K12/Door/SentAtPlace.lean: held by Lean in seats_under_test) ⟹ behind the first k sub-protocols: K12.Door.atFirstSeats Ld = true (FoldFacts' field's own Bool) · placesAre Ld.places = true.
  seats_under_test  the same with hL drawn from seats_side: under its one test with code sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) and laidAtCodes Z.first.codes Z.made.proof.1 = some Ld.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
What is not claimed. The six debts. The plan's side. No soundness.
-/
import Johnson.IMR.SendsK1

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S kindsBeforeBatching backKinds)
open VerifiableInference.Desc.K12.Coin (laidOf SeatsPrefix)
open VerifiableInference.Desc.K12.Door (snAt)
open ProofFile (Cl)

theorem first_kind : ∀ l < 24, (kindsBeforeBatching (subAt l) (l == 0))[0]? =
    some (if l = 0 then KindName.K1 else KindName.K2) := by decide

theorem hear_k2 : ∀ l < 25, ∀ i < 9, 1 ≤ i → (kindsBeforeBatching (subAt l) (l == 0))[i]? = some KindName.K2 →
    l = 24 ∧ i = 1 := by decide

theorem hear_no_k12 : ∀ l < 25, ∀ i < 9, (kindsBeforeBatching (subAt l) (l == 0))[i]? ≠ some KindName.K12 := by
  decide

theorem hear_lt9 : ∀ l < 25, (kindsBeforeBatching (subAt l) (l == 0)).length ≤ 9 := by decide

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **WHAT IS LEFT.** -/
theorem debts_left (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {s₀ : S}
    (k2link : ∀ l, 1 ≤ l → l < 24 → ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 } →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + 2))
        (snAt Z Bs.G₀ placesW (14 * l + 2)) b')
    (k2head : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 } →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ 339) (snAt Z Bs.G₀ placesW 339) b')
    (batch : ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + nAt l + 2)) []
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)))
    (behind : ∀ l < 25, ∀ (Lk : Link S Cl) (b : Block S Cl), c.links[l]? = some Lk →
      b.rounds = [] → (∀ s rs gs, b.decide s rs gs = Lk.runBehind s) →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + nAt l + 3)) [] b)
    (k2finish : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 1, kind := .K2 } →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ 353) (snAt Z Bs.G₀ placesW 353) b')
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ 354) (snAt Z Bs.G₀ placesW 354) b') :
    SendDebts ft Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀ := by
  refine debts_at_snAt hS hR O ?_ ?_ batch behind ?_
  · intro l hl k b' hk lot hp
    have e := (first_kind l hl).symm.trans hk
    by_cases h0 : l = 0
    · subst h0
      obtain rfl : KindName.K1 = k := Option.some.inj e
      exact (sends_K1_link O (l := 0) (i := 0) (by omega) hk lot hp).on
    · rw [if_neg h0] at e
      obtain rfl : KindName.K2 = k := Option.some.inj e
      exact k2link l (by omega) hl b' lot hp
  · intro l hl i k b' hi hk hs lot hp
    have hi9 : i < 9 := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hk).1 (hear_lt9 l hl)
    have hk3 : k = .K1 ∨ k = .K2 ∨ k = .K12 := by
      revert hs
      cases k <;> simp [senderKind]
    rcases hk3 with rfl | rfl | rfl
    · exact (sends_K1_link O hl hk lot hp).on
    · obtain ⟨rfl, rfl⟩ := hear_k2 l hl i hi9 hi hk
      exact k2head b' lot hp
    · exact absurd hk (hear_no_k12 l hl i hi9)
  · intro j k b' hk hs lot hp
    rcases j with _ | _ | _ | _ | j
    · obtain rfl : KindName.K2 = k := Option.some.inj hk
      exact k2finish b' lot hp
    · obtain rfl : KindName.K12 = k := Option.some.inj hk
      exact k12 b' lot hp
    · obtain rfl : KindName.K13 = k := Option.some.inj hk
      exact nomatch hs
    · obtain rfl : KindName.K1 = k := Option.some.inj hk
      exact (sends_K1_back O lot hp).on
    · exact nomatch hk

/-- **THE TOP, FROM WHAT IS LEFT.** -/
theorem seats_left (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} (p : ProofFile.InstPub)
    (D : SendDebts ft Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p))
    (hu : (ProofFile.startS Z p).failed = none) {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hL : laidOf Z.first.codes ((List.range 358).flatMap (snAt Z Bs.G₀ placesW)) =
      some (VerifiableInference.Desc.K12.Door.toTree Ld)) {k : ℕ} (hk : k ≤ 358)
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld out.1 = true ∧
      VerifiableInference.Desc.placesAre Ld.places out.1.st out.1.book = true := by
  obtain ⟨a, b⟩ := seats_start hS hR O p D hu hL hk hf
  exact ⟨door_seats a, b⟩

/-- **… AND WITH THE PLAN's SIDE AS seats_side (Johnson/Desc/K12/Door/SentAtPlace.lean) BRINGS IT DOWN**: under its one test with code (sendsAreB; evaluated nowhere yet). That seats_side ends in seats_left's hL is held by Lean here. -/
theorem seats_under_test (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} (p : ProofFile.InstPub)
    (D : SendDebts ft Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p))
    (hu : (ProofFile.startS Z p).failed = none) {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    {k : ℕ} (hk : k ≤ 358) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld out.1 = true ∧
      VerifiableInference.Desc.placesAre Ld.places out.1.st out.1.book = true :=
  seats_left hS hR O p D hu
    (VerifiableInference.Desc.K12.Door.seats_side Z Bs.G₀ placesW 358 Z.first.codes Ld hB hLd) hk hf

end

end IM

#print axioms IM.seats_under_test
#print axioms IM.seats_left
#print axioms IM.debts_left
