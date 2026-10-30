--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OVER THE COMPOSER's LettersAll.lean, whose `𝔇All` has neither G₀ nor sh:
wt and cr1 are letters, and the
premise hN speaks at `Meaning.seatBy (Meaning.fLay …)`. The four statements follow these letters;
no proof turns.
Johnson/Top/H0/Walk/FrameReadKeptAtAll.lean: THE THREE SENTENCES ON THE COMPOSED MEANING's
PARAMETERS (`ReadKept`, FrameFieldsBack.lean) AND THE TWO PREMISES `DecRides`, `SeedRides`
(FramePromiseRides.lean) AT THE COMPOSER's OWN CLOSED STRUCTURE OF PARAMETERS `P5J.At.𝔇All`
(Johnson/P5J/LettersAll.lean). Statements and proofs: three equations by definition, and calls.

What is said.
  `meantAt_all`: **`MeantAt (𝔇All …) (seats Zp) (fun q => (Meaning.backReq (reqB q)).getD d₀)`**
    (FrameReadKeptAt.lean): the reader of the OOD samples is `smpNamed` at the plan's seats: by
    definition; the decoder of the committed table does not read the verifier's state: the
    composer's own `noRec_decT`; the reader of the request reads the public part alone: by
    definition.
  `readKept_all`: **`ReadKept (𝔇All …) base`, at every base.**
  `decRides_all`: `DecRides (𝔇All …) rel` at every relation rel.
  `seedRides_all`: `SeedRides (𝔇All …) rel base In` at every rel that gives `Kept`.

Limits. 𝔇All takes letters of its own (the second hash o; Zp, Np, cF; the coding E; five premises on
the plan; x; wt, cr1; nR): all are letters here too: whether its premises can be met together is the
composer's to show. Nothing on 𝔇All's fields cr1 and headPart. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameReadKeptAt
import Johnson.P5J.LettersAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated)
open VerifiableInference.Desc.First (S)
open P5J.At

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
  {pp : Inst.Model.ScalesAndPolicy}
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt
    (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181) OnBytes.Flat.numsFull pp))
  (hs : Desc.K14.Law.fullShapeB
    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
  (lay : ByteArray)
  (hL : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
  (hN : SeatsNamed (arr Zp) (N Zp cF) (Meaning.sizesOf (X Zp))
    (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))))
  (hG : GroupsSeated (ms Zp lay) (N Zp cF))
  (x : VerifiableInference.Desc.First.Look.Place)
  (wt cr1 : ℕ → ProofFile.InstPub × P5J.TS → Strs →
    VerifiableInference.Desc.Wit (VerifiableInference.Desc.Sound.CellsQ OnBytes.Flat.numsFull.rows
      (P5J.colsAt OnBytes.Flat.numsFull)) Tok VerifiableInference.Desc.Sound.MsgT → Prop)
  (nR : ℕ)

/-- **The closed structure's three parameters are the meant terms.** -/
theorem meantAt_all :
    MeantAt (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) (seats Zp)
      (fun q => (Meaning.backReq (reqB q)).getD d₀) where
  smp := rfl
  dec := noRec_decT o Zp Np cF E hs
  req _ := rfl

/-- **THE THREE SENTENCES AT THE CLOSED STRUCTURE.** -/
theorem readKept_all (base : Nat) :
    ReadKept (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) base :=
  readKept_meant (meantAt_all o Zp Np cF E hs lay hL hN hG x wt cr1 nR) base

theorem decRides_all (rel : S → S → Prop) :
    DecRides (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) rel :=
  decRides_noRec (meantAt_all o Zp Np cF E hs lay hL hN hG x wt cr1 nR).dec rel

theorem seedRides_all {rel : S → S → Prop} (hrel : ∀ s t, rel s t → Kept s t) (base : Nat)
    (In : ProofFile.InstPub × S → Strs → Prop) :
    SeedRides (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) rel base In :=
  seedRides_meant (meantAt_all o Zp Np cF E hs lay hL hN hG x wt cr1 nR) hrel base In

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.meantAt_all
#print axioms Johnson.Desc.First.Walk.Tied.readKept_all
#print axioms Johnson.Desc.First.Walk.Tied.decRides_all
#print axioms Johnson.Desc.First.Walk.Tied.seedRides_all
