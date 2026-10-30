-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersRec.lean: THE STRUCTURE OF THE COMPOSED MEANING's LETTERS (MgData, Johnson/Desc/Sound/MgAll.lean) WITH THE CLOSED VALUES LAID (Johnson/P5J/LettersAt.lean). Two definitions.
  At.𝔇At … 𝔇₀: 𝔇₀: a letter for what is not closed; every closed field is laid over it.
  At.𝔇Ok ok E 𝔇₀: the same with its four premises paid from the named tests (PlanOk): no scope is wanted (H's seat: in the label's form).
Limits. Definitions. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.PlanOk
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MgData)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

section Rec
variable {pp : Inst.Model.ScalesAndPolicy}
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
    OnBytes.Flat.numsFull pp))
  (hs : Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
  (lay : ByteArray)
  (hL : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
  (hN : VerifiableInference.Desc.Sound.SeatsNamed (arr Zp) (N Zp cF) (Meaning.sizesOf (X Zp))
    (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))))
  (hG : VerifiableInference.Desc.Sound.GroupsSeated (ms Zp lay) (N Zp cF))

/-- **THE STRUCTURE OF THE COMPOSED MEANING's LETTERS, AT THE TERM**: 𝔇₀: a letter for what is not closed; every closed field is laid over it. -/
noncomputable def 𝔇At {nR : ℕ}
    (𝔇₀ : VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    VerifiableInference.Desc.Sound.MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp) :=
  { 𝔇₀ with
    links := links, built := Zp.made.p.built.links, cs := cs Zp, N := N Zp cF
    G := F0T o Zp Np cF, arr := arr Zp, smp := smp Zp, ms := ms Zp lay
    decT := decT o Zp Np cF E hs, put := put, H := H o Zp Np cF E hs lay hL hN hG
    reqB := reqB, shape := shape Zp, layout := layout Zp
    lk := lk Zp, rw := rw Zp }

end Rec

variable {o Zp Np cF} {lay : ByteArray}

/-- **The structure of the composed meaning's letters, under the named tests.** -/
noncomputable def 𝔇Ok (ok : PlanOk o Zp Np cF lay) {pp : Inst.Model.ScalesAndPolicy}
    (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
      OnBytes.Flat.numsFull pp)) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR (X Zp) :=
  𝔇At o Zp Np cF E ok.shape lay ok.laid ok.hN ok.hG 𝔇₀

end P5J.At
