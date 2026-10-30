-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/MgAtConst.lean: THE CONSTANT mgAt UNDER THE ONE HEAD (Johnson/P5J/AtMg.lean); AND THE FACTS ON A START FROM THE ONE HEAD ALONE. Two definitions, two theorems.
  AtMg.𝔇 h 𝔇₀ · mgAt h 𝔇₀ := mgAll (h.𝔇 𝔇₀) mgBase. THE CODING IS THE GOALS' OWN: At.EAt Z := FlashProve.theCoding (asDescriptionFiles Z) (Johnson/P5J/DecFree.lean: the one decoder reads neither the coding nor the model's public parameters: decT_is). THE ONE LETTER LEFT IN mgAt: 𝔇₀ (the fields that are not laid).
  mgAt_is_tower: under headLink (At.X Zp) = 24: mgAt h 𝔇₀ = meaningQ At.put (oneDec decT H) headPart digitsPart (meaningSig cs G arr smp ms decT (withReq reqB (mgLetter …))): AT THE CLOSED LETTERS, WRITTEN OUT.
  AtMg.tieStart: TieStart (eleven of the proof file's rows) at mgAt's letter, from AtMg alone: nine as in Johnson/P5J/TieAtStart.lean; scope_reads := reads · scope_public := pubOne.
Limits. One call. The full size alone. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT
secondHashFunction; SIDE LIBRARY AtFullSide/Top/). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtMg
import Johnson.P5J.TieAtStart
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound (MgData mgAll mgBase mgLetter MsgT)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The structure of the composed meaning's letters, under the one head. -/
noncomputable def AtMg.𝔇 (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR
      (At.X Zp)) :
    MgData ProofFile.Inst ProofFile.InstPub At.Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR (At.X Zp) :=
  At.𝔇Ok h.plan (At.EAt Z) 𝔇₀

/-- **THE CONSTANT.** -/
noncomputable def mgAt (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR
      (At.X Zp)) :
    VerifiableInference.Desc.First.Meaning ProofFile.InstPub (Wit (CellsM OnBytes.Flat.numsFull) At.Tok MsgT) :=
  mgAll (h.𝔇 𝔇₀) mgBase

/-- **The constant is the meaning at which the tops' laws are stated**, where the head's segment's number is 24: mgAll_is_tower (Johnson/Desc/Sound/MgAll.lean) at the constant's letters. -/
theorem mgAt_is_tower (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR
      (At.X Zp)) (hH : VerifiableInference.OnPublicFiles.headLink (At.X Zp) = 24) :
    mgAt h 𝔇₀ =
      meaningQ At.put
        (VerifiableInference.Desc.Sound.oneDec (At.decT o Zp Np cF (At.EAt Z) h.plan.shape) (h.𝔇 𝔇₀).H)
        𝔇₀.headPart 𝔇₀.digitsPart
        (VerifiableInference.Desc.Sound.meaningSig (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp)
          (At.ms Zp Z.lay) (At.decT o Zp Np cF (At.EAt Z) h.plan.shape)
          (withReq At.reqB (mgLetter (h.𝔇 𝔇₀) mgBase))) :=
  VerifiableInference.Desc.Sound.mgAll_is_tower (h.𝔇 𝔇₀) mgBase hH

/-- **THE FACTS ON A START, ALL ELEVEN, FROM THE ONE HEAD.** -/
theorem AtMg.tieStart (h : AtMg o Z D r Zp Np cF) (DP : WholeD) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR
      (At.X Zp)) :
    TieStart (Z := Z) (lay := some Z.lay) (X := At.X Zp) OnBytes.Flat.numsFull (At.EAt Z) DP
      (F0T o Zp Np cF) LPFD.Full.instanceAsPlainRecord (fun s => s) (fun q : ProofFile.InstPub => q.request)
      (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) ProofFile.Inst.asked (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay)
      (At.N Zp cF) (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps (F0T o Zp Np cF) (At.smp Zp)
      Zp.made.p.chains.proof.first.codes (fun p : ProofFile.InstPub => OnBytes.Model.Verify.words32 p.request) :=
  tieStart_at_start (At.EAt Z) DP o Zp Np cF h.plan.shape h.laid.pub h.plan.laid
    h.plan.hN h.plan.hG 𝔇₀ mgBase rfl (fun _ => ⟨rfl, rfl⟩) rfl h.reads h.pubOne

end P5J

#print axioms P5J.mgAt_is_tower
#print axioms P5J.AtMg.tieStart
