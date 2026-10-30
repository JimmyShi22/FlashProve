-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ProofFileAtNameA.lean: `ProofFileAt Z` FROM THE TOP STATEMENTS' OWN THREE PREMISES ON Z,
    ONE NAMED CONDITION ON THE HEAD, AND WHAT IS OWED AT THE CLOSED CONSTANT: `proofFileAt_at_all`
    (RowsAtAll.lean) at `headA_at_name` (AtNameA.lean). NO LETTER 𝔇₀.
  `OwedAll h`: WHAT IS OWED UNDER A HEAD h : AtMgA secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np
      cF x: there is a filling 𝔏 of the tower's free letters with: 𝔏.rP is recZ Z · the three lists'
      heads · a statement d (any) · ∀ K, h.Kind 𝔏 K · h.Five 𝔏 (depthZ Z).
  **`proofFileAt_of_owedA`**: in scope · `protocolDataWellFormed` accepts · the files are read · At.Conds Z · (∀ Zp
      Np cF x h, OwedAll h) ⟹ ProofFileAt Z.
Limits. A JOINING: IT PAYS NO LAW. No member of OwedAll is known. "There is 𝔏" lets the payer lay
    the two later tables' letters: meant: the closed 𝔏₀ (`AtMgA.free`, FreeAll.lean). What
    ProofFileAt Z is worth is fixed by its own text, not by 𝔏. Whether At.Conds Z holds at the
release's own files is a run's matter. The full size alone. No soundness follows.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsAtAll
import Johnson.P5J.AtNameA

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

variable {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **What is owed under a head at the name, at the closed constant.** -/
def OwedAll (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x) : Prop :=
  ∃ (𝔏 : Free numsFull (dpZ Z) (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (_ : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll ((dpZ Z).at frS.P.T.a) (allOf ((dpZ Z).at frS.P.T.a))).Str),
    𝔏.rP = recZ Z ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁ ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂ ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃ ∧
    (∀ K, h.Kind 𝔏 K) ∧ h.Five 𝔏 (depthZ Z)

/-- **THE PROOF FILE's SHARE OF ProofSound AT Z, FROM WHAT IS OWED AT THE CLOSED CONSTANT.** -/
theorem proofFileAt_of_owedA (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) {pp : Inst.Model.ScalesAndPolicy} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (C : At.Conds Z)
    (owed : ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x), OwedAll h) :
    ProofFileAt Z := by
  obtain ⟨Zp, Np, cF, x, h⟩ := headA_at_name hZ hl hR C
  obtain ⟨𝔏, d, hr, q₁, q₂, q₃, kinds, V⟩ := owed Zp Np cF x h
  exact proofFileAt_at_all h hl h.laid.run 𝔏 hr q₁ q₂ q₃ kinds V d

end P5J

#print axioms P5J.proofFileAt_of_owedA
