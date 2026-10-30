-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ProofFileAtMg.lean: `ProofFileAt Z` (Johnson/Goal/Skeleton/ProofFile.lean: the proof
    file's share of the top statement ProofSound, at the public files Z) FROM THE KINDS' SHARES AND
    FIVE ROWS, UNDER THE ONE HEAD: `rows_at_mg` (RowsAtMg.lean) joined
to `proofFileAt_of_rows` (Johnson/Goal/Skeleton/ProofAtNameRows.lean).
  **`proofFileAt_at_mg`**: AtMg o Z (dpZ Z) r Zp Np cF · `protocolDataWellFormed` accepts at Z · `theProofRun
      (asDescriptionFiles Z)` is the seated term's run on the requests · the three lists' heads · 𝔏.rP is
      recZ Z (the second part of the fixed instance z₀ of `dataAtFiles flashProveData Z`) ·
    (∀ K, h.KindR 𝔇₀ 𝔏 K) · h.Five 𝔇₀ 𝔏 (depthZ Z) ⟹
        ProofFileAt Z.
  What Lean takes by unfolding: numsFull for numsRef · the top statements' own coding At.EAt Z for
      the coding of `dataAtFiles flashProveData Z` · its claims.
Limits. A JOINING: IT PAYS NO LAW: no member of h.Kind or h.Five is known; whether AtMg can be met
    at the release's own files, AT THE DATA dpZ Z, is not shown here; while theProofRun is a
    placeholder its equation is not expected to
hold, and the theorem then says nothing (ProofAtNameRows.lean's own limit).
(Where this and lean/THEOREM.md differ, the page
holds.) 𝔇₀ and 𝔏 are letters. The full
    size alone. No soundness follows.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsAtMg
import Johnson.Goal.Skeleton.ProofAtNameTied

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

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

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

set_option maxHeartbeats 8000000 in
/-- **THE PROOF FILE's SHARE OF ProofSound AT Z, FROM THE KINDS' SHARES AND FIVE ROWS.** -/
theorem proofFileAt_at_mg (h : AtMg o Z (dpZ Z) r Zp Np cF) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (seat_proof_file : theProofRun (asDescriptionFiles Z) = ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord).run) {nR :
                                  ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull (dpZ Z) (F0T o Zp Np cF) At.Tok) (hr : 𝔏.rP = recZ Z)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (kinds : ∀ K, h.KindR 𝔇₀ 𝔏 K) (V : h.Five 𝔇₀ 𝔏 (depthZ Z))
    (d : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (EAll ((dpZ Z).at frS.P.T.a) (allOf ((dpZ Z).at frS.P.T.a))).Str) :
    ProofFileAt Z :=
  proofFileAt_of_rows Z hl (F0T o Zp Np cF) LPFD.Full.instanceAsPlainRecord seat_proof_file fun early he P Tl => by
    subst he
    obtain ⟨Q₀, c₀, Ns, MgS, ML, Pm, PLm, split, Q₂, rP, c₁, k₁, c₂, k₂, c₃, k₃, e₁, e₂, e₃, dW,
        wEnd⟩ := 𝔏
    subst hr
    obtain ⟨h₁, h₂, h₃, R'⟩ := rows_at_mg h 𝔇₀ _ (depthZ Z) q₁ q₂ q₃ kinds V d hl
      (runP_the_at Z _ seat_proof_file) Tl
    exact ⟨_, R'⟩

end P5J

#print axioms P5J.proofFileAt_at_mg
