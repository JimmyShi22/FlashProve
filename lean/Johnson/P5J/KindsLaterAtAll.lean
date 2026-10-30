-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/KindsLaterAtAll.lean: the two later chains' laws kind by kind
(Johnson/P5J/KindsLaterAtMg.lean) AT THE HEAD `AtMgA`: at the composed meaning's closed structure of
parameters h.𝔇 (Johnson/P5J/MgAtAll.lean), as Johnson/P5J/RowsAtAll.lean has the first chain's
kinds (`AtMgA.Kind`) and the five rows (`AtMgA.Five`). Names, and calls.

  `AtMgA.KindShared`, `AtMgA.KindLast`, `AtMgA.Three`: the shares and the three rows, at h.𝔇.
  `AtMgA.KindAll h 𝔏 depthReq K`: ONE LAW FOR EACH KIND: kind K's shares of all three chains.
  `AtMgA.five_of_kinds`, `AtMgA.five_of_all`: h.Five from h.Three and the shares;
  `AtMgA.kinds_of_five`: and back.
  `proofFileAt_at_all_kinds`: `proofFileAt_at_all` with its two premises on laws replaced by
    (∀ K, h.KindAll 𝔏 (depthZ Z) K) and h.Three 𝔏.

Limits. KindsLaterAtMg.lean's and RowsAtAll.lean's own: joinings; no law is paid; no member is
known; 𝔏 is a letter. No soundness follows. Nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsAtAll
import Johnson.P5J.KindsLaterAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- Kind K's share of the shared chain's laws, at the closed constant. -/
def AtMgA.KindShared (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (K : KindName) : Prop :=
  h.toAtMg.KindShared h.𝔇 𝔏 depthReq K

/-- Kind K's share of the last chain's laws, at the closed constant. -/
def AtMgA.KindLast (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (K : KindName) : Prop :=
  h.toAtMg.KindLast h.𝔇 𝔏 K

/-- The three rows that are left of the five, at the closed constant. -/
def AtMgA.Three (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  h.toAtMg.Three h.𝔇 𝔏

/-- **ONE LAW FOR EACH KIND, AT THE CLOSED CONSTANT: kind K's shares of all three chains.** -/
def AtMgA.KindAll (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (K : KindName) : Prop :=
  h.Kind 𝔏 K ∧ h.KindShared 𝔏 depthReq K ∧ h.KindLast 𝔏 K

/-- **h.Five, from h.Three and seven shares by name.** -/
theorem AtMgA.five_of_kinds (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (V : h.Three 𝔏)
    (s₀ : h.KindShared 𝔏 depthReq .frame) (s₁ : h.KindShared 𝔏 depthReq .K1)
    (s₁₂ : h.KindShared 𝔏 depthReq .K12) (s₁₄ : h.KindShared 𝔏 depthReq .K14)
    (t₀ : h.KindLast 𝔏 .frame) (t₁₂ : h.KindLast 𝔏 .K12) (t₁₄ : h.KindLast 𝔏 .K14) :
    h.Five 𝔏 depthReq :=
  h.toAtMg.five_of_kinds h.𝔇 𝔏 depthReq V s₀ s₁ s₁₂ s₁₄ t₀ t₁₂ t₁₄

/-- **h.Five, from h.Three and one premise for each kind.** -/
theorem AtMgA.five_of_all (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (V : h.Three 𝔏)
    (kinds : ∀ K, h.KindAll 𝔏 depthReq K) : h.Five 𝔏 depthReq :=
  h.five_of_kinds 𝔏 depthReq V (kinds .frame).2.1 (kinds .K1).2.1 (kinds .K12).2.1
    (kinds .K14).2.1 (kinds .frame).2.2 (kinds .K12).2.2 (kinds .K14).2.2

/-- **The cut loses nothing.** -/
theorem AtMgA.kinds_of_five (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (V : h.Five 𝔏 depthReq) :
    h.Three 𝔏 ∧ (∀ K, h.KindShared 𝔏 depthReq K) ∧ ∀ K, h.KindLast 𝔏 K :=
  h.toAtMg.kinds_of_five h.𝔇 𝔏 depthReq V

/-- **The proof file's share of ProofSound at Z, at the closed constant, from one law for each kind
and three rows.** -/
theorem proofFileAt_at_all_kinds (h : AtMgA o Z (dpZ Z) r Zp Np cF x)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (seat_proof_file : theProofRun (asDescriptionFiles Z) = ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord).run)
    (𝔏 : Free numsFull (dpZ Z) (F0T o Zp Np cF) At.Tok) (hr : 𝔏.rP = recZ Z)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (kinds : ∀ K, h.KindAll 𝔏 (depthZ Z) K) (V : h.Three 𝔏)
    (d : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (EAll ((dpZ Z).at frS.P.T.a) (allOf ((dpZ Z).at frS.P.T.a))).Str) :
    ProofFileAt Z :=
  proofFileAt_at_all h hl seat_proof_file 𝔏 hr q₁ q₂ q₃ (fun K => (kinds K).1)
    (h.five_of_all 𝔏 (depthZ Z) V kinds) d

end P5J

#print axioms P5J.AtMgA.five_of_kinds
#print axioms P5J.AtMgA.five_of_all
#print axioms P5J.AtMgA.kinds_of_five
#print axioms P5J.proofFileAt_at_all_kinds
