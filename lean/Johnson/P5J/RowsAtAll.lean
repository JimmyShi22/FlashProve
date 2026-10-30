-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/RowsAtAll.lean: THE COUNTED FIELDS AT THE CLOSED CONSTANT: NO LETTER 𝔇₀ IS LEFT. Under
    the head `AtMgA` (MgAtAll.lean: AtMg, with what is handed in) the composed meaning is
    ONE TERM: mgAtAll h := mgAll h.𝔇 mgBase, all 29 parameters laid.
Why: `AtMg.Kind h 𝔇₀ 𝔏 K` lays some parameters over 𝔇₀ (`AtMg.𝔇`) and leaves the others as
    𝔇₀ has them: a hypothesis "for all 𝔇₀" would be too wide to be met.
  **`AtMgA.Kind h 𝔏 K`** := KindTiedR (At.N Zp cF) (mgAtAll h) fullLinks At.ps h.rch (h.ex 𝔏) (h.row
      𝔏) K: THE FORM IN WHICH A KIND's LAW IS COUNTED: at the closed meaning; with "reached" and
      "the public part is a typed instance's" in hand.
  `AtMgA.kind_is`: it is `AtMg.KindR` at 𝔇₀ := h.𝔇: rfl. `AtMgA.kind_of_reached`: a law at bare
      RchAt gives it.
  `AtMgA.Five h 𝔏 depthReq`: the five rows that are laws beside the kinds', at 𝔇₀ := h.𝔇.
  **`proofFileAt_at_all`**: AtMgA at D := dpZ Z · protocolDataWellFormed · the seated term's run · 𝔏.rP = recZ Z ·
      the three lists' heads · (∀ K, h.Kind 𝔏 K) · h.Five 𝔏 (depthZ Z) ⟹ ProofFileAt Z.
WHICH LETTERS OF 𝔏 ARE "FOR ALL" BY RIGHT, AND WHICH MUST BE LAID FOR A LAW TO BE TRUE [by reading
    the definitions]. In h.Kind 𝔏 K only h.ex 𝔏 and h.row 𝔏 read 𝔏: c₀ (a default of the table's
    extractor) · c₁ k₁ … k₃ (pinned by the heads' equations) · e₁ e₂ e₃ · dW · wEnd (the
pieces' own extractors and two default witnesses; the table's extractor is laid over e₁): a kind's
    law is meant at ALL of these. h.Five reads Q₀ · Ns · MgS · ML · Pm · PLm · split · Q₂ as well:
    THESE MUST BE LAID AT THE TWO LATER TABLES' CONSTANTS for its rows to be true:
FreeShared.lean and FreeAt.lean lay them (𝔏₀). rP is pinned to recZ Z at the name.
Limits. A JOINING: IT PAYS NO LAW. No member of h.Kind or h.Five is known; whether AtMgA can be met
    at the release's own files is not shown in Lean. The full size alone. No soundness follows.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.ProofFileAtMg
import Johnson.P5J.MgAtAll

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
open Johnson.Desc.First.Walk.Tied (RchAt)
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **KIND K's SHARE AT THE CLOSED CONSTANT: THE FORM IN WHICH A KIND's LAW IS COUNTED.** -/
def AtMgA.Kind (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (K : KindName) : Prop :=
  KindTiedR (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
    (At.N Zp cF) (mgAtAll h) fullLinks At.ps h.toAtMg.rch (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏) K

/-- It is the share with the rider in hand, at the closed structure of parameters. -/
theorem AtMgA.kind_is (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (K : KindName) : h.Kind 𝔏 K = h.toAtMg.KindR h.𝔇 𝔏 K := rfl

/-- A law at bare "reached" gives it. -/
theorem AtMgA.kind_of_reached (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (K : KindName)
    (k : KindTiedR (At.N Zp cF) (mgAtAll h) fullLinks At.ps (RchAt (F0T o Zp Np cF))
      (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏) K) : h.Kind 𝔏 K :=
  KindTiedR.mono (fun _ _ h' => h'.1) k

/-- The five rows that are laws beside the kinds', at the closed constant. -/
def AtMgA.Five (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (depthReq : ℕ) : Prop :=
  h.toAtMg.Five h.𝔇 𝔏 depthReq

set_option maxHeartbeats 8000000 in
/-- **THE PROOF FILE's SHARE OF ProofSound AT Z, AT THE CLOSED CONSTANT.** -/
theorem proofFileAt_at_all (h : AtMgA o Z (dpZ Z) r Zp Np cF x) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (seat_proof_file : theProofRun (asDescriptionFiles Z) = ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord).run)
    (𝔏 : Free numsFull (dpZ Z) (F0T o Zp Np cF) At.Tok) (hr : 𝔏.rP = recZ Z)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (kinds : ∀ K, h.Kind 𝔏 K) (V : h.Five 𝔏 (depthZ Z))
    (d : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (EAll ((dpZ Z).at frS.P.T.a) (allOf ((dpZ Z).at frS.P.T.a))).Str) :
    ProofFileAt Z :=
  proofFileAt_at_mg h.toAtMg hl seat_proof_file h.𝔇 𝔏 hr q₁ q₂ q₃ kinds V d

end P5J

#print axioms P5J.AtMgA.kind_is
#print axioms P5J.AtMgA.kind_of_reached
#print axioms P5J.proofFileAt_at_all
