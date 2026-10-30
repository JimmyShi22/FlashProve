-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09Len.lean: «NO FEWER PIECES THAN PLACES» (the conjunct `len` of the batching kind's
condition; the premise hlen of `k09_kind_of_laws` and `k09_kind_of_list`) IS A FACT FROM THE HEAD,
at the second hash function, under the tower's own three equations on the flat lists' heads: no
test, nothing to evaluate. Kind-free. Theorems.

What is said.
  `AtMg.row_length`: **the seated row has as many pieces as the seated description's first flat list
    has sub-protocols** (at every hash). `row_358`: **at the second hash function: 358**, by
    `flat_358`. `list_hlen`: **so `At.ps.length ≤ (h.row 𝔏).length`.**

Limits. Calls of `AtMg.ofDesc` (its field on the pieces' sub-protocols, counted) and
of `IM.flat_358` (in scope, at the opened seat). Nothing on soundness.

-/
import Johnson.P5J.K09Kind
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start flatPlacesOf)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **AS MANY PIECES AS SUB-PROTOCOLS.** -/
theorem AtMg.row_length (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    (h.row 𝔏).length = (F0T o Zp Np cF).first.blocksInOrder.length := by
  have e := congrArg List.length (h.ofDesc 𝔏 q₁ q₂ q₃).b₁
  simp only [List.length_map] at e
  exact e

set_option maxRecDepth 1000000 in
theorem ps_358 : At.ps.length = 358 := by decide +kernel

/-- **AT THE SECOND HASH FUNCTION: 358.** -/
theorem row_358 (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    (h.row 𝔏).length = 358 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact (h.row_length 𝔏 q₁ q₂ q₃).trans (Meaning.K2.flat_358 h.scope O)

/-- **SO: NO FEWER PIECES THAN PLACES.** -/
theorem list_hlen (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    At.ps.length ≤ (h.row 𝔏).length := by
  rw [row_358 h 𝔏 q₁ q₂ q₃, ps_358]

end P5J

#print axioms P5J.AtMg.row_length
#print axioms P5J.ps_358
#print axioms P5J.row_358
#print axioms P5J.list_hlen
