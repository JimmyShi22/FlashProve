-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ThreeLeftAtAll.lean: Johnson/P5J/ThreeLeft.lean AT THE CLOSED CONSTANT: `AtMgA.Three h
    𝔏`
(Johnson/P5J/KindsLaterAtAll.lean) from what is left of it. One definition, two theorems, each one
    call of
that file's. General in 𝔏: at a named 𝔏 (the tower's letters laid at the tables' constants) it is
    called
with that 𝔏.

  `AtMgA.ThreeLeft h 𝔏` := h.toAtMg.ThreeLeft h.𝔇 𝔏.
  **`AtMgA.three_of_left`**: what is left gives `AtMgA.Three h 𝔏`.
  `AtMgA.left_of_three`: the way back: `ThreeLeft` asks nothing that `Three` did not ask.

Limits. That file's.

-/
import Johnson.P5J.ThreeLeft
import Johnson.P5J.KindsLaterAtAll

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
open Desc.K14 (p14Of beforePointOf first)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- What is left of `AtMgA.Three`, at the closed constant. -/
def AtMgA.ThreeLeft (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  h.toAtMg.ThreeLeft h.𝔇 𝔏

/-- **`AtMgA.Three` from what is left of it.** -/
theorem AtMgA.three_of_left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (hk : ∀ z : LPFD.Full.XF × RecFull, 𝔏.Pm.shape 0
      (first (p14Of Zp.p.chains (beforePointOf Np)).codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hsp : 𝔏.split = true)
    (V : h.ThreeLeft 𝔏) : h.Three 𝔏 :=
  h.toAtMg.three_of_left h.𝔇 𝔏 hk q₁ q₂ q₃ hsp V

/-- `AtMgA.ThreeLeft` asks nothing that `AtMgA.Three` did not ask. -/
theorem AtMgA.left_of_three (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (V : h.Three 𝔏) : h.ThreeLeft 𝔏 :=
  h.toAtMg.left_of_three h.𝔇 𝔏 V

end P5J

#print axioms P5J.AtMgA.three_of_left
#print axioms P5J.AtMgA.left_of_three
