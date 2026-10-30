-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/RchAtMg.lean: THE TOWER'S CONDITION BESIDE THE FIRST TABLE'S PROMISE GIVES "REACHED" IN
    THE LETTERS IN WHICH THE FACTS ALONG THE FOLD ARE PAID: the one premise hRch of the kinds'
    ‹name›_field lemmas, at Rch := h.rch and at_ := fun a => a.1.
  **`AtMg.rch_is_reach`**: h.rch k a → Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1: the first
      half of h.rch, by unfolding the seated term (its first chain is cF; its first start is
      ProofFile.startS Zp).
  `AtMg.rch_typed`: h.rch k a → ∃ z, a.1.1 = (instanceAsPlainRecord z).pub: the second half.
  `AtMg.rc_is_rch` · `AtMg.rc_reached`: h.rc p gives h.rch at the number of the first
      chain's sub-protocols, at any strings: the premise hE of `five_at_end`
      (Johnson/Desc/Sound/RcOfFold.lean [not in this library]).
Limits. Projections and unfoldings.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FourAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

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
open VerifiableInference.Desc (Chain)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **"Reached" in the letters of the facts along the fold.** -/
theorem AtMg.rch_is_reach (h : AtMg o Z D r Zp Np cF) (k : ℕ)
    (a : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch k a) :
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1 := hr.1

/-- The rider. -/
theorem AtMg.rch_typed (h : AtMg o Z D r Zp Np cF) (k : ℕ)
    (a : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch k a) :
    ∃ z : LPFD.Full.XF × RecFull, a.1.1 = (LPFD.Full.instanceAsPlainRecord z).pub := hr.2

/-- **What goes on to the two later tables is the condition at the first chain's last border**, at
    any strings y. -/
theorem AtMg.rc_is_rch (h : AtMg o Z D r Zp Np cF)
    (y : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (p : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) (hp : h.rc p) :
    h.rch (F0T o Zp Np cF).first.blocksInOrder.length (p, y) := ⟨hp.1, hp.2⟩

/-- In the form in which `five_at_end` takes it (its premise hE), at at_ := fun a =>
    a.1 and get := fun p => p. (That `five_at_end`: Johnson/Desc/Sound/RcOfFold.lean.) -/
theorem AtMg.rc_reached (h : AtMg o Z D r Zp Np cF)
    (y : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (q : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) (hq : h.rc q) :
    ∃ (k : ℕ) (a : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str), h.rch k a ∧ a.1.2 = q.2 :=
  ⟨_, (q, y), h.rc_is_rch y q hq, rfl⟩

end P5J

#print axioms P5J.AtMg.rch_is_reach
#print axioms P5J.AtMg.rch_typed
#print axioms P5J.AtMg.rc_is_rch
#print axioms P5J.AtMg.rc_reached
