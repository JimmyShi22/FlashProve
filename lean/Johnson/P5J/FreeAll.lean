-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FreeAll.lean: **THE TOWER'S END CALLED AT THE TWO CLOSED VALUES**: the composed meaning's
closed constant (`AtMgA`, h.𝔇) and the tower's free letters at `AtMg.free`
(FreeAt.lean).
  `AtMgA.free`          h.toAtMg.free h.𝔇: no letter is left but the head's (Zp Np cF x, which
                        "laid" opens).
  **`owedAll_of_free`** what `proofFileAt_of_owedA` (ProofFileAtNameA.lean) asks, `OwedAll h`, from
                        the kinds' shares and the five rows AT THE VALUE: its "there is 𝔏" is met by
                        h.free; the four equations on 𝔏 are paid here.
  `proofFileAt_at_free` `proofFileAt_at_all` at the value.
d: the default statement (the plain form's last letter; nothing is asked of it): `AtMg.dIdle`.
Limits. CALLS: no law is paid: no member of h.Kind or h.Five at the value is known. No soundness
follows. Nothing on hiding. It holds no coding theory.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FreeAt
import Johnson.P5J.ProofFileAtNameA

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

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
open Desc.K14.Law.Fence (numbersSh)
open Desc.K14.Law (ShPlan ShOpen Sh.planAt Sh.openAt Sh.Open₁ Sh.nums Sh.mg Sh.pm Sh.own Sh.ex)

open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE VALUE AT THE CLOSED CONSTANT.** -/
def AtMgA.free (h : AtMgA o Z D r Zp Np cF x) : Free numsFull D (F0T o Zp Np cF) At.Tok :=
  h.toAtMg.free h.𝔇

theorem AtMgA.free_rP (h : AtMgA o Z D r Zp Np cF x) : h.free.rP = recZ Z := rfl
theorem AtMgA.free_q₁ (h : AtMgA o Z D r Zp Np cF x) :
    (F0T o Zp Np cF).first.blocksInOrder = h.free.c₁ :: h.free.k₁ := P5J.free_q₁ h.toAtMg h.𝔇
theorem AtMgA.free_q₂ (h : AtMgA o Z D r Zp Np cF x) :
    (F0T o Zp Np cF).shared.blocksInOrder = h.free.c₂ :: h.free.k₂ := P5J.free_q₂ h.toAtMg h.𝔇
theorem AtMgA.free_q₃ (h : AtMgA o Z D r Zp Np cF x) :
    (F0T o Zp Np cF).second.blocksInOrder = h.free.c₃ :: h.free.k₃ := P5J.free_q₃ h.toAtMg h.𝔇
theorem AtMgA.free_split (h : AtMgA o Z D r Zp Np cF x) : h.free.split = true := rfl
theorem AtMgA.free_pm (h : AtMgA o Z D r Zp Np cF x) :
    h.free.Pm = Sh.pm h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇) := rfl

/-- **WHAT THE TOWER's END ASKS, FROM THE KINDS' SHARES AND THE FIVE ROWS AT THE VALUE.** -/
theorem owedAll_of_free
    (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x)
    (kinds : ∀ K, h.Kind h.free K) (V : h.Five h.free (depthZ Z)) : OwedAll h :=
  ⟨h.free, h.toAtMg.dIdle, rfl, free_q₁ h.toAtMg h.𝔇, free_q₂ h.toAtMg h.𝔇, free_q₃ h.toAtMg h.𝔇, kinds, V⟩

/-- **THE PROOF FILE's SHARE OF ProofSound AT Z, AT THE TWO CLOSED VALUES.** -/
theorem proofFileAt_at_free (h : AtMgA o Z (dpZ Z) r Zp Np cF x)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (seat_proof_file : theProofRun (asDescriptionFiles Z) = ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord).run)
    (kinds : ∀ K, h.Kind h.free K) (V : h.Five h.free (depthZ Z)) :
    ProofFileAt Z :=
  proofFileAt_at_all h hl seat_proof_file h.free rfl (free_q₁ h.toAtMg h.𝔇) (free_q₂ h.toAtMg h.𝔇)
    (free_q₃ h.toAtMg h.𝔇) kinds V h.toAtMg.dIdle

end P5J

#print axioms P5J.AtMgA.free_rP
#print axioms P5J.AtMgA.free_q₁
#print axioms P5J.AtMgA.free_q₂
#print axioms P5J.AtMgA.free_q₃
#print axioms P5J.AtMgA.free_split
#print axioms P5J.AtMgA.free_pm
#print axioms P5J.owedAll_of_free
#print axioms P5J.proofFileAt_at_free
