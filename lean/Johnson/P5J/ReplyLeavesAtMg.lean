-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/ReplyLeavesAtMg.lean: THE ROW reply_leaves (`FiveF`, Johnson/P5J/TowerEnd.lean) AT THE
VERIFIER'S OWN VALUE, UNDER THE ONE HEAD `AtMg` AT THE SECOND HASH FUNCTION, WITH ITS THREE DEBTS
PAID. A joining of two theorems.

  `reply_leaves_at_mg`: `reply_at_mg` (Johnson/P5J/ReplyAtMg.lean) at the H and the three facts that
    `reply_stones` (Johnson/P5J/ReplyStonesLaid.lean) gives from the head's own fields scope, reads
    and laid: `EachRep` … on 0 (h.row 𝔏), at any promise on.
Limits. At OnBytes.secondHashFunction alone. Whether the head `AtMg` can be met at the release's own files is
not shown (see `headMember_zFull`). The full size alone. Nothing on soundness. On hiding nothing.

-/
import Johnson.P5J.ReplyAtMg
import Johnson.P5J.ReplyStonesLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

set_option maxHeartbeats 4000000 in
/-- **reply_leaves AT THE VERIFIER's OWN VALUE.** -/
theorem reply_leaves_at_mg (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (on : ℕ → ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str → Prop) :
    EachRep At.tokOf fullLinks At.ps
      (fun a : (F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁ =>
        ((a.1, a.2) : ProofFile.InstPub × TS)) tokVOf
      (fun b => repHeard (fun s : TS => s) b.1) on 0 (h.row 𝔏) := by
  obtain ⟨H, R1, R2, R3⟩ := reply_stones h.scope h.reads h.laid
  exact reply_at_mg h 𝔏 q₁ q₂ q₃ R1 R2 R3 on

end P5J

#print axioms P5J.reply_leaves_at_mg
