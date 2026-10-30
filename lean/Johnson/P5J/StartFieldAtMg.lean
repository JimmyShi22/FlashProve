-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/StartFieldAtMg.lean: The field start of `P5J.TablesFitR`, at the letters at which
`P5J.AtMg.Five` (Johnson/P5J/RowsAtMg.lean) asks `tables_fit`. One theorem and one example that checks its type.

  `AtMg.start_field`: `start_field_at_term` (Johnson/P5J/StartFieldAtTerm.lean) at the first meaning as
    the tower spells it (`h.mq 𝔇₀`) and at the tower's free letter `𝔏.MgS`.
  The example at the foot: it is laid into the field start of the very `tables_fit` that `h.Five`
    asks: so that it has the field's type there is checked by Lean, not by a comparison of texts.

Limits. That file's. The head `h` is used only to name `h.mq`: no fact of it is spent.

-/
import Johnson.P5J.StartFieldAtTerm
import Johnson.P5J.RowsAtMg

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
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_zero rchAt_hand block_at piece_step)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The field START at the letters at which `AtMg.Five` asks `tables_fit`.** -/
theorem AtMg.start_field (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) :
    ∀ (p : (F0T o Zp Np cF).XiPub) (s₁ : (F0T o Zp Np cF).S₁) (s₂ : (F0T o Zp Np cF).S₂)
      (s : (F0T o Zp Np cF).S₃),
      (fun p a b => ((F0T o Zp Np cF).start₃ p a b).toOption) p s₁ s₂ = some s →
      (VerifiableInference.Desc.Sound.tiedMeaning
        (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
          ((a.1, (fun s => s) a.2) : (F0T o Zp Np cF).XiPub × TS)) (h.mq 𝔇₀) 𝔏.MgS).unmarked1
        (p, s₁) :=
  start_field_at_term o Zp Np cF (h.mq 𝔇₀) 𝔏.MgS

/-- An example that checks the type; it says nothing by itself (its end is its premise):
`AtMg.start_field` is accepted as the field START of the very `tables_fit` that `h.Five` asks. -/
example (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (depthReq : ℕ) (t : h.Five 𝔇₀ 𝔏 depthReq) :
    h.Five 𝔇₀ 𝔏 depthReq :=
  FiveF.mk t.head_cuts t.reply_leaves t.shared_joint_count t.leads3_last_chains_table
    { t.tables_fit with START := h.start_field 𝔇₀ 𝔏 }

end P5J

#print axioms P5J.AtMg.start_field
