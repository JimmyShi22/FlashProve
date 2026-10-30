-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReplyAtMg.lean: THE ROW reply_leaves (one of the five rows that are laws beside the
    kinds' shares: `FiveF`, TowerEnd.lean) AT THE VERIFIER'S OWN VALUE, CUT INTO ITS THREE DEBTS.
    Under the one head `AtMg`.
  **`reply_at_mg`**: AtMg → the three lists' heads → (R1) (R2) (R3) → `EachRep` At.tokOf fullLinks
      At.ps … tokVOf (the state's own reader of the heard reply) on 0 (h.row 𝔏), AT ANY
    PROMISE on: so at the one at which `FiveF.reply_leaves` asks it. By `eachRep_of_desc`
        (ReplyAtDriver.lean); paid inside: the pieces hold the lists' sub-protocols (`AtMg.ofDesc`)
        · on the
    table "the row lays the token" is "the kind is K7" (`lays_full`, by the kernel) · the table's
        extractor's token is the reply heard (`htok_nat`).
  THE THREE DEBTS, for some H : First.Blocks TS ProofFile.Cl:
    (R1) First.firstChain H fullLinks true = some cF: the seated term's first chain IS the driver's
        at H.
    (R2) ∀ t s, H.same t s = true → the heard reply of s is that of t: what the seat's guard lets
        pass leaves the reading.
    (R3) ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce …: the sub-protocol at K7's place
        hears once: nothing heard in front, something behind.
Limits. A joining: it pays none of the three. Whether an H with (R1) exists at the laid value is not
    shown here. The full size alone.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsAtMg
import Johnson.P5J.ReplyAtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

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

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

set_option maxHeartbeats 4000000 in
/-- **reply_leaves AT THE VERIFIER's OWN VALUE, FROM ITS THREE DEBTS.** -/
theorem reply_at_mg (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {H : VerifiableInference.Desc.First.Blocks TS ProofFile.Cl}
    (R1 : VerifiableInference.Desc.First.firstChain H fullLinks true = some cF)
    (R2 : ∀ t s, H.same t s = true → heardV (fun s : TS => s) s = heardV (fun s : TS => s) t)
    (R3 : ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce (heardV fun s : TS => s))
    (on : ℕ → ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str → Prop) :
    EachRep At.tokOf fullLinks At.ps
      (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ => ((a.1, a.2) : ProofFile.InstPub × TS))
          tokVOf
      (fun b => repHeard (fun s : TS => s) b.1) on 0 (h.row 𝔏) :=
  eachRep_of_desc (F0T o Zp Np cF) (piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁
      𝔏.c₂ 𝔏.k₂
      𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd) (h.ofDesc 𝔏 q₁ q₂ q₃) (fun
          s : TS => s) At.tokOf tokVOf fullLinks true on R1 R2 R3 lays_full
    (fun t x hx => htok_nat (fun s : TS => s) t x hx)

end P5J

#print axioms P5J.reply_at_mg
