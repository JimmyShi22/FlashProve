-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LeftOfParts.lean: `h.ThreeLeft 𝔇₀ 𝔏` FROM ITS SEVEN PARTS, EACH NAMED.
One abbreviation, one theorem.

Why. `AtMg.ThreeLeft` (Johnson/P5J/ThreeLeft.lean) holds seven fields: head_cuts, and TP, PW, SH₃,
POf, POb, stepQ of tables_left. Two of them have a form at the tower's letters, for every 𝔏:
SH₃ (`AtMg.sh3_field`, Johnson/P5J/Sh3AtMg.lean) and stepQ (`AtMg.stepQ_field`,
Johnson/P5J/StepQAtMg.lean).
The other five have payers only where 𝔏 is laid at the tables' constants.
This file joins the seven for every 𝔏, so that at a laid 𝔏 one call is left.

  `fieldAt f`: the proposition in which the projection f ends. It names a field's type and copies no
    text. (Kin to the device `fieldOf` of Johnson/Desc/K14/Law/LedgerAtFree.lean.)
  **`AtMg.left_of_parts`**: head_cuts, TP, PW, POf, POb (each as `fieldAt` of its own projection),
    h.Sh3Owed 𝔇₀ 𝔏, and 𝔏.Q₂ = h.stepOf 𝔇₀ 𝔏 ext give h.ThreeLeft 𝔇₀ 𝔏.
    General in the second hash function, in 𝔇₀ and in 𝔏.

Limits. A joining: it pays no field. No member is known. No soundness follows from it.
Nothing on hiding.

-/
import Johnson.P5J.StepQAtMg
import Johnson.P5J.Sh3AtMg

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

open VerifierAndGoals.AtTheName
open VerifiableInference.Desc (Chain KindName)

/-- The proposition in which a projection ends. -/
abbrev fieldAt {A B : Prop} (_ : A → B) : Prop := B

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **`h.ThreeLeft 𝔇₀ 𝔏` from its seven parts.** -/
theorem AtMg.left_of_parts (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (head_cuts : fieldAt fun V : h.ThreeLeft 𝔇₀ 𝔏 => ThreeLeftF.head_cuts V)
    (TP : fieldAt fun V : h.ThreeLeft 𝔇₀ 𝔏 => (ThreeLeftF.tables_left V).TP)
    (PW : fieldAt fun V : h.ThreeLeft 𝔇₀ 𝔏 => (ThreeLeftF.tables_left V).PW)
    (POf : fieldAt fun V : h.ThreeLeft 𝔇₀ 𝔏 => (ThreeLeftF.tables_left V).POf)
    (POb : fieldAt fun V : h.ThreeLeft 𝔇₀ 𝔏 => (ThreeLeftF.tables_left V).POb)
    (S : h.Sh3Owed 𝔇₀ 𝔏)
    (ext : ℕ → (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) ×
        (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str →
      Wit (CellsM numsFull) At.Tok MsgT → Wit (CellsM numsFull) At.Tok MsgT)
    (hQ : 𝔏.Q₂ = h.stepOf 𝔇₀ 𝔏 ext) : h.ThreeLeft 𝔇₀ 𝔏 :=
  ThreeLeftF.mk head_cuts
    ⟨TP, PW, h.sh3_field 𝔇₀ 𝔏 S, POf, POb, h.stepQ_field 𝔇₀ 𝔏 ext hQ⟩

end P5J

#print axioms P5J.AtMg.left_of_parts
