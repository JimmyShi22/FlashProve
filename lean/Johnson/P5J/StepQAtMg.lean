-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/StepQAtMg.lean: THE FIELD stepQ OF `tables_fit` AT THE TOWER's LETTERS, FOR ONE EQUATION
ON 𝔏.Q₂. One definition, one theorem, two examples.

Why. `stepQ_tablesR` (Johnson/Desc/Sound/GlueAtLedgerStep/SharedAtTablesR.lean) has the field stepQ of
`TablesFitR` (Johnson/P5J/TopTablesR.lean) with no premise, at general letters, where the letter Q₂
is the shared table's own step `stepAt`. At the tower Q₂ is 𝔏.Q₂, a letter.
So one equation is wanted.

  `AtMg.stepOf h 𝔇₀ 𝔏 ext`: the shared table's own step at the tower's letters; ext: any extractor.
  **`AtMg.stepQ_field`**: 𝔏.Q₂ = h.stepOf 𝔇₀ 𝔏 ext gives the field stepQ, in its own text, at the
    letters at which `AtMg.Three` and `AtMg.ThreeLeft` ask it.
    General in the second hash function, in 𝔇₀ and in 𝔏.
  The two examples lay it into `h.Three 𝔇₀ 𝔏` (Johnson/P5J/KindsLaterAtMg.lean) and into
    `h.ThreeLeft 𝔇₀ 𝔏` (Johnson/P5J/ThreeLeft.lean): so that it fits is Lean's word.

What it is worth. By its definition (Johnson/Desc/Sound/SharedJointCountRowB.lean) `stepAt … k a b`
is the shared table's promise of b at border k + 1, and: every witness of the relation of b at k + 1
goes, by ext, to one of a at k.
The field's conclusion is a weakening of just that: its first half as it stands, its second half
with ext's witness.
So at this Q₂ the field costs nothing and says nothing.
The weight lies with whoever shows that the shared chain's pieces lead into 𝔏.Q₂.

Limits. It swaps the field for an equation: at which 𝔏 the equation holds is not said here.
No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.ThreeLeft
import Johnson.Desc.Sound.GlueAtLedgerStep.SharedAtTablesR

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

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
  (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
  (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
  (ext : ℕ → (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str →
    Wit (CellsM numsFull) At.Tok MsgT → Wit (CellsM numsFull) At.Tok MsgT)

set_option quotPrecheck false in
/-- The first chain's state as the table reads it. -/
local notation "GT" => (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
  ((a.1, (fun s => s) a.2) : (F0T o Zp Np cF).XiPub × TS))

set_option quotPrecheck false in
/-- The three rows of pieces. -/
local notation "TW" => (piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂
  𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)

set_option quotPrecheck false in
/-- The shared table's numbers, tied to the first table's. -/
local notation "NT" => tiedNumbers (At.N Zp cF) 𝔏.Ns

set_option quotPrecheck false in
/-- The shared table's meaning, tied to the first table's. -/
local notation "MT" => tiedMeaning GT (h.mq 𝔇₀) 𝔏.MgS

set_option quotPrecheck false in
/-- The two later tables' own condition. -/
local notation "OC" => ocR GT (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps h.rc

/-- **The shared table's own step, at the tower's letters.** -/
def AtMg.stepOf := stepAt NT MT 𝔏.Pm OC 𝔏.split (TW).p₂ (TW).l₂ ext

/-- **The field stepQ at the tower's letters**, where 𝔏.Q₂ is the shared table's own step. -/
theorem AtMg.stepQ_field (hQ : 𝔏.Q₂ = h.stepOf 𝔇₀ 𝔏 ext) : ∀ k a b, 𝔏.Q₂ k a b →
    onQ₂ NT 𝔏.Pm OC 𝔏.split (TW).p₂ (TW).l₂ (k + 1) b ∧
      ((∃ w, relQ₂ NT MT 𝔏.split (TW).p₂ (TW).l₂ (k + 1) b w) →
        ∃ w, relQ₂ NT MT 𝔏.split (TW).p₂ (TW).l₂ k a w) := by
  rw [hQ]
  exact stepQ_tablesR _ _ _ _ _ _ _ _ _ _ _ ext

/-- It is the field stepQ of `h.Three`'s own tables_fit. -/
example (hQ : 𝔏.Q₂ = h.stepOf 𝔇₀ 𝔏 ext) (V : h.Three 𝔇₀ 𝔏) : h.Three 𝔇₀ 𝔏 :=
  ThreeF.mk V.head_cuts V.reply_leaves
    { V.tables_fit with stepQ := h.stepQ_field 𝔇₀ 𝔏 ext hQ }

/-- It is the field stepQ of `h.ThreeLeft`'s own tables_left. -/
example (hQ : 𝔏.Q₂ = h.stepOf 𝔇₀ 𝔏 ext) (V : h.ThreeLeft 𝔇₀ 𝔏) : h.ThreeLeft 𝔇₀ 𝔏 :=
  ThreeLeftF.mk V.head_cuts { V.tables_left with stepQ := h.stepQ_field 𝔇₀ 𝔏 ext hQ }

end P5J

#print axioms P5J.AtMg.stepQ_field
