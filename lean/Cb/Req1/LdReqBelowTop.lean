-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqBelowTop.lean: at the bound "infinite" every clause "every round's error, as a
probability, is at most κ" that is named below holds, under the hypotheses below. These errors are
numbers that a link lists (the data field `Link.P.err`), or any list e: that a link is sound at the
numbers that it lists is no statement of this file.

Statements (each a `Prop` in `Cb.Spec`) and proofs. The clauses are `Err.Below` (Iop/InteractiveOracleProof.lean) and
what Cb/Req1/LdReqBelow.lean, Cb/Req1/LdSegRefBelow.lean and Cb/Req1/LdReqRefFinal.lean build on it.

Why: a verifier message is drawn from a non-empty finite type: so ⊤ times its number of values is ⊤.

Main names:
  `Spec.ldBelowTop_err`: `Err.Below e ⊤`, for every list of errors.
  `Spec.ldBelowTop_nat`: `(n : ℝ≥0∞) ≤ ⊤ *` (number of values of a non-empty finite type).
    `Spec.ldBelowTop_send`: a sending's number.
  `Spec.ldBelowTop_chain`, `Spec.ldBelowTop_prog`: every chain, every list of moves.
  `Spec.ldBelowTop_nums`: `A.Nums ⊤` for every closed body; `S.NumsAt ⊤` for every reference segment
    with `[Nonempty S.K.Pf]`.

Limits: bookkeeping, for guards that say nothing on the size of errors: a toy that takes κ := ⊤
meets the clauses on numbers of Cb/Req1/LdReqRefFinal.lean for any data (a segment: with
`[Nonempty S.K.Pf]`; the list's `L.Nums ⊤` is not stated here); it then shows nothing about them.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefFinal

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

namespace Spec

def ldBelowTop_nat : Prop :=
  ∀ (n : ℕ) (D : Type) [Fintype D] [Nonempty D], (n : ℝ≥0∞) ≤ ⊤ * (Fintype.card D : ℝ≥0∞)

def ldBelowTop_send : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (d : LdSendD a),
    (ldSendFamErr d.N d.Sd d.L : ℝ≥0∞) ≤ ⊤ * (Fintype.card d.Sd.D : ℝ≥0∞)

def ldBelowTop_err : Prop := ∀ (s : Shape) (e : Err s), Err.Below e ⊤

def ldBelowTop_chain : Prop := ∀ (Kc : Type) (A B : Joint Kc) (c : Chain Kc A B), c.ErrBelow ⊤

def ldBelowTop_prog : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a b : LdStage E Kc) (p : LdProg a b), p.Below ⊤

def ldBelowTop_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E),
    (∀ A : LdRefD E Kc I, A.Nums ⊤) ∧
    (∀ (a : LdStage E Kc) (S : LdRefS E Kc I a) [Nonempty S.K.Pf], S.NumsAt ⊤)

end Spec

theorem ldBelowTop_nat : Spec.ldBelowTop_nat := fun n D _ _ => by
  rw [ENNReal.top_mul (by exact_mod_cast Fintype.card_ne_zero)]
  exact le_top

theorem ldBelowTop_send : Spec.ldBelowTop_send := fun _ _ _ _ _ d => ldBelowTop_nat _ d.Sd.D

theorem ldBelowTop_err : Spec.ldBelowTop_err := by
  intro s
  induction s with
  | nil => intro _; trivial
  | cons r s ih => exact fun e => ⟨ldBelowTop_nat e.1 r.Chal, ih e.2⟩

theorem ldBelowTop_chain : Spec.ldBelowTop_chain := by
  intro Kc A B c
  induction c with
  | one l => exact (errBelow_one l ⊤).2 (ldBelowTop_err _ _)
  | snoc c l ih => exact (errBelow_snoc c l ⊤).2 ⟨ih, ldBelowTop_err _ _⟩

theorem ldBelowTop_prog : Spec.ldBelowTop_prog := by
  intro E Kc _ _ a b p
  induction p with
  | nil => exact LdProg.below_nil _ ⊤
  | snoc p m ih => exact (LdProg.below_snoc p m ⊤).2 ⟨ih, ldBelowTop_chain Kc _ _ _⟩

theorem ldBelowTop_nums : Spec.ldBelowTop_nums := fun E Kc _ _ _ =>
  ⟨fun _ =>
      ⟨ldBelowTop_prog E Kc _ _ _, ldBelowTop_nat _ _, ldBelowTop_nat _ _, ldBelowTop_nat _ _,
        ldBelowTop_nat _ _, ldBelowTop_err _ _, ldBelowTop_err _ _⟩,
    fun _ _ _ =>
      ⟨⟨ldBelowTop_prog E Kc _ _ _, ldBelowTop_nat _ _, ldBelowTop_nat _ _, ldBelowTop_nat _ _,
          ldBelowTop_nat _ _, ldBelowTop_err _ _, ldBelowTop_err _ _⟩,
        ldBelowTop_nat _ _, ldBelowTop_err _ _, ldBelowTop_nat _ _, ldBelowTop_nat _ _⟩⟩

end Cb
