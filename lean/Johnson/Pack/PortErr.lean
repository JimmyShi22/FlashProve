-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/PortErr.lean: the error of a sending, member by member, as a fraction of the joint
seeds.

Statements and proofs. q is the size of the extension field. The arithmetic is done for an abstract
finite field and for natural numbers; the extension field enters by instantiation.
Main names:
  `cardU`, `padErr_def`: a finite field has q - 1 units; the number `err` of `Sample.pad` with
    factors in the units, at a cube of b bits, is the larger of b q^(b - 1) (q - 1) and q^b.
  `max_big`, `max_small`, `rule_big`, `rule_small`: arithmetic.
  `card_D`, `mult_eq`, `zerr_def`: the joint seeds of a sending are q^bMax (q - 1); a member's
    multiplicity is q^(bMax - b), b its cube's bits.
  `termOf`, `err_sum`: the sending's error (`ldSendFamErr`) is the sum of the members' terms.
  `term_big`, `term_small`: with c a member's term, n the number of joint seeds and L its list: at b
    ≥ 2, c q = (C(L, 2) b) n; at b ≤ 1, c (q - 1) = C(L, 2) n. So c / n = C(L, 2) max (b / q) (1 /
    (q - 1)).
Limits: no lemma here names the planner's bound. By its text (`sampleError`,
OnBytes/Params/Distance.lean; `planSend`, OnBytes/Params/Planner.lean) that bound is, at one answer,
the same with L² / 2 in place of C(L, 2), and the messages' errors add; so the term here is the
smaller. L here is the library's `listMax`, there the planner's own list size.
-/
import Johnson.Pack.PortS

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000

namespace Johnson.Pack
open Cb Cb.Ood Iop IOR Prob OnBytes.Slice

section Abstract
variable (E : Type) [Field E] [Fintype E]

theorem cardU [inst : Fintype Eˣ] : Fintype.card Eˣ = Fintype.card E - 1 := by
  classical
  have h := Fintype.card_units E
  rw [← h]
  exact congrArg (@Fintype.card Eˣ) (Subsingleton.elim _ _)

theorem padErr_def [Fintype Eˣ] (b : ℕ) {J₀ P : Type} (pl : J₀ → Fin b → Bool) (w : P → E) :
    (Sample.pad E (Fin b) J₀ P Eˣ pl w Units.val).err =
      max (b * Fintype.card E ^ (b - 1) * (Fintype.card E - 1)) (Fintype.card E ^ b) := by
  show max (Fintype.card (Fin b) * Fintype.card E ^ (Fintype.card (Fin b) - 1) * Fintype.card Eˣ)
    (Fintype.card E ^ Fintype.card (Fin b)) = _
  rw [Fintype.card_fin, cardU E]

end Abstract

/-- Arithmetic: the larger of the two, at two bits or more. -/
theorem max_big (q b : ℕ) (hq : 2 ≤ q) (h : 2 ≤ b) :
    max (b * q ^ (b - 1) * (q - 1)) (q ^ b) = b * q ^ (b - 1) * (q - 1) := by
  refine max_eq_left ?_
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have h2 : 2 * (q - 1) ≤ (c + 1) * (q - 1) := Nat.mul_le_mul_right _ h
  have h1 : q ≤ (c + 1) * (q - 1) := le_trans (by omega) h2
  calc q ^ c * q ≤ q ^ c * ((c + 1) * (q - 1)) := Nat.mul_le_mul_left _ h1
    _ = (c + 1) * q ^ c * (q - 1) := by ring

theorem max_small (q b : ℕ) (h : b ≤ 1) : max (b * q ^ (b - 1) * (q - 1)) (q ^ b) = q ^ b := by
  refine max_eq_right ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl
  · simp
  · simp

theorem rule_big (q n b C : ℕ) (hb : b ≤ n) (h : 2 ≤ b) :
    q ^ (n - b) * (C * (b * q ^ (b - 1) * (q - 1))) * q = (C * b) * (q ^ n * (q - 1)) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + (c + 1) := ⟨n - (c + 1), by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  ring

theorem rule_small (q n b C : ℕ) (hb : b ≤ n) :
    q ^ (n - b) * (C * q ^ b) * (q - 1) = C * (q ^ n * (q - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + b := ⟨n - b, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

/-! ### At the sending -/

theorem two_le_card : 2 ≤ Fintype.card GE := Fintype.one_lt_card

theorem zerr_def (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : (portZ cs s).err =
    max (bitsZ cs s * Fintype.card GE ^ (bitsZ cs s - 1) * (Fintype.card GE - 1))
      (Fintype.card GE ^ bitsZ cs s) :=
  padErr_def GE (bitsZ cs s) (J₀ := {j // ¬ padP cs s j}) (P := {j // padP cs s j})
    (fun j t => (idxZ cs s j.1).testBit t.val) (wZ cs s)

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))

theorem card_D :
    Fintype.card (seedsOf cs l).D = Fintype.card GE ^ bMax cs l * (Fintype.card GE - 1) := by
  show Fintype.card ((Fin (bMax cs l) → GE) × GEˣ) = _
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, cardU GE]

theorem mult_eq (i : Fin l.length) :
    (seedsOf cs l).mult i = Fintype.card GE ^ (bMax cs l - bitsZ cs (l.get i).1) := by
  show Fintype.card (Fin (bMax cs l - bitsZ cs (l.get i).1) → GE) = _
  rw [Fintype.card_fun, Fintype.card_fin]

/-- A member's term of the sending's error. -/
noncomputable def termOf (Ls : Fin l.length → ℕ) (i : Fin l.length) : ℕ :=
  (seedsOf cs l).mult i * ((Ls i).choose 2 * (portZ cs (l.get i).1).err)

theorem err_sum (Ls : Fin l.length → ℕ) :
    ldSendFamErr (sigOf cs l) (seedsOf cs l) Ls = ∑ i, termOf cs l Ls i := by
  unfold ldSendFamErr termOf
  rfl

/-- The term against the number of seeds, at a cube of two bits or more. -/
theorem term_big (Ls : Fin l.length → ℕ) (i : Fin l.length) (h : 2 ≤ bitsZ cs (l.get i).1) :
    termOf cs l Ls i * Fintype.card GE =
      ((Ls i).choose 2 * bitsZ cs (l.get i).1) * Fintype.card (seedsOf cs l).D := by
  unfold termOf
  rw [mult_eq, zerr_def, max_big _ _ two_le_card h, card_D]
  exact rule_big _ _ _ _ (bits_le cs l i) h

/-- The term against the number of seeds, at a cube of at most one bit. -/
theorem term_small (Ls : Fin l.length → ℕ) (i : Fin l.length) (h : bitsZ cs (l.get i).1 ≤ 1) :
    termOf cs l Ls i * (Fintype.card GE - 1) =
      (Ls i).choose 2 * Fintype.card (seedsOf cs l).D := by
  unfold termOf
  rw [mult_eq, zerr_def, max_small _ _ h, card_D]
  exact rule_small _ _ _ _ (bits_le cs l i)

end
end Johnson.Pack

#print axioms Johnson.Pack.zerr_def
#print axioms Johnson.Pack.card_D
#print axioms Johnson.Pack.err_sum
#print axioms Johnson.Pack.term_big
#print axioms Johnson.Pack.term_small
#print axioms Johnson.Pack.cardU
#print axioms Johnson.Pack.padErr_def
#print axioms Johnson.Pack.max_big
#print axioms Johnson.Pack.rule_big
#print axioms Johnson.Pack.rule_small
