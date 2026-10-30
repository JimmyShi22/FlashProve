-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/EnumDigits.lean: ENUMERATIONS BY DIGITS: NO MEMBER IS PICKED BY A STATEMENT OF
EXISTENCE, AND EACH LENGTH IS WRITTEN AS A PRODUCT OR A POWER. Definitions, statements and proofs;
general.

Why. Johnson/Top/ToldReachAll.lean covers the honest committer's coins by enumerations that are
picked by choice: witnesses, no algorithm. A description whose running fields may use no choice
wants enumerations that are written. Here they are built from their parts: entry
number c of a pair, of a function or of salts is read off the digits of c.

Beside Iop/Num.lean. That file's numberings (`Num α`: a bijection with `Fin (Fintype.card α)`;
`Num.blocks`) are written too, and `Enum.ofNum` (Iop/WireOf.lean) makes an enumeration of one. Its
length is then `Fintype.card α - 1`, and at a closed type of functions Lean's kernel sets out to
compute that number, which has more digits than can be written.

So the lengths here are products and powers of the parts' lengths. THE KERNEL IS NOT TAMED BY THAT
ALONE: see the head of Johnson/Goal/Conditions/WideDigits.lean.

Main names (namespace `VerifiableInference.OnPublicFiles`). Each `…_ok` says `Enum.OK`: every member of
the type is listed, once.
  `enumBool`, `enumBool_ok`: false, true.
  `enumZMod p`, `enumZMod_ok`: the integers modulo p (p not 0): entry c is c.
  `enumPair a b`, `enumPair_ok`: pairs: entry c is (entry c % A of a, entry c / A % B of b), A and B
    the two lengths.
  `enumFuns k a`, `enumFuns_ok`: functions from `Fin k`: entry c at j is entry c / A^j % A of a: THE
    DIGIT OF WEIGHT A^j OF c IN BASE A. By `finFunctionFinEquiv` (Mathlib).
  `saltsBy d s E`, `saltsBy_once`, `saltsBy_covers`: the salts `saltsOfBits d s f`
    (Johnson/Top/ToldReachAll.lean), f running through E: general in E.
  **`saltsDigits d s`**, `saltsDigits_once`, **`saltsDigits_covers`**: at E := the functions by
    digits: bit k of the salt at place j is the digit of weight 2^k of the digit of weight (2^s)^j
    of c.

Limits.
- NO ENTRY IS EVALUATED, and at the sizes meant the numbers c have more digits than a machine holds.
  "No choice" is said of the TEXT of the definitions here (each is a quotient and a remainder); the
  print at the foot speaks of axioms beneath types and proofs too.
- Salts of another length than s at one of the first 2^d places are not covered.
- Nothing on drawing a number uniformly.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ToldReachAll
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom
open _root_.Iop (Enum)

variable {α β : Type}

/-- False, true. -/
def enumBool : Enum Bool := ⟨1, fun c => decide (c.val = 1)⟩

theorem enumBool_ok : enumBool.OK :=
  ⟨fun a b h =>
      (by decide : ∀ a b : Fin 2, decide (a.val = 1) = decide (b.val = 1) → a = b) a b h,
    fun b => by
      cases b
      · exact ⟨(0 : Fin 2), rfl⟩
      · exact ⟨(1 : Fin 2), rfl⟩⟩

/-- The integers modulo p: entry c is c. -/
def enumZMod (p : ℕ) : Enum (ZMod p) := ⟨p - 1, fun c => (c.val : ZMod p)⟩

theorem enumZMod_ok (p : ℕ) [NeZero p] : (enumZMod p).OK := by
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne p))
  constructor
  · intro c c' h
    have h' : ((c.val : ℕ) : ZMod p) = ((c'.val : ℕ) : ZMod p) := h
    have e := congrArg ZMod.val h'
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_eq c.isLt hp),
      ZMod.val_natCast_of_lt (lt_of_lt_of_eq c'.isLt hp)] at e
    exact Fin.ext e
  · intro x
    exact ⟨⟨x.val, lt_of_lt_of_eq (ZMod.val_lt x) hp.symm⟩, ZMod.natCast_zmod_val x⟩

/-- Pairs: the remainder names the first, the quotient the second. -/
def enumPair (a : Enum α) (b : Enum β) : Enum (α × β) where
  n := (a.n + 1) * (b.n + 1) - 1
  e := fun c => (a.e ⟨c.val % (a.n + 1), Nat.mod_lt _ a.n.succ_pos⟩,
    b.e ⟨c.val / (a.n + 1) % (b.n + 1), Nat.mod_lt _ b.n.succ_pos⟩)

theorem enumPair_ok (a : Enum α) (b : Enum β) (ha : a.OK) (hb : b.OK) : (enumPair a b).OK := by
  have hp : (a.n + 1) * (b.n + 1) - 1 + 1 = (a.n + 1) * (b.n + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))
  constructor
  · intro c c' h
    have h₁ : a.e ⟨c.val % (a.n + 1), Nat.mod_lt _ a.n.succ_pos⟩ =
        a.e ⟨c'.val % (a.n + 1), Nat.mod_lt _ a.n.succ_pos⟩ := congrArg Prod.fst h
    have h₂ : b.e ⟨c.val / (a.n + 1) % (b.n + 1), Nat.mod_lt _ b.n.succ_pos⟩ =
        b.e ⟨c'.val / (a.n + 1) % (b.n + 1), Nat.mod_lt _ b.n.succ_pos⟩ := congrArg Prod.snd h
    exact Fin.ext (pair_once a.n b.n c.val c'.val (lt_of_lt_of_eq c.isLt hp)
      (lt_of_lt_of_eq c'.isLt hp) (congrArg Fin.val (ha.1 h₁)) (congrArg Fin.val (hb.1 h₂)))
  · rintro ⟨x, y⟩
    obtain ⟨i, hi⟩ := ha.2 x
    obtain ⟨j, hj⟩ := hb.2 y
    have h := reach_pair a.n b.n i.val j.val i.isLt j.isLt
    have ei : (⟨(i.val + (a.n + 1) * j.val) % (a.n + 1), Nat.mod_lt _ a.n.succ_pos⟩ :
        Fin (a.n + 1)) = i := Fin.ext h.1
    have ej : (⟨(i.val + (a.n + 1) * j.val) / (a.n + 1) % (b.n + 1),
        Nat.mod_lt _ b.n.succ_pos⟩ : Fin (b.n + 1)) = j := Fin.ext h.2.1
    refine ⟨⟨i.val + (a.n + 1) * j.val, lt_of_lt_of_eq h.2.2 hp.symm⟩, ?_⟩
    show (a.e ⟨(i.val + (a.n + 1) * j.val) % (a.n + 1), Nat.mod_lt _ a.n.succ_pos⟩,
      b.e ⟨(i.val + (a.n + 1) * j.val) / (a.n + 1) % (b.n + 1), Nat.mod_lt _ b.n.succ_pos⟩) =
        (x, y)
    rw [ei, ej, hi, hj]

/-- Functions from `Fin k`: the value at j is named by the digit of weight (a.n + 1)^j. -/
def enumFuns (k : ℕ) (a : Enum α) : Enum (Fin k → α) where
  n := (a.n + 1) ^ k - 1
  e := fun c j => a.e ⟨c.val / (a.n + 1) ^ j.val % (a.n + 1), Nat.mod_lt _ a.n.succ_pos⟩

theorem enumFuns_ok (k : ℕ) (a : Enum α) (ha : a.OK) : (enumFuns k a).OK := by
  have hp : (a.n + 1) ^ k - 1 + 1 = (a.n + 1) ^ k :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) k))
  have key : ∀ c : Fin ((a.n + 1) ^ k - 1 + 1), (enumFuns k a).e c =
      fun j => a.e (finFunctionFinEquiv.symm (Fin.cast hp c) j) := by
    intro c
    funext j
    rfl
  constructor
  · intro c c' h
    have h' : (fun j => a.e (finFunctionFinEquiv.symm (Fin.cast hp c) j)) =
        fun j => a.e (finFunctionFinEquiv.symm (Fin.cast hp c') j) :=
      (key c).symm.trans (h.trans (key c'))
    have h'' : finFunctionFinEquiv.symm (Fin.cast hp c) =
        finFunctionFinEquiv.symm (Fin.cast hp c') := by
      funext j
      exact ha.1 (congrFun h' j)
    have e : (Fin.cast hp c).val = (Fin.cast hp c').val :=
      congrArg Fin.val (finFunctionFinEquiv.symm.injective h'')
    exact Fin.ext e
  · intro f
    choose g hg using fun j => ha.2 (f j)
    refine ⟨Fin.cast hp.symm (finFunctionFinEquiv g), (key _).trans ?_⟩
    funext j
    show a.e (finFunctionFinEquiv.symm (finFunctionFinEquiv g) j) = f j
    rw [Equiv.symm_apply_apply, hg]

/-- The salts `saltsOfBits d s f`, f running through E. -/
def saltsBy (d s : ℕ) (E : Enum (Fin (2 ^ d) → Fin s → Bool)) : Enum (ℕ → Bits) where
  n := E.n
  e := fun c => saltsOfBits d s (E.e c)

/-- It lists each of these once. -/
theorem saltsBy_once (d s : ℕ) (E : Enum (Fin (2 ^ d) → Fin s → Bool)) (hE : E.OK) :
    Function.Injective (saltsBy d s E).e := by
  intro c c' h
  apply hE.1
  funext j
  have hj : saltsOfBits d s (E.e c) j.val = saltsOfBits d s (E.e c') j.val := congrFun h j.val
  unfold saltsOfBits at hj
  rw [dif_pos j.isLt, dif_pos j.isLt] at hj
  exact List.ofFn_injective hj

/-- Every choice of salts of the right length is covered, as far as the first 2^d places go. -/
theorem saltsBy_covers (d s : ℕ) (E : Enum (Fin (2 ^ d) → Fin s → Bool)) (hE : E.OK)
    (σ : ℕ → Bits) (hσ : ∀ j, j < 2 ^ d → (σ j).length = s) :
    ∃ c, ∀ j, j < 2 ^ d → (saltsBy d s E).e c j = σ j := by
  obtain ⟨c, hc⟩ := hE.2 (fun j k => (σ j.val).getD k.val false)
  refine ⟨c, fun j hj => ?_⟩
  show saltsOfBits d s (E.e c) j = σ j
  rw [hc]
  unfold saltsOfBits
  rw [dif_pos hj]
  apply List.ext_getElem
  · rw [List.length_ofFn, hσ j hj]
  · intro k h₁ h₂
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ h₂

/-- **All salts of s bits at each of the first 2^d places, by the digits of the number.** -/
def saltsDigits (d s : ℕ) : Enum (ℕ → Bits) := saltsBy d s (enumFuns (2 ^ d) (enumFuns s enumBool))

theorem saltsDigits_once (d s : ℕ) : Function.Injective (saltsDigits d s).e :=
  saltsBy_once d s _ (enumFuns_ok _ _ (enumFuns_ok _ _ enumBool_ok))

theorem saltsDigits_covers (d s : ℕ) (σ : ℕ → Bits) (hσ : ∀ j, j < 2 ^ d → (σ j).length = s) :
    ∃ c, ∀ j, j < 2 ^ d → (saltsDigits d s).e c j = σ j :=
  saltsBy_covers d s _ (enumFuns_ok _ _ (enumFuns_ok _ _ enumBool_ok)) σ hσ

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.enumBool
#print axioms VerifiableInference.OnPublicFiles.enumZMod
#print axioms VerifiableInference.OnPublicFiles.enumPair
#print axioms VerifiableInference.OnPublicFiles.enumFuns
#print axioms VerifiableInference.OnPublicFiles.saltsDigits
#print axioms VerifiableInference.OnPublicFiles.enumBool_ok
#print axioms VerifiableInference.OnPublicFiles.enumZMod_ok
#print axioms VerifiableInference.OnPublicFiles.enumPair_ok
#print axioms VerifiableInference.OnPublicFiles.enumFuns_ok
#print axioms VerifiableInference.OnPublicFiles.saltsDigits_once
#print axioms VerifiableInference.OnPublicFiles.saltsDigits_covers
