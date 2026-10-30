-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/EnumIndex.lean: THE WRITTEN INVERSE OF THE ENUMERATIONS BY DIGITS
(Johnson/Top/EnumDigits.lean): the NUMBER at which a given function, or given salts, stand in the
list: written, not picked by a statement of existence. General.

Why. EnumDigits.lean shows that saltsDigits d s lists all salts of s bits at the first 2^d places
(saltsDigits_covers: "there is c"). A generator of the committer's coins that is to name salts which
it is handed wants that c as a term.

Main names (namespace VerifiableInference.OnPublicFiles).
  idxBool, e_idxBool   false stands at 0, true at 1.
  idxFuns k a g, e_idxFuns   the function whose value at j stands at g j in a: its number has the
    digit g j at the weight (a.n + 1)^j: Mathlib's finFunctionFinEquiv, which is that sum.
  idxSalts d s f, e_idxSalts   the salts saltsOfBits d s f.
  idxOf d s σ, e_idxOf   GIVEN SALTS σ of s bits at the first 2^d places: at these places the entry
    with the number idxOf d s σ is σ.

Limits. The print at the foot shows Classical.choice beneath idxOf: it lies beneath Mathlib's
finFunctionFinEquiv; "written" is said of the text of the definitions here, and Lean has made code
for them. EnumDigits.lean's: written, not run: at the sizes meant the numbers have more digits than
a machine holds. Beyond the first 2^d places the listed salts are empty, whatever σ is there.
Nothing on drawing a number.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.EnumDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom
open _root_.Iop (Enum)

variable {α : Type}

/-- False stands at 0, true at 1. -/
def idxBool (b : Bool) : Fin (enumBool.n + 1) := ⟨b.toNat, by cases b <;> decide⟩

theorem e_idxBool (b : Bool) : enumBool.e (idxBool b) = b := by cases b <;> rfl

theorem enumFuns_len (k : ℕ) (a : Enum α) : (enumFuns k a).n + 1 = (a.n + 1) ^ k :=
  Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) k))

/-- The number of the function whose value at j stands at g j in a. -/
def idxFuns (k : ℕ) (a : Enum α) (g : Fin k → Fin (a.n + 1)) : Fin ((enumFuns k a).n + 1) :=
  Fin.cast (enumFuns_len k a).symm (finFunctionFinEquiv g)

theorem e_idxFuns (k : ℕ) (a : Enum α) (g : Fin k → Fin (a.n + 1)) :
    (enumFuns k a).e (idxFuns k a g) = fun j => a.e (g j) := by
  funext j
  show a.e (finFunctionFinEquiv.symm (finFunctionFinEquiv g) j) = a.e (g j)
  rw [Equiv.symm_apply_apply]

/-- The number of the salts saltsOfBits d s f. -/
def idxSalts (d s : ℕ) (f : Fin (2 ^ d) → Fin s → Bool) : Fin ((saltsDigits d s).n + 1) :=
  idxFuns (2 ^ d) (enumFuns s enumBool) fun j => idxFuns s enumBool fun k => idxBool (f j k)

theorem e_idxSalts (d s : ℕ) (f : Fin (2 ^ d) → Fin s → Bool) :
    (saltsDigits d s).e (idxSalts d s f) = saltsOfBits d s f := by
  show saltsOfBits d s ((enumFuns (2 ^ d) (enumFuns s enumBool)).e
    (idxFuns (2 ^ d) (enumFuns s enumBool) fun j => idxFuns s enumBool fun k => idxBool (f j k))) =
      saltsOfBits d s f
  rw [e_idxFuns]
  congr 1
  funext j
  rw [e_idxFuns]
  funext k
  exact e_idxBool _

/-- The number of given salts: of σ j, j below 2 ^ d, the first s bits are read, false where σ j is
shorter; σ j from 2 ^ d on is not read. -/
def idxOf (d s : ℕ) (σ : ℕ → Bits) : Fin ((saltsDigits d s).n + 1) :=
  idxSalts d s fun j k => (σ j.val).getD k.val false

/-- **At the first 2^d places the entry with that number is σ**, if σ has s bits there. -/
theorem e_idxOf (d s : ℕ) (σ : ℕ → Bits) (hσ : ∀ j, j < 2 ^ d → (σ j).length = s) :
    ∀ j, j < 2 ^ d → (saltsDigits d s).e (idxOf d s σ) j = σ j := by
  intro j hj
  unfold idxOf
  rw [e_idxSalts]
  unfold saltsOfBits
  rw [dif_pos hj]
  apply List.ext_getElem
  · rw [List.length_ofFn, hσ j hj]
  · intro k h₁ h₂
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ h₂

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.idxOf
#print axioms VerifiableInference.OnPublicFiles.e_idxBool
#print axioms VerifiableInference.OnPublicFiles.e_idxFuns
#print axioms VerifiableInference.OnPublicFiles.e_idxSalts
#print axioms VerifiableInference.OnPublicFiles.e_idxOf
