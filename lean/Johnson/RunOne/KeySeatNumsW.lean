-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeatNumsW.lean: THEOREMS BY THE KERNEL's EVALUATION, EACH A TEST THAT CAN FAIL, AND THREE COROLLARIES. The third sampled message of the key file's first chain (W's), at the full size's codes: its shape AS AN EVALUATION PRINTED IT off the key file's own description (code 5 · one main row of degree 3 · one mask row under mask code 6 · one answer): Tie · meetsB at a radius · hm · the degree. Then: honest_pins_at (KeyHonestAt.lean) at the three shapes, from «no fault at the seat» alone.
OBJECT: csKey (Johnson/Top/H/KeyRows.lean) · shW (here). USER: honest_full_idx | _mul | _w. That shW IS the description's shape as a term is not shown: its six numbers are those that the evaluation printed.
Nothing on soundness.

-/
import Johnson.RunOne.KeySeatNums
import Johnson.RunOne.KeyHonestAt

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1
open VerifiableInference.Desc.Key.Fill
open Johnson.Top.H (csKey shIdx shMul)

/-- W's message: one main row over the extension field under code 5, one mask row under mask code 6. -/
def shW : OracleShape := { code := 5, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 6, answers := 1 }

theorem tieW : Tie csKey shW := ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem meetsW : meetsB csKey shW 3145534 = true := by decide +kernel
/-- The control: one more is too many. -/
theorem meetsW_not : meetsB csKey shW 3145535 = false := by decide +kernel
theorem hmW : shW.mainRows = 0 ∨ (cMain csKey shW).a = aOf csKey shW := by decide +kernel
theorem numsW : ((cMain csKey shW).a, (cMask csKey shW).a, aOf csKey shW) = (22, 13, 22) := by decide +kernel

/-- The conclusion of honest_pins_at, as a proposition on the letters. -/
def HonestAt {XI : Type} (F : FileDescription XI) (cs : Codes) (s : OracleShape) (e j₀ t₀ : ℕ) : Prop :=
  ∀ (m : (portCode cs s).J → GE) (r : (portCode cs s).Q → GE), Sendable cs s m r → ∀ (o : ℕ) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ),
    ∃ (a : Statement) (y : Strs) (w : Wit Unit Unit VerifiableInference.Desc.Key.Fill.Tab),
      hasSmp (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a = true ∧
      NoColl F (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a y ∧
      PIN F (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a y w ∧
      w.msg 0 = ofU cs s e m

variable {XI : Type} (F : FileDescription XI) (tag : String) (j₀ t₀ : ℕ)

theorem honest_full_idx (hfit : seatFaultAt F csKey tag shIdx j₀ t₀ = none) : HonestAt F csKey shIdx 6130 j₀ t₀ :=
  fun _ _ h o ρ => honest_pins_at F tag j₀ t₀ hfit tieIdx meetsIdx h o ρ
theorem honest_full_mul (hfit : seatFaultAt F csKey tag shMul j₀ t₀ = none) : HonestAt F csKey shMul 3131959 j₀ t₀ :=
  fun _ _ h o ρ => honest_pins_at F tag j₀ t₀ hfit tieMul meetsMul h o ρ
theorem honest_full_w (hfit : seatFaultAt F csKey tag shW j₀ t₀ = none) : HonestAt F csKey shW 3145534 j₀ t₀ :=
  fun _ _ h o ρ => honest_pins_at F tag j₀ t₀ hfit tieW meetsW h o ρ

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.tieW
#print axioms Johnson.RunOne.KeyLetters.meetsW
#print axioms Johnson.RunOne.KeyLetters.meetsW_not
#print axioms Johnson.RunOne.KeyLetters.hmW
#print axioms Johnson.RunOne.KeyLetters.numsW
#print axioms Johnson.RunOne.KeyLetters.honest_full_idx
#print axioms Johnson.RunOne.KeyLetters.honest_full_mul
#print axioms Johnson.RunOne.KeyLetters.honest_full_w
