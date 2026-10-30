-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMemberFull.lean: THEOREMS. **The member at the written codes of a key file of full size**: the codes csKey, the shapes shIdx (the masks for the index) and shMul (the multiplicities) and the radii 6130 and 3131959 of Johnson/Top/H/KeyRows.lean.
OBJECT: dec₂ | cond₂ of KeyLetters.lean at csKey · shIdx · shMul · 6130 · 3131959 · the message numbers 0 and 1. USER: none yet. LETTERS: in member_full_at X · Y · stOf · f₀ · f₁ · MW · decW; in member_full | member_exists none.
  tieIdx | tieMul | meetsIdx | meetsMul | okIdx | okMul   the premises on numbers, by evaluation in the kernel
  shareIdx | shareMul      the inequality of clash_share at K = 128
  share_idx | share_mul    **at every word, fixed before the seed is drawn: the seeds that are collisions of its list are at most 2^-128 of the message's own seeds**. A count of typed seeds: no proof of work enters it
  member_full_at   member_two with no premise on numbers left
  member_full      **for every pair of messages and randomness (the two main rows of the second over the base field) and every third part there is a point at which cond₂ holds and dec₂ returns them**
  member_exists    the closed sentence: there are a point and a value with cond₂ and dec₂ = some
What is not claimed. That these numbers are a key file's is said elsewhere (Johnson/Goal/PlanValues/, not beneath this file). That the radii are those that a later test certifies. The frame's reading of strings. The matrix's decoder. Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyMemberBack
import Johnson.Top.H.KeyRows

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1
open Johnson.RunOne.KeySendErr (qE badOwn)
open Johnson.Top.H (csKey shIdx shMul)

theorem tieIdx : Tie csKey shIdx := ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem tieMul : Tie csKey shMul := ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem meetsIdx : meetsB csKey shIdx 6130 = true := by decide +kernel
theorem meetsMul : meetsB csKey shMul 3131959 = true := by decide +kernel
theorem okIdx : CodeOK csKey shIdx := by decide +kernel
theorem okMul : CodeOK csKey shMul := by decide +kernel

theorem shareIdx : badOwn csKey shIdx 6130 * 2 ^ 128 ≤ qE ^ bitsZ csKey shIdx * (qE - 1) := by
  unfold badOwn
  rw [Nat.choose_two_right]
  decide +kernel

theorem shareMul : badOwn csKey shMul 3131959 * 2 ^ 128 ≤ qE ^ bitsZ csKey shMul * (qE - 1) := by
  unfold badOwn
  rw [Nat.choose_two_right]
  decide +kernel

/-- The control on the inequality: it fails at 2^192. -/
theorem shareMul_not : ¬ badOwn csKey shMul 3131959 * 2 ^ 192 ≤ qE ^ bitsZ csKey shMul * (qE - 1) := by
  unfold badOwn
  rw [Nat.choose_two_right]
  decide +kernel

theorem share_idx (f : (portOmZ csKey shIdx 6130).Str) :
    cnt ((portOmZ csKey shIdx 6130).Clash f) * 2 ^ 128 ≤ Fintype.card ((Fin (bitsZ csKey shIdx) → GE) × GEˣ) := clash_share 128 meetsIdx shareIdx f

theorem share_mul (f : (portOmZ csKey shMul 3131959).Str) :
    cnt ((portOmZ csKey shMul 3131959).Clash f) * 2 ^ 128 ≤ Fintype.card ((Fin (bitsZ csKey shMul) → GE) × GEˣ) := clash_share 128 meetsMul shareMul f

/-- The message of masks for the index has no main row: every pair is Sendable. -/
theorem sendIdx (m : (portCode csKey shIdx).J → GE) (r : (portCode csKey shIdx).Q → GE) : Sendable csKey shIdx m r :=
  fun _ => ⟨fun x => x.1.elim0, fun q => q.1.elim0⟩

section
variable {X Y MW : Type} {stOf : X → Statement} {o₀ o₁ : Nat}
  {f₀ : Y → (portOmZ csKey shIdx 6130).Str} {f₁ : Y → (portOmZ csKey shMul 3131959).Str} {decW : Y → Option MW}

theorem member_full_at {m₀ : (portCode csKey shIdx).J → GE} {r₀ : (portCode csKey shIdx).Q → GE} {m₁ : (portCode csKey shMul).J → GE} {r₁ : (portCode csKey shMul).Q → GE}
    (h₁ : Sendable csKey shMul m₁ r₁) {a : X × Y} {W : MW}
    (hf₀ : f₀ a.2 = sent csKey shIdx 6130 m₀ r₀) (hf₁ : f₁ a.2 = sent csKey shMul 3131959 m₁ r₁) (hW : decW a.2 = some W)
    {ρ₀ : (Fin (bitsZ csKey shIdx) → GE) × GEˣ} {ρ₁ : (Fin (bitsZ csKey shMul) → GE) × GEˣ}
    (hI₀ : SeedIs csKey shIdx (stOf a.1) o₀ ρ₀ ((portZ csKey shIdx).val ρ₀ m₀ ())) (hI₁ : SeedIs csKey shMul (stOf a.1) o₁ ρ₁ ((portZ csKey shMul).val ρ₁ m₁ ()))
    (hn₀ : ¬ (portOmZ csKey shIdx 6130).Clash (sent csKey shIdx 6130 m₀ r₀) ρ₀) (hn₁ : ¬ (portOmZ csKey shMul 3131959).Clash (sent csKey shMul 3131959 m₁ r₁) ρ₁) :
    cond₂ csKey shIdx shMul 6130 3131959 o₀ o₁ stOf f₀ f₁ a ∧ dec₂ csKey shIdx shMul 6130 3131959 o₀ o₁ stOf f₀ f₁ decW a = some (m₀, m₁, W) :=
  member_two tieIdx tieMul (sendIdx m₀ r₀) h₁ hf₀ hf₁ hW hI₀ hI₁ hn₀ hn₁
end

theorem member_full {MW : Type} (m₀ : (portCode csKey shIdx).J → GE) (r₀ : (portCode csKey shIdx).Q → GE) (m₁ : (portCode csKey shMul).J → GE) (r₁ : (portCode csKey shMul).Q → GE)
    (h₁ : Sendable csKey shMul m₁ r₁) (W : MW) :
    ∃ a : Statement × ((portOmZ csKey shIdx 6130).Str × (portOmZ csKey shMul 3131959).Str × MW),
      cond₂ csKey shIdx shMul 6130 3131959 0 1 id (fun y => y.1) (fun y => y.2.1) a ∧
        dec₂ csKey shIdx shMul 6130 3131959 0 1 id (fun y => y.1) (fun y => y.2.1) (fun y => some y.2.2) a = some (m₀, m₁, W) := by
  obtain ⟨ρ₀, hn₀⟩ := no_clash_has 128 (by decide) meetsIdx shareIdx (sent csKey shIdx 6130 m₀ r₀)
  obtain ⟨ρ₁, hn₁⟩ := no_clash_has 128 (by decide) meetsMul shareMul (sent csKey shMul 3131959 m₁ r₁)
  exact member_two_has tieIdx tieMul (sendIdx m₀ r₀) h₁ W hn₀ hn₁

/-- **The closed sentence.** -/
theorem member_exists :
    ∃ (a : Statement × ((portOmZ csKey shIdx 6130).Str × (portOmZ csKey shMul 3131959).Str × Unit)) (u : Two csKey shIdx shMul Unit),
      cond₂ csKey shIdx shMul 6130 3131959 0 1 id (fun y => y.1) (fun y => y.2.1) a ∧
        dec₂ csKey shIdx shMul 6130 3131959 0 1 id (fun y => y.1) (fun y => y.2.1) (fun y => some y.2.2) a = some u := by
  obtain ⟨a, h⟩ := member_full (MW := Unit) 0 0 0 0 (fun _ => ⟨fun _ => ⟨0, map_zero _⟩, fun _ => ⟨0, map_zero _⟩⟩) ()
  exact ⟨a, _, h⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.tieIdx
#print axioms Johnson.RunOne.KeyLetters.tieMul
#print axioms Johnson.RunOne.KeyLetters.share_idx
#print axioms Johnson.RunOne.KeyLetters.share_mul
#print axioms Johnson.RunOne.KeyLetters.shareMul_not
#print axioms Johnson.RunOne.KeyLetters.member_full_at
#print axioms Johnson.RunOne.KeyLetters.member_full
#print axioms Johnson.RunOne.KeyLetters.member_exists
