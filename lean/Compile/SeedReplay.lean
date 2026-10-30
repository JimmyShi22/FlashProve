-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedReplay.lean: two lemmas on stores and on related oracle algorithms, used in
Compile/Batch/SeedReplay.lean (words of this library: lean/GLOSSARY.md).

  `viewVals_prefix`  If A is a prefix of B, the store B without all that follows A is A
                     (`viewVals`, Compile/Step1_life2_Virt.lean).
  `ORel.all_left`    If c and c' are related by `ORel r` (Compile/SeedKit.lean), every result a of c
                     has some b with r a b (`All`, Compile/SeedFix.lean).

The token language and its stores are devices of this library.
-/
import Compile.SeedFix

noncomputable section

open Rom Iop

namespace Compile
namespace Seed

open Life2 (up down viewVals)

variable {I X : Type} {lam : ℕ} (p : Params)

/-- the store without all that follows a prefix -/
theorem viewVals_prefix {A B : List Bits} (h : A <+: B) :
    viewVals A.length (B.length - A.length) B = A := by
  obtain ⟨C, rfl⟩ := h
  unfold viewVals
  have e : A.length + ((A ++ C).length - A.length) = (A ++ C).length := by simp
  rw [e, List.drop_length, List.append_nil, List.take_left']
  rfl

theorem ORel.all_left {S : OSpec} {α β : Type} {r : α → β → Prop} {c : OComp S α}
    {c' : OComp S β} (h : ORel r c c') :
    All (fun a => ∃ b, r a b) c := by
  induction h with
  | pure h => exact ⟨_, h⟩
  | query o q _ ih => exact ih
  | sample n _ ih => exact ih

end Seed
end Compile
