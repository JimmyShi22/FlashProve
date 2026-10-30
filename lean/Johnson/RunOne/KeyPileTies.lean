-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyPileTies.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS:
THE PREMISE PileTies OF pile_of_eval (Johnson/RunOne/KeyPile21.lean) PAID OUT OF THE PROMISE on₂ … 1
ITSELF, at the tables' own letters K₁ := plan₁ one and last₁ := last₁At one
(Johnson/RunOne/KeySeam1.lean): the
first chain's last book-keeping holds «every mask entry of the claim lies on a mask table» (sizesB:
Johnson/RunOne/KeyReaders1.lean).
ON EMPTINESS: as KeyRow21.lean's head: NO MEMBER OF on₂ … 1 IS SHOWN BY ANYBODY.
OBJECT: PileTies at K₁ := plan₁ one · last₁ := last₁At one · USER: pile_of_eval | point_back₂_lib
(hties) · LETTERS: one : OneTime; the tables' others free.
  last₁_masks   the first chain's last book-keeping gives: the state holds a claim, and every mask
    entry of it lies on a mask table
  pileTies_at   PROVED FROM: the plan has a stage (1 ≤ one.ranges.stages.length: PUBLIC: at a plan
    without a stage V's number would be B's)
WHAT IS SPENT OF THE PROMISE IN FRONT: Free₂ 1's last.
Nothing on soundness.
-/
import Johnson.RunOne.KeyPile21
import Johnson.RunOne.KeySeam1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState)
open _root_.Desc.Plain (Par)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ n₁ slots₁ ties₁ tiesA sizesB)

/-- The first chain's last book-keeping: every mask entry of the claim lies on a mask table. -/
theorem last₁_masks (one : OneTime) (s : FirstState) (h : last₁At one s = true) :
    ∀ L, s.lin = some L → ∀ u ∈ L.claim.masks.toList, u.part = .mask := by
  unfold last₁At at h
  have ht : ties₁ one (2 + 6 * n₁ one + 5) s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ tiesA sizesB at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  have hn : n₁ one = 2 := ht.1.1.1.1.1.1
  have h6 := ht.2.1.1.2
  rw [hn] at h6
  intro L hL u hu
  rw [hL] at h6
  have h6' : (listOfT (L.claim.masks.toList.map (·.oracle)) == [0] && L.claim.masks.all (·.part ==
      .mask)) = true := by simpa using h6
  have h7 := (Bool.and_eq_true_iff.1 h6').2
  have h8 := (Array.all_eq_true_iff_forall_mem.1 h7) u (Array.mem_toList_iff.1 hu)
  simpa using h8

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (off₂ : Nat → Nat)

/-- **PileTies, paid out of the promise.** -/
theorem pileTies_at (one : OneTime) (hst : 1 ≤ one.ranges.stages.length) :
    PileTies F Fr₂ G₂ at_ p (plan₁ one) R enc rad a coll (last₁At one) off₂ := by
  intro x hx L hL
  have hf : Free₂ F G₂ at_ p.S (plan₁ one) R coll (last₁At one) off₂ 1 x.1 (strsOf Fr₂ x.2) := by
    rcases hx with hn | ⟨_, _, h3, _⟩
    · exact absurd trivial hn
    · exact h3
  have hw := last₁_w one _ hf.last
  rw [hL] at hw
  have ew : L.w = 1 + 2 * one.ranges.stages.length := Option.some.inj hw
  refine ⟨?_, last₁_masks one _ hf.last L hL⟩
  rw [ew]
  have hne : one.ranges.stages ≠ [] := List.ne_nil_of_length_pos hst
  simp [plan₁, KeyReaders.planOf, hne]

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.last₁_masks
#print axioms Johnson.RunOne.KeyRows23.pileTies_at
