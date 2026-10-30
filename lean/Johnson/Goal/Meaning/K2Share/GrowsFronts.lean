-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/K2Share/GrowsFronts.lean: kind K2's four quiet steps beside the switch: behind
each the statement has only grown (Johnson/Desc/Grows.lean).

  headFrontQ_grows ("H.0.front"), headOpenQ_grows ("H.1.quiet") (Johnson/Top/H0/Tw/K2C/Head.lean):
    by grows_front and grows_behind (Johnson/Goal/Meaning/K2Share/K2Whole.lean).
  grows_finishFront, finishFrontQ_grows ("F.0.front"), finishBehindQ_grows ("F.0.quiet")
    (Johnson/Top/H0/Tw/K2C/Finish.lean): the first opens one group (grows_newGroupG); the second
    leaves the statement.
With k2_grows (K2Whole.lean) these are the five clauses of K2Grows in Johnson/IMR/GrowsSeat.lean, which lies in this library.
OBJECT: the four laid steps. USER: Johnson/IMR/K2ShareAt.lean, which lies in this library.
-/
import Johnson.Goal.Meaning.K2Share.RecFronts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Keeps (Fn)
open VerifiableInference.Desc.ChainEnd (GrowsBy)
open _root_.Tw.K2 (firstFront finishFront firstBehind newGroupG)

theorem headFrontQ_grows (tl : HTailF2) : Fn (GrowsBy fun s : S => s.st) (headFrontQ tl) :=
  fun s t h => by
  show Grows s.st t.st
  unfold headFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨x, hx, h⟩ := ebind h
      obtain ⟨s₁, h1, h⟩ := ebind h
      split at h
      · cases h
        exact grows_front hx
      · cases h

theorem headOpenQ_grows (P : HeadPar) : Fn (GrowsBy fun s : S => s.st) (headOpenQ P) :=
  fun s t h => by
  show Grows s.st t.st
  unfold headOpenQ at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, hb, h⟩ := ebind h
        dsimp only at h
        obtain ⟨⟨L, out⟩, hfr, h⟩ := ebind h
        dsimp only at h
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h1, h⟩ := ebind h
                split at h
                · cases h
                  exact grows_behind hb
                · cases h
        · cases h
  · cases h

theorem grows_finishFront {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : finishFront S0 f = .ok x) : Grows S0 x.st := by
  unfold finishFront at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i S' g hn
        cases h
        exact grows_newGroupG hn

theorem finishFrontQ_grows : Fn (GrowsBy fun s : S => s.st) finishFrontQ := fun s t h => by
  show Grows s.st t.st
  unfold finishFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i G x hG hx
        obtain ⟨s₁, h1, h⟩ := ebind h
        split at h
        · cases h
          exact grows_finishFront hx
        · cases h
      · cases h
      · cases h

theorem finishBehindQ_grows : Fn (GrowsBy fun s : S => s.st) finishBehindQ := fun s t h => by
  show Grows s.st t.st
  unfold finishBehindQ at h
  split at h
  · obtain ⟨m, -, rfl⟩ := Keeps.emap_ok h
    exact Grows.refl _
  · cases h

#print axioms headFrontQ_grows
#print axioms headOpenQ_grows
#print axioms finishFrontQ_grows
#print axioms finishBehindQ_grows

end VerifiableInference.Desc.First.K2
