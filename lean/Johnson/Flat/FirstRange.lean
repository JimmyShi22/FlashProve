-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/FirstRange.lean: the fixed instance from which `pubOf` takes the description's rounds
meets the reader's test on an instance beside the lengths (r < e, and y = 0 if e is before the
window's end), at the sizes of every parameter file that `sizesAt` takes; and `Verify.linksOf`
returns at the plan of every three public files that `planned` takes.

Main names:
  `sizesAt_window_pos`: the window of a parameter file that `sizesAt` takes is not empty: it is a
    power of two.
  `firstInstance_range`: where the window is not empty, `firstInstance` (Johnson/Flat/LinksAt.lean)
    has r < e, and y = 0 if e is before the window's end. `firstInstance_range_at`: so at
    `sizesAt`'s sizes, with no premise on the window.
  `planned_builtOf`, `linksOf_returns`: where `planned` returns p, `Verify.linksOf p.X cov` returns
    at EVERY cov. No run of the verifier program on a request is asked as a premise:
    `Verify.linksOf` refuses on two sizes of the plan alone, and `planned` itself has called it with
    success (`builtOf`, OnBytes/Model/VerifyStages.lean).
Beside this file: `stFromCall_wordsOf` (Johnson/Flat/InstanceLaws.lean): `Head.stFromCall` returns
at the words of an instance that meets this test, where also the window is below 2 ^ 32 and the
vocabulary at most 2 ^ 32; `sizesAt_planned` (Johnson/Flat/SizesPlanned.lean) gives these two
bounds. That `Head.coveredOf` returns there is not shown in this file.
Limits: `sizesAt policy = .ok P` is a premise on the acceptance policy (exact match). Nothing on
what the links' routines do.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.LinksAt
import OnBytes.Params.ConfigureLaws
import OnBytes.Tie.Pv.Keeps.LinksOrder

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- The window of a parameter file that `sizesAt` takes is not empty. -/
theorem sizesAt_window_pos {policy : ByteArray} {P : Params} (hP : sizesAt policy = .ok P) :
    0 < P.T := by
  unfold sizesAt at hP
  obtain ⟨S, _, hP⟩ := exc_bind hP
  split at hP
  · have e : sizesOf S.h = P := Except.ok.inj hP
    rw [← e]
    exact Nat.two_pow_pos S.h.lt
  · cases hP

/-- The fixed instance from which `pubOf` takes the description's rounds is one that the reader
takes, where the window is not empty. -/
theorem firstInstance_range (P : Params) (hV : 0 < P.V) (hT : 0 < P.T) :
    (firstInstance P hV).r < (firstInstance P hV).e ∧
      ((firstInstance P hV).e < P.T → (firstInstance P hV).y.val = 0) := by
  refine ⟨?_, fun _ => rfl⟩
  show P.T - 1 < P.T
  omega

/-- **The same at the sizes of a parameter file.** -/
theorem firstInstance_range_at {policy : ByteArray} {P : Params} (hP : sizesAt policy = .ok P)
    (hV : 0 < P.V) :
    (firstInstance P hV).r < (firstInstance P hV).e ∧
      ((firstInstance P hV).e < P.T → (firstInstance P hV).y.val = 0) :=
  firstInstance_range P hV (sizesAt_window_pos hP)

/-- What `planned` holds as the built links is what `builtOf` returns. -/
theorem planned_builtOf {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) : builtOf p.X p.chains = .ok p.built := by
  unfold planned at h
  obtain ⟨X, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨ch, _, h⟩ := exc_bind h
  obtain ⟨b, hb, h⟩ := exc_bind h
  cases h
  exact hb

/-- **Where `planned` returns p, `Verify.linksOf p.X` returns at every value of the covered
positions.** -/
theorem linksOf_returns {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) (cov : Head.Covered) :
    ∃ ls, Verify.linksOf p.X cov = .ok ls := by
  have hb := planned_builtOf h
  unfold builtOf at hb
  obtain ⟨ls0, h0, _⟩ := exc_bind hb
  unfold Verify.linksOf at h0 ⊢
  rw [L5.LinksOrder.listLinksH_fold] at h0 ⊢
  simp only [Array.size_mapIdx] at h0 ⊢
  split at h0
  · cases h0
  · rename_i hc
    rw [if_neg hc]
    exact ⟨_, rfl⟩

end OnBytes.Flat
