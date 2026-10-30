-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/QuietK2Sends.lean: KIND K2's TWO TEXTS WITHOUT A ROUND
THAT WRITE THE STATEMENT: headOpenQ_keepsQ · finishFrontQ_keepsQ, at every GroundQuiet R.
CARRIED BY PROGRAM out of Johnson/Top/H0/Tw/K2C/SendsOn.lean:
each declaration that is needed for the top and names GroundKeeps | StKeeps is copied under
its own name with a letter behind it (Q), with GroundQuiet | StQuiet in that word's place; its
docstrings are struck (they are that file's); where a proof opens the word itself it is turned by
hand. THE ORIGINAL IS IMPORTED AND NOT TURNED: what names neither word is called from it. IF THE
ORIGINAL ITSELF IS WIDENED INSTEAD, THIS FILE FALLS.
BENEATH: Johnson/ToldDescR/K2KeepsQuiet.lean (a port of
Johnson/Top/H0/Tw/K2C/Keeps.lean to GroundQuiet).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H0.Tw.K2C.SendsOn
import Johnson.Desc.GroundQuiet
import Johnson.ToldDescR.K2KeepsQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront)
open VerifiableInference.Desc.Ground (GroundKeeps GroundQuiet)

variable {R : Statement → Statement → Prop}

theorem headOpenQ_keepsQ (H : GroundQuiet R) {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    R s.st s'.st := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  rw [k.out']
  exact firstBehind_keepsQ H k.behind

theorem finishFrontQ_keepsQ (H : GroundQuiet R) {s s' : S} (h : finishFrontQ s = .ok s') : R s.st
    s'.st := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s s').1 h
  rw [k.out]
  exact finishFront_keepsQ H k.front

end VerifiableInference.Desc.First.K2
