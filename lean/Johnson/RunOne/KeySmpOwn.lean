-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySmpOwn.lean: ROW 1.1's CONDITION ON THE READING, SmpOwn (KeySendYes1.lean), IS MET AT EVERY BaseSt's FIRST READING B.h₁ under three facts on the base: ArrOk at the table's messages 0 | 1 | 2 · B.orc₁ is the plan's orc (AtFk's field) · B.SmGroups (the letter sm does not read a message's list of groups: KeyLettersAt.lean:21; a filling has it with no premise: smGroupsK, in KeyFillSeed.lean).
OBJECT: SmpOwn B.h₁ at_ one · USER: Left11.smpOwn (and the like field at every later sending of the first chain) · LETTERS: B at_ one.
  orc_le        PROVED: the plan names a number for the table's messages 0 | 1 | 2 alone
  smpOwn_base   PROVED
Nothing on soundness.
-/
import Johnson.RunOne.KeySendYes1
import Johnson.RunOne.KeyLettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23 (BaseSt)

theorem orc_le (one : OneTime) (k o : Nat) (h : (plan₁ one).orc k = some o) : k ∈ [0, 1, 2] := by
  have h' : (if k == 0 then some 0 else if k == 1 then some 1 else if k == 2 then some (1 + 2 * one.ranges.stages.length) else none) = some o := h
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h2 : k = 2
      · subst h2; simp
      · simp [h0, h1, h2] at h'

theorem smpOwn_base {Cells M Smp Rec : Type} (B : BaseSt Cells M Smp Rec) (at_ : Where) (one : OneTime)
    (hA : ArrOk B.h₁ at_ [0, 1, 2]) (ho : B.orc₁ = (plan₁ one).orc) (hg : B.SmGroups) : SmpOwn B.h₁ at_ one := by
  intro p s s' k o x gs hk hc hx hx'
  have ha : B.arr (at_ k).1 (at_ k).2 = k := hA k (orc_le one k o hk)
  show (B.orc₁ (B.arr (at_ k).1 (at_ k).2)).bind (B.smAt s'.d.st) = (B.orc₁ (B.arr (at_ k).1 (at_ k).2)).bind (B.smAt s.d.st)
  rw [ha, ho, hk]
  show B.smAt s'.d.st o = B.smAt s.d.st o
  unfold BaseSt.smAt
  rw [hx', hx, hc]
  exact hg _ _ _ _

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.smpOwn_base
