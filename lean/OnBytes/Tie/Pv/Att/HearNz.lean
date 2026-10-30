-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Att/HearNz.lean: in the stages that the port's routines for an attention sub-proof's
own messages have heard (OnBytes/Tie/Pv/Att/HearStages.lean), the reading of each sumcheck's beta is
not 0, from one premise on the context at which the stages begin.

Main names:
  AllNz ρ st: the reading of beta is not 0 at each sumcheck among the stages st.
  heard_nz: if the stages were heard from a context with NzCtx ρ
    (OnBytes/Tie/Pv/Psc/Run/NzCtx.lean), then AllNz ρ st, and the context that is left has NzCtx ρ.

Limits: NzCtx ρ at the first context is a premise, and it is proved nowhere in this library: it says
of a view that what its rounds have drawn under the rule that never gives 0 does not read as 0.
-/
import OnBytes.Tie.Pv.Att.HearStages
import OnBytes.Tie.Pv.Psc.Run.NzRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Road

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The reading of beta is not 0 at each sumcheck among the stages. -/
def AllNz : List StageH → Prop
  | [] => True
  | .sum _ _ _ H :: l => ρ.val H.beta ≠ 0 ∧ AllNz l
  | .bat _ _ _ :: l => AllNz l
  | .point _ :: l => AllNz l

theorem heard_nz : ∀ (st : List StageH) (c c' : Ctx), HeardAs st c c' → NzCtx ρ c →
    AllNz ρ st ∧ NzCtx ρ c'
  | [], c, c', h, hc => by
    rw [show c' = c from h]
    exact ⟨trivial, hc⟩
  | .sum riders ws dY H :: l, c, c', h, hc => by
    obtain ⟨c1, c2, h1, h2⟩ := h
    obtain ⟨a1, a2⟩ := parts_nz ρ h1 hc
    obtain ⟨b1, b2⟩ := heard_nz l c2 c' h2 a2
    exact ⟨⟨a1, b1⟩, b2⟩
  | .bat sent rows x :: l, c, c', h, hc => by
    obtain ⟨c1, c2, c3, h1, h2, h3, h4⟩ := h
    exact heard_nz l c3 c' h4 (keeps_requireRows ρ _ _ _ _
      (keeps_closeOne ρ _ _ _ _ _ _ (keeps_recvEs ρ _ _ _ _ hc h1) h2) h3)
  | .point d :: l, c, c', h, hc => by
    obtain ⟨c1, h1, h2⟩ := h
    exact heard_nz l c1 c' h2 (keeps_close ρ _ _ _ _ _ _ hc h1)

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.heard_nz
