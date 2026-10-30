-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ReplyHear.lean: the list of tokens in what `Head.hear` returns. For proofs only; the
program does not import this file.

  `replyToken_ok`: where `Head.replyToken` returns, it returns `tokenOf`
    (OnBytes/K/ReplyToken.lean).
  `hear_win`: from whatever states `Head.hear` (OnBytes/Model/HeadHeard.lean) returns x on the plain
    scalars `plain`: the field `x.win` is `winOf cov h.T (tokenOf plain)`.
What is not claimed: that the head's routine calls `hear`, and on which scalars:
OnBytes/K/HeadSplit.lean has that.


-/
import OnBytes.K.ReplyToken
import OnBytes.Cut.Binds
import OnBytes.Model.HeadHeard

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model
open OnBytes.Cut (bindS)

/-- Where `replyToken` returns, it returns `tokenOf`. -/
theorem replyToken_ok {plain : Array E} {V : Nat} {F F' : Fork} {c c' : Ctx} {y : Nat}
    (h : Head.replyToken plain V F c = .ok ((y, F'), c')) : y = tokenOf plain := by
  rw [replyToken_eq] at h
  obtain ⟨_, _, _, _, h⟩ := bindS h
  obtain ⟨_, _, _, _, h⟩ := bindS h
  cases h
  rfl

/-- Where `hear` returns, the list of checked tokens is `winOf` at `tokenOf plain`. -/
theorem hear_win {h : Head.Shape} {L : Head.HL} {hp : Head.HPlanH2} {cov : Head.Covered}
    {plain : Array E} {F F' : Fork} {c c' : Ctx} {x : Head.Heard}
    (hr : Head.hear h L hp cov plain F c = .ok ((x, F'), c')) :
    x.win = Head.winOf cov h.T (tokenOf plain) := by
  unfold Head.hear at hr
  obtain ⟨yTok, _, _, hy, hr⟩ := bindS hr
  have ey := replyToken_ok hy
  subst ey
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨g1, _, _, _, hr⟩ := bindS hr
  obtain ⟨Zl, _, _, _, hr⟩ := bindS hr
  obtain ⟨PV, _, _, _, hr⟩ := bindS hr
  obtain ⟨⟨sW, gp, wpl⟩, _, _, _, hr⟩ := bindS hr
  obtain ⟨⟨sPv, omV, tV⟩, _, _, _, hr⟩ := bindS hr
  obtain ⟨qN, _, _, _, hr⟩ := bindS hr
  obtain ⟨qH, _, _, _, hr⟩ := bindS hr
  obtain ⟨tN, _, _, _, hr⟩ := bindS hr
  obtain ⟨⟨tH, rs⟩, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  obtain ⟨_, _, _, _, hr⟩ := bindS hr
  cases hr
  rfl

end OnBytes.K
