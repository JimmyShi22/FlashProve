-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/Built.lean: the links as built, in the record that the stages of a call share, are what
the program's own function makes of the public part and the chains in that same record.

"The program" is the Lean program verify-on-bytes. Model.Verify.planned computes all that follows
from the three configuration files; Model.Verify.commonOfCall hands its public part, its chains and
its links as built on to the stages. Statements on the list of links that the stage request runs
take as a premise that the links as built are what Model.Verify.builtOf returns. This file proves
that premise for every call.

Main theorems: planned_built, commonOfCall_same, common_built.
It claims nothing on soundness. The program does not import this file.

-/
import OnBytes.Model.VerifyLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK

open OnBytes.Params (exc_bind)
open OnBytes.Model.Verify

/-- What planned returns holds the links that builtOf makes of its public part and its chains. -/
theorem planned_built {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) : builtOf p.X p.chains = .ok p.built := by
  unfold planned at h
  obtain ⟨X, _, h1⟩ := exc_bind h
  dsimp only at h1
  obtain ⟨chains, _, h2⟩ := exc_bind h1
  obtain ⟨b, hb, h3⟩ := exc_bind h2
  cases h3
  exact hb

/-- The record that the stages share holds the plan's public part, chains and links as built. -/
theorem commonOfCall_same {r : Read} {C : Common} (h : commonOfCall r = .ok C) :
    ∃ p : Planned, planned r.pol r.KL r.layout = .ok p ∧ C.X = p.X ∧ C.chains = p.chains ∧
      C.built = p.built := by
  unfold commonOfCall at h
  cases hp : planned r.pol r.KL r.layout with
  | error n =>
    rw [hp] at h
    cases h
  | ok p =>
    rw [hp] at h
    have h1 : commonOf p.X p.cfg p.chains p.built r.key r.id.asked = .ok C := h
    unfold commonOf at h1
    dsimp only at h1
    split at h1
    · obtain ⟨first, h2, h3⟩ := exc_bind h1
      cases h2
      obtain ⟨_, _, h4⟩ := exc_bind h3
      cases h4
      exact ⟨p, rfl, rfl, rfl, rfl⟩
    · obtain ⟨_, h2, _⟩ := exc_bind h1
      cases h2

/-- **The premise, for every call.** -/
theorem common_built {r : Read} {C : Common} (h : commonOfCall r = .ok C) :
    builtOf C.X C.chains = .ok C.built := by
  obtain ⟨p, hp, e1, e2, e3⟩ := commonOfCall_same h
  rw [e1, e2, e3]
  exact planned_built hp

end OnBytes.TieK
