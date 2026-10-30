-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/HeadShapeOfSettings.lean: where the planner's `publicOf` returns X on the public files
and `settingsAtRef` returns pp, the head's shape `X.hS` holds the C, theta and cap of `pp.pol`, with
sh = 8, sT = 4, F = 24.

Purpose. pol is a parameter file's bytes, KL a scale file's, layout a layout file's, if there is
one. `publicOf pol KL layout` (OnBytes/Model/VerifyPublic.lean) is a function of the public files
alone. Among what it returns is the record `X.hS`, which holds the acceptance policy's numbers for
the head's check. `settingsAtRef pol KL` (Johnson/Flat/SettingsAtRef.lean) gives the integer model's
settings pp, of whose policy `pp.pol` (`AcceptancePolicy`, Inst/Model/ProgramR.lean) a claim under a policy
speaks. Both read the same scan of pol (`polScan`, OnBytes/Model/Config.lean). One statement and its
proof, over these files alone.

Main name:
  `hS_of_settings`: under `publicOf pol KL layout = .ok X` and `settingsAtRef pol KL = .ok pp`:
    `X.hS` has as clipC, theta, cap those of `pp.pol`, and digSh = 8, tabS = 4, famF = 24. By
    `publicOf_cut` (OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean): `X.hS` is `headShape` of `X.P`, which
    copies the seven lines.

Limits. It says which numbers the record holds: not that any check reads or enforces them, and
nothing on a protocol or on soundness. Of the policy's seven lines three are tied to pp, three are
the same numbers at every file at which `settingsAtRef` returns, and the line s is tied to nothing
here. `Head.layout` (OnBytes/Model/HeadLayout.lean) reads all six fields while `publicOf` runs; that
`X.HLy` and `X.H` are made of this `X.hS` is not said here. `publicOf` hashes with the earlier mode,
a fixed function, at several places of its text, and on the tables' digests it hangs whether it
returns: so that `publicOf` returns is a statement about that fixed function. That `publicOf` and
`settingsAtRef` both return at any files is no theorem. The limits in the head of
Johnson/Flat/SettingsAtRef.lean hold here too. Of Lean's own text; nothing here is about the C++
programs.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.SettingsAtRef
import OnBytes.Model.VerifyDerives
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales here: each table is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

open OnBytes.Model

/-- **Where, at the same two files, `settingsAtRef` returns settings pp and `publicOf` returns a
public part X, the record `X.hS` has the C, theta and cap of `pp.pol`**, and digSh = 8, tabS = 4,
famF = 24. It says which numbers are handed to the head's check, not that the check enforces them.
-/
theorem hS_of_settings {pol KL : ByteArray} {layout : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} {pp : Inst.Model.ScalesAndPolicy}
    (hX : OnBytes.Model.Verify.publicOf pol KL layout = .ok X)
    (h : OnBytes.Flat.settingsAtRef pol KL = .ok pp) :
    X.hS.clipC = pp.pol.C ∧ X.hS.theta = pp.pol.theta ∧ X.hS.cap = pp.pol.cap ∧
      X.hS.digSh = 8 ∧ X.hS.tabS = 4 ∧ X.hS.famF = 24 := by
  obtain ⟨S, hS, h8, h4, hF, hp⟩ := settingsAtRef_lines h
  have e : X.P = S := by
    have := (OnBytes.Model.Verify.publicOf_scan hX).symm.trans hS
    exact Except.ok.inj this
  rw [(Fo.Pub.publicOf_cut pol KL layout X hX).2.1, hp]
  show X.P.h.clipC = _ ∧ X.P.h.theta = _ ∧ X.P.h.cap = _ ∧ X.P.h.digSh = 8 ∧
    X.P.h.tabS = 4 ∧ X.P.h.famF = 24
  rw [e]
  exact ⟨rfl, rfl, rfl, h8, h4, hF⟩

end OnBytes.Flat

#print axioms OnBytes.Flat.hS_of_settings
