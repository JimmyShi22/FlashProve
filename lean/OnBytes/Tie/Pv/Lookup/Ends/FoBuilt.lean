-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBuilt.lean.
The records of the links that were built before: where they come from.

The verifier runs the records of the links that were built from the configuration files alone, each
with the routine of the link at its place in `Verify.linksOf C.X cov`. This file follows these
records back.

 * `common_built`: what the common beginning of the stages holds: the public record, the chains and
   the built links of what `planned` returned on the configuration files.
 * `planned_built`: in what `planned` returns, the public record is `publicOf`'s and the built links
   are `builtOf`'s on that record and these chains.
 * `builtOf_links`: the built links are what `declareLinks` returns on `Verify.linksOf X default`.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLinksOf
import OnBytes.Model.Verify

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages

theorem planned_built {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) :
    publicOf pol KL layout = .ok p.X ∧ builtOf p.X p.chains = .ok p.built := by
  unfold planned at h
  obtain ⟨X, h1, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨chains, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨B, h3, h⟩ := (excBind_ok _ _ _).1 h
  cases h
  exact ⟨h1, h3⟩

theorem common_built {r : Read} {C : Common} (h : commonOfCall r = .ok C) :
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
    · obtain ⟨_, _, h1⟩ := (excBind_ok _ _ _).1 h1
      obtain ⟨_, _, h1⟩ := (excBind_ok _ _ _).1 h1
      cases h1
      exact ⟨p, rfl, rfl, rfl, rfl⟩
    · obtain ⟨_, e, _⟩ := (excBind_ok _ _ _).1 h1
      cases e

theorem builtOf_links {X : Public} {chains : Chains} {B : LinksH}
    (h : builtOf X chains = .ok B) :
    ∃ (l0 : Array LinkH) (declared : Array FrameLink), linksOf X default = .ok l0 ∧
      declareLinks l0 X.NGr X.p4 = .ok (B.links, declared) := by
  unfold builtOf at h
  obtain ⟨l0, h0, h⟩ := (excBind_ok _ _ _).1 h
  unfold buildLinksH at h
  obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨named, declared⟩, h3, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
  split at h
  · exact absurd h (by intro e; cases e)
  · obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (excBind_ok _ _ _).1 h
    cases h
    exact ⟨l0, declared, h0, h3⟩

end Fo
