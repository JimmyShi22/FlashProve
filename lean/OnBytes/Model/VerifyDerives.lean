-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyDerives.lean: how the parameter bytes of an entry file's chain follow from the
three configuration files.

`planned` (OnBytes/Model/Verify.lean) computes all that a call derives from the three configuration
files, the parameter bytes of the seven chains among it. This file proves which simpler function
gives those of the entry's chain: `Params.entryParams`, on what `Params.readLines` reads from the
parameter file, by its description the first 32 lines, and on the digest of the three files, which
by the code (no theorem) takes in every byte of all three.

Main theorem. `planned_entry`: if `planned` returns p on the files pol, KL and lay, then
`Params.readLines` reads lines l from pol, the digest in p is
`Params.configurationDigest [pol, lay, KL]`, and `Params.entryParams` on l and that digest returns
the parameter bytes of the entry's chain in p. `planned_entryBytes` says the same in one equation,
with `Params.entryBytesOf`.

What is not claimed. Nothing on soundness, and nothing on the planner's bounds. The converse is not
stated: `Params.entryParams` can return bytes where `planned` refuses. Nothing is said of the other
six chains. `Params.entryParams` is code of OnBytes/Params/Derive.lean: no theorem says that it is
the format's or the C++ programs' derivation, and tests alone compare its bytes with theirs, at
stored lines and digests. For proofs only; the program does not import this file.
-/
import OnBytes.Model.VerifyLaws
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false

namespace OnBytes.Model

open OnBytes.Params (exc_bind)

/-- The lines in a scan of the parameter file are those that `Params.readLines` reads from it. -/
theorem polScan_frame {pol : ByteArray} {P : PolScan} (h : polScan pol = .ok P) :
    ∃ rest, Params.readLines pol = .ok (P.frame, rest) := by
  unfold polScan at h
  cases hr : Params.readLines pol with
  | error e =>
    rw [hr] at h
    cases h
  | ok x =>
    rw [hr] at h
    obtain ⟨frame, rest⟩ := x
    refine ⟨rest, ?_⟩
    have e : P.frame = frame := by
      dsimp only at h
      obtain ⟨w, hw, h⟩ := exc_bind h
      cases hw
      repeat' first
        | (obtain ⟨_, _, h⟩ := exc_bind h)
        | (split at h)
      all_goals first
        | (cases h; rfl)
        | cases h
    rw [e]

namespace Verify

/-- The scan in what `polLayout` returns is the scan of the parameter file. -/
theorem polLayout_scan {pol : ByteArray} {P : PolScan} {y : Layer.Lay}
    (h : polLayout pol = .ok (P, y)) : polScan pol = .ok P := by
  unfold polLayout at h
  obtain ⟨P0, h0, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  exact h0

/-- The scan in the public part is the scan of the parameter file. -/
theorem publicOf_scan {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf pol KL layout = .ok X) : polScan pol = .ok X.P := by
  unfold publicOf at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  have e : X.P = P := by
    dsimp only at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := exc_bind h)
      | (split at h)
    all_goals first
      | (cases h; rfl)
      | cases h
  rw [e]
  exact polLayout_scan h0

/-- What the chains hold as made is what `Params.configure` returns on the lines of the public part,
some shapes, the digest and 0 bits. -/
theorem chainsOf_made {X : Public} {layout : Option ByteArray} {cfg : ByteArray} {c : Chains}
    (h : chainsOf X layout cfg = .ok c) :
    ∃ shapes, Params.configure X.P.frame shapes cfg 0 = .ok c.made := by
  unfold chainsOf at h
  obtain ⟨⟨_, shapes⟩, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  split at h
  · cases h
    exact ⟨shapes, hm⟩
  · cases h

/-- If `planned` returns p on the three configuration files, then `Params.readLines` reads lines l
from the parameter file, the digest in p is that of the three files, the parameter file first and
the layout file second, and `Params.entryParams` on l and that digest returns the parameter bytes of
the entry's chain in p. -/
theorem planned_entry {pol KL lay : ByteArray} {p : Planned}
    (h : planned pol KL (some lay) = .ok p) :
    ∃ l rest, Params.readLines pol = .ok (l, rest) ∧
      p.cfg = Params.configurationDigest [pol, lay, KL] ∧
      Params.entryParams l (Params.configurationDigest [pol, lay, KL]) =
        .ok (p.chains.bytes .link) := by
  unfold planned at h
  obtain ⟨X, hX, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨chains, hc, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  obtain ⟨rest, hr⟩ := polScan_frame (publicOf_scan hX)
  obtain ⟨shapes, hm⟩ := chainsOf_made hc
  exact ⟨X.P.frame, rest, hr, rfl, Params.configure_entry hm⟩

/-- The same in one equation: the parameter bytes of the entry's chain in p are
`Params.entryBytesOf` of the three files. -/
theorem planned_entryBytes {pol KL lay : ByteArray} {p : Planned}
    (h : planned pol KL (some lay) = .ok p) :
    Params.entryBytesOf pol lay KL = some (p.chains.bytes .link) := by
  obtain ⟨l, rest, h1, _, h2⟩ := planned_entry h
  unfold Params.entryBytesOf
  rw [h1]
  show (Params.entryParams l (Params.configurationDigest [pol, lay, KL])).toOption = _
  rw [h2]
  rfl

end Verify

end OnBytes.Model

#print axioms OnBytes.Model.Verify.planned_entry
#print axioms OnBytes.Model.Verify.planned_entryBytes
