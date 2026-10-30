-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/PlannedParts.lean: what the program computes from the three configuration files
(`Verify.planned`, OnBytes/Model/Verify.lean), taken apart by name: the public part, the parameter
file's lines, the shapes that the planner is handed, the planner's yes and two of the three readers'
answers.

Main names (namespace OnBytes.Model.Verify):
  `publicOf_lines`: the lines in the public part of what `publicOf` returns are those that
    `Params.readLines` reads off the parameter file (by `polScan_frame` and `publicOf_scan`,
    OnBytes/Model/VerifyDerives.lean).
  `shapesOf_sub`: the sub-proofs' record in the shapes is `subproofsWith X` at the list of links
    that `Plan.reqFrame` returns: so its rounds are `linkRounds X`, and nothing is sent after the
    links.
  `chainsOf_parts`: from `chainsOf`'s yes: the shapes by name, the planner's yes at X's lines and
    these shapes, and the answers of the key's and the proof's readers on its bytes.
  `planned_parts`: these from `planned`'s yes, at X := p.X.
Under "there is": the rest of the parameter file behind its lines; the links and the shapes, fixed
by `shapesOf`'s equation; the declared arrays and the layout file as read, of which nothing more is
said; the frame's links and layout, fixed by `Plan.reqFrame`'s equation at these two.
The walks use `Fo.BatRows.bindE_ok` (OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean) and
`Fo.Pub.ite_unit_ok` (FoPublic.lean).

Limits: one direction: from a routine that returns; that `planned` returns at any files is shown by
no term here. Left out of `planned_parts`, though `planned`'s text has them: that p.cfg is the
digest of the three files; the entry's reader's answer; the yes of `Params.sized`, `linksFit` and
`builtOf`; the layout in the shapes; whence the declared arrays and the layout file as read come.
Nothing on what the numbers are. Nothing on soundness. The program does not import this file.

-/
import OnBytes.Model.VerifyDerives
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify

open Fo.BatRows (bindE_ok)
open Fo.Pub (ite_unit_ok)

/-- **The lines in the public part are the parameter file's.** -/
theorem publicOf_lines {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf pol KL layout = .ok X) :
    ∃ rest, Params.readLines pol = .ok (X.P.frame, rest) :=
  polScan_frame (publicOf_scan h)

/-- The sub-proofs' record in the shapes. -/
private theorem shapesWith_sub {X : Public} {links : List Params.ReqLink}
    {layout : Params.ReqLayout} {ids : List Nat} {s : Params.Shapes}
    (h : shapesWith X links layout ids = .ok s) :
    s.sub = subproofsWith X links := by
  unfold shapesWith at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  rfl

/-- The same from `shapesOf`. -/
theorem shapesOf_sub {X : Public} {lay : Option ByteArray} {links : Array Stages.LinkH}
    {shapes : Params.Shapes} (h : shapesOf X lay = .ok (links, shapes)) :
    ∃ declared file rl layout,
      Plan.reqFrame declared file X.P.frame.answers = some (rl, layout) ∧
        shapes.sub = subproofsWith X rl := by
  unfold shapesOf at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨⟨links', declared⟩, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨file, _, h⟩ := bindE_ok h
    split at h
    · rename_i x hx
      obtain ⟨⟨reqLinks, layout⟩, ex, h⟩ := bindE_ok h
      have e0 : x = (reqLinks, layout) := Except.ok.inj ex
      dsimp only at h
      obtain ⟨s, hs, h⟩ := bindE_ok h
      have e : (links', s) = (links, shapes) := Except.ok.inj h
      rw [← (Prod.mk.inj e).2]
      exact ⟨declared, file, reqLinks, layout, hx.trans (congrArg some e0), shapesWith_sub hs⟩
    · obtain ⟨_, e, _⟩ := bindE_ok h
      cases e
  · obtain ⟨_, e, _⟩ := bindE_ok h
    cases e

/-- From `chainsOf`'s yes. -/
theorem chainsOf_parts {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : chainsOf X lay c = .ok ch) :
    ∃ links shapes, shapesOf X lay = .ok (links, shapes) ∧
      Params.configure X.P.frame shapes c 0 = .ok ch.made ∧
      Params.KeyChains.read ch.made.keyOneTime ch.made.keyShared ch.made.keySecond = some ch.key ∧
      Params.ProofChains.read ch.made.first ch.made.shared ch.made.second = some ch.proof := by
  unfold chainsOf at h
  obtain ⟨⟨links, shapes⟩, hs, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨z, _, h⟩ := bindE_ok h
  obtain ⟨u, _, h⟩ := bindE_ok h
  obtain ⟨made, hm, h⟩ := bindE_ok h
  split at h
  · rename_i key link proof hK hL hP
    cases h
    exact ⟨links, shapes, hs, hm, hK, hP⟩
  · cases h

/-- **What `planned` returns, taken apart by name.** -/
theorem planned_parts {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) :
    ∃ links shapes rest declared file rl lay,
      publicOf pol KL layout = .ok p.X ∧
      Params.readLines pol = .ok (p.X.P.frame, rest) ∧
      shapesOf p.X layout = .ok (links, shapes) ∧
      shapes.sub.plan = linkRounds p.X ∧
      shapes.sub.afterLinks = pure () ∧
      Params.configure p.X.P.frame shapes p.cfg 0 = .ok p.chains.made ∧
      Params.KeyChains.read p.chains.made.keyOneTime p.chains.made.keyShared
        p.chains.made.keySecond = some p.chains.key ∧
      Params.ProofChains.read p.chains.made.first p.chains.made.shared p.chains.made.second =
        some p.chains.proof ∧
      Plan.reqFrame declared file p.X.P.frame.answers = some (rl, lay) ∧
      shapes.sub = subproofsWith p.X rl := by
  unfold planned at h
  obtain ⟨X, hX, h⟩ := bindE_ok h
  obtain ⟨ch, hc, h⟩ := bindE_ok h
  obtain ⟨b, _, h⟩ := bindE_ok h
  cases h
  obtain ⟨links, shapes, hs, hm, hK, hP⟩ := chainsOf_parts hc
  obtain ⟨rest, hr⟩ := publicOf_lines hX
  obtain ⟨declared, file, rl, lay, hf, e⟩ := shapesOf_sub hs
  exact ⟨links, shapes, rest, declared, file, rl, lay, hX, hr, hs, by rw [e]; rfl, by rw [e]; rfl,
    hm, hK, hP, hf, e⟩

end OnBytes.Model.Verify

#print axioms OnBytes.Model.Verify.publicOf_lines
#print axioms OnBytes.Model.Verify.shapesOf_sub
#print axioms OnBytes.Model.Verify.chainsOf_parts
#print axioms OnBytes.Model.Verify.planned_parts
