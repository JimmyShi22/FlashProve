-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/PublicAtBaseScope.lean: two more of the library's lemmas that open the text of
the public part of a stage (`publicOf`, OnBytes/Model/VerifyPublic.lean), each once more at the text
that takes the second hash function as an argument o (`publicOfO o`,
Johnson/Desc/Ok/PlanWritten/PublicAt.lean).

What is here. `Pub34Scope.more_of_publicO` (Johnson/Goal/Meaning/Pub34Scope.lean) and
`ScopeAtPlan.publicOf_wsLayO` (Johnson/Goal/PlanValues/ScopeAtPlan.lean): the statement and the
proof are the library's, line for line, with `publicOfO o` for `publicOf`. They were made by a
program from the library's text. They stand apart from their eighteen fellows
(Johnson/Desc/Ok/PlanWritten/PublicAtBase.lean) because their source files import the goals.

The statements are tools: they hold of all public files and all arguments o; the scope is named in
neither, and no description of the protocol is named. What of OnBytes/Model/ is used: what the
library's two lemmas use.

Limits. As in Johnson/Desc/Ok/PlanWritten/PublicAtBase.lean. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAtCut
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Goal.PlanValues.ScopeAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

section
open Meaning Meaning.P34
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Scales Reads layout layoutBase takeCalls takeSegments
  segmentList builtInCalls scalesHeld readsOf tailsOf ropeOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (fams used)

/-- At o: Five more lines of the public part, on its own results. -/
theorem Pub34Scope.more_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL lay = .ok X) :
    readsOf X.y = .ok X.layers.rd ∧
      X.layers.tails = tailsOf X.y ∧ ropeOf X.y.h = .ok X.layers.rope ∧
      Layer.Pub.of X.y X.layers.sc X.layers.rope X.layers.wsLay X.P.h.V #[] X.P.settings =
        .ok X.layers ∧ Layer.plansG X.layers = .ok X.G := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := Hd.ok_of_either h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := Hd.ok_of_either2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  obtain ⟨e1, e2, e3, e4, e5⟩ := pub_more (by assumption)
  obtain ⟨-, e6⟩ := Hd.pub_fields (by assumption)
  unfold Model.Verify.Public.y
  dsimp only
  rw [e1, e2, e4, e5, e6]
  exact ⟨e3, rfl, by assumption, by assumption, by assumption⟩

end

section
open Lk6 Lk6.AtPlan
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind recordLines)
open OnBytes.K.Left (keeps_lines toList_data)
open OnBytes.K.Left.TestSaysLines (full32)

/-- At o: The layout of the committed matrix in the public part is made from the scan and the
layers' layout. -/
theorem ScopeAtPlan.publicOf_wsLayO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL layout = .ok X) :
    ∃ y, polLayout pol = .ok (X.P, y) ∧
      wsLayOf (weightShape X.P y) y.h.p3 X.P.lkW = .ok X.layers.wsLay := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨sc, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  have h := Fo.Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨ws, hws, h⟩ := exc_bind h
  obtain ⟨rope, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨HLy, _, h⟩ := exc_bind h
  have key : ∃ layers, Layer.Pub.of y sc rope ws P.h.V #[] P.settings = .ok layers ∧
      X.P = P ∧ X.layers = layers := by
    split at h
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨layers, hlay, h⟩ := exc_bind h
      refine ⟨layers, hlay, ?_⟩
      repeat' first
        | (obtain ⟨_, _, h⟩ := exc_bind h)
        | (cases h; exact ⟨rfl, rfl⟩)
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨layers, hlay, h⟩ := exc_bind h
      refine ⟨layers, hlay, ?_⟩
      repeat' first
        | (obtain ⟨_, _, h⟩ := exc_bind h)
        | (cases h; exact ⟨rfl, rfl⟩)
  obtain ⟨layers, hlay, e1, e2⟩ := key
  rw [e1, e2, pubOf_wsLay hlay]
  exact ⟨y, h0, hws⟩

end

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.Pub34Scope.more_of_publicO
#print axioms VerifiableInference.PlanWritten.ScopeAtPlan.publicOf_wsLayO
