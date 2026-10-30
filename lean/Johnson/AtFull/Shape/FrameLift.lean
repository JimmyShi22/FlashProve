-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/FrameLift.lean: FROM THE FRAME's TWO PREMISES AT THE CHAIN's SHAPE ALONE TO
THE SAME TWO AT THE WHOLE (the chain's shape with the rows' makes). General laws; nothing is
evaluated.

What it is for. Other files show Carries and Returns at their members for the letters
firstShape guard upd vals, whose type of shapes is ChainSh
(Johnson/Desc/ProofFile/Honest/Thread/ShapeFirst.lean). The first chain's letters at the end are
firstZA g vals, whose type of shapes is ShA (FrameForm.lean). These two laws carry such a file's
work over; nothing is typed anew.

  `liftQ G`: a step on the chain's shape alone, on the whole: the makes stand.
  `LeavesMakes bs ft b`: the member's accepting step leaves the rows' makes. A definition: a
    premise's form.
  **`carries_lift`**: Carries at firstShape, LeavesMakes, and g b = liftQ ‹firstShape's step at b›
    ⊢ Carries at firstZA g vals.
  **`returns_lift`**: Returns at firstShape, that equation, and vals b = vals0 b ⊢ Returns at
    firstZA g vals. No premise on the makes.

Limits. LeavesMakes is shown at no member here: a member that leaves the statement pays it at once.
LeavesMakes asks that the makes stand at every accepting step; carries_lift spends it only where the
step on shapes returns as well: a little more than the conclusion needs. Like Carries, it holds
emptily where no member stands at the number. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FrameForm
import Johnson.Desc.ProofFile.Honest.Thread.ShapeFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest (Shape Carries Returns firstShape)

/-- A step on the chain's shape alone, on the whole: the rows' makes stand. -/
def liftQ (G : ChainSh → Except String ChainSh) (x : ShA) : Except String ShA :=
  (G x.1).map fun a => (a, x.2)

/-- The member's accepting step leaves the rows' makes. -/
def LeavesMakes {Cl : Type} (bs : List (Block S Cl)) (ft b : Nat) : Prop :=
  ∀ blk, bs[b]? = some blk → ∀ s rs cols s' n, blk.step ft s rs cols = .ok (s', n) →
    formsOf s'.st = formsOf s.st

variable {Cl : Type} {bs : List (Block S Cl)} {ft b : Nat}
  {guard : Nat → ChainSh → Bool} {upd : Nat → ChainSh → ChainSh}
  {vals0 vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}
  {g : Nat → ShA → Except String ShA}

/-- **"Carries" at the chain's shape alone gives "Carries" at the whole**, at a member that leaves
the rows' makes. -/
theorem carries_lift (hC : Carries bs ft (firstShape guard upd vals0) b)
    (hk : LeavesMakes bs ft b) (hg : g b = liftQ ((firstShape guard upd vals0).g b)) :
    Carries bs ft (firstZA g vals) b := by
  intro blk hb s rs cols s' n t hs ht
  have ht' : g b (shA s) = .ok t := ht
  rw [hg] at ht'
  unfold liftQ at ht'
  cases ha : (firstShape guard upd vals0).g b (shA s).1 with
  | error e =>
    rw [ha] at ht'
    cases ht'
  | ok a =>
    rw [ha] at ht'
    cases ht'
    have e1 : a = chainSh s' := hC blk hb s rs cols s' n a hs ha
    have e2 := hk blk hb s rs cols s' n hs
    subst e1
    show (chainSh s', formsOf s.st) = (chainSh s', formsOf s'.st)
    rw [e2]

/-- **"Returns" likewise**: no premise on the makes. -/
theorem returns_lift (hR : Returns bs ft (firstShape guard upd vals0) b)
    (hg : g b = liftQ ((firstShape guard upd vals0).g b)) (hv : vals b = vals0 b) :
    Returns bs ft (firstZA g vals) b := by
  intro blk hb s rs cols t ht hF hvv
  have ht' : g b (shA s) = .ok t := ht
  have hvv' : vals b s (rs.map VerifiableInference.Desc.noDigest) (blk.shown ft rs cols) = true :=
    hvv
  rw [hg] at ht'
  rw [hv] at hvv'
  unfold liftQ at ht'
  cases ha : (firstShape guard upd vals0).g b (shA s).1 with
  | error e =>
    rw [ha] at ht'
    cases ht'
  | ok a => exact hR blk hb s rs cols a ha hF hvv'

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.carries_lift
#print axioms Johnson.AtFull.Shape.returns_lift
#print axioms Johnson.AtFull.Shape.liftQ
#print axioms Johnson.AtFull.Shape.LeavesMakes
