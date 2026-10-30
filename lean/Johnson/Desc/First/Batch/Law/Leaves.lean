-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Leaves.lean
(kind K9's small law on the reply): THEOREMS: K9's blocks, at the state S that the
proof file's first chain carries, LEAVE THE REPLY THAT WAS HEARD AS IT WAS: Block.Leaves S.heard
(Johnson/Desc/Sound/FoldHeard.lean; the reading: Johnson/Desc/First/StateHeard.lean).
  heard_set          the lens's writing (Batch/AtS.lean: atS.set) leaves the reading.
  leaves_drawAlone   the draw's block.
  leaves_oneEquation the equation's block.
  leaves_adds, leaves_batch   the adding's block and the batching's, UNDER A NAMED PREMISE ON THE
                     FUNCTION OF CLAIMS: where it returns, the state that it returns has the same
                     reading (the runs are other kinds').
The law runs over all records in front, also those that no run reaches: outside a segment K9's
blocks refuse ("K9.in-a-segment"); they mark nothing.
Not here: the block that shuts a segment (Batch/Place.lean), and the joint with the closing.

-/
import Johnson.Desc.Sound.FoldHeard
import Johnson.Desc.First.StateHeard
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Batch.Law.AtBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where drawAlone adds batch oneEquation)
open VerifiableInference.Desc.First (S)

/-- The lens's writing leaves the reply that was heard. -/
theorem heard_set (s : S) (p : K9.Part) : (atS.set s p).heard = s.heard := by
  have h1 : (atS.set s p).heard = ((s.putLink p.L).putFork p.F).heard :=
    S.heard_of_same _ _ rfl rfl
  rw [h1, S.heard_putFork, S.heard_putLink]

theorem leaves_drawAlone {Cl : Type} (p : Where) :
    Block.Leaves S.heard (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [drawAlone] at h
  match rs, h with
  | [r], h =>
    obtain ⟨a, _, h⟩ := ok_bind h
    obtain ⟨chi, _, h⟩ := ok_bind h
    obtain ⟨o, _, h⟩ := ok_bind h
    rw [← Except.ok.inj h]
    exact heard_set s _

theorem leaves_oneEquation {Cl : Type} (p : Where) :
    Block.Leaves S.heard (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨a, _, h⟩ := ok_bind h
  obtain ⟨o, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  exact heard_set s _

theorem leaves_adds {Cl : Type} (p : Where) (piece : Nat) (what : String)
    (claims : S → Except String (List Claim × S))
    (hc : ∀ s x, claims s = .ok x → x.2.heard = s.heard) :
    Block.Leaves S.heard (adds (Cl := Cl) atS p piece what claims) := by
  intro s rs gs s' h
  simp only [adds] at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨b, _, h⟩ := ok_bind h
  obtain ⟨G, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h, heard_set]
  exact hc s x hx

theorem leaves_batch (p : Where) (claims : S → Except String (List Claim × S))
    (hc : ∀ s x, claims s = .ok x → x.2.heard = s.heard) :
    Block.Leaves S.heard (batch atS p claims) := by
  intro s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h2⟩ := ok_bind h
  rw [leaves_adds p p.piece "the segment's" claims hc t₁ [] [] s' h2,
    leaves_drawAlone p s rs gs t₁ h1]

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.heard_set
#print axioms VerifiableInference.Desc.K9L.leaves_drawAlone
#print axioms VerifiableInference.Desc.K9L.leaves_oneEquation
#print axioms VerifiableInference.Desc.K9L.leaves_adds
#print axioms VerifiableInference.Desc.K9L.leaves_batch
