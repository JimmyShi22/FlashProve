-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/LeavesClose.lean
(kind K9's small law on the reply): THEOREMS: WHAT CLOSES A SEGMENT
(Batch/Place.lean), at the state S that the proof file's first chain carries, LEAVES THE REPLY THAT
WAS HEARD AS IT WAS: Block.Leaves S.heard (Johnson/Desc/Sound/FoldHeard.lean).
  heard_putRec     the writing back of K10's part (putRec) leaves the reading.
  leaves_closing   K10's block at S: whatever the kind decides: by the writing back alone.
  leaves_shut      the block that marks the segment's book-keeping as shut.
  leaves_andThen   two blocks as one (general).
  leaves_closeOf   each of the three blocks of closeOf p P.
  leaves_joint     the three as one block (joint p P).
No premise. The law runs over all records in front, also those that no run reaches.

-/
import Johnson.Desc.First.Batch.Place
import Johnson.Desc.First.Batch.Law.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where oneEquation recOf putRec closing shut closeOf joint)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par Rec)

variable {Cl : Type}

/-- The writing back of K10's part leaves the reply that was heard. -/
theorem heard_putRec (s : S) (r : Rec) : (putRec s r).heard = s.heard := by
  have h1 : (putRec s r).heard = (s.putLive { s.live with frame := r.frame }).heard :=
    S.heard_of_same _ _ rfl rfl
  rw [h1, S.heard_putLive]

theorem leaves_closing (P : Par) : Block.Leaves S.heard (closing (Cl := Cl) P) := by
  intro s rs gs s' h
  have h' : ((First.Close.kind (Cl := Cl) P).decide (recOf s) rs gs).map (putRec s) = .ok s' := h
  cases hq : (First.Close.kind (Cl := Cl) P).decide (recOf s) rs gs with
  | error e =>
    rw [hq] at h'
    exact nomatch h'
  | ok r =>
    rw [hq] at h'
    have e : putRec s r = s' := Except.ok.inj h'
    rw [← e]
    exact heard_putRec s r

theorem leaves_shut (p : Where) (piece : Nat) :
    Block.Leaves S.heard (shut (Cl := Cl) p piece) := by
  intro s rs gs s' h
  simp only [shut] at h
  obtain ⟨L, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  exact S.heard_putLink _ _

/-- Two blocks as one. -/
theorem leaves_andThen {T α : Type} (f : T → α) (name : String) (p q : Block T Cl)
    (hp : p.Leaves f) (hq : q.Leaves f) : (Block.andThen name p q).Leaves f := by
  intro s rs gs s' hd
  have hd' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun t =>
      q.decide t (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := hd
  cases h1 : p.decide s (rs.take p.rounds.length) (gs.take p.openings) with
  | error e =>
    rw [h1] at hd'
    exact nomatch hd'
  | ok t =>
    rw [h1] at hd'
    exact (hq _ _ _ _ hd').trans (hp _ _ _ _ h1)

/-- **Each of the three blocks that close a segment.** -/
theorem leaves_closeOf (p : Where) (P : Par) :
    ∀ b ∈ closeOf (Cl := Cl) p P, b.Leaves S.heard := by
  intro b hb
  simp only [closeOf, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact fun s rs gs s' h => leaves_oneEquation (Cl := Cl) p s rs gs s' h
  · exact leaves_closing P
  · exact leaves_shut p _

/-- **The three as one block.** -/
theorem leaves_joint (p : Where) (P : Par) : Block.Leaves S.heard (joint (Cl := Cl) p P) :=
  fun s rs gs s' h =>
    leaves_andThen S.heard s!"the one equation and the closing of segment {p.link}" _ _
      (leaves_andThen S.heard "the one equation and the closing" _ _
        (leaves_oneEquation (Cl := Cl) p) (leaves_closing P))
      (leaves_shut p (P.piece + 1)) s rs gs s' h

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.heard_putRec
#print axioms VerifiableInference.Desc.K9L.leaves_closing
#print axioms VerifiableInference.Desc.K9L.leaves_shut
#print axioms VerifiableInference.Desc.K9L.leaves_andThen
#print axioms VerifiableInference.Desc.K9L.leaves_closeOf
#print axioms VerifiableInference.Desc.K9L.leaves_joint
