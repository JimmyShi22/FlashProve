-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/MovesRow.lean
(kind K9's soundness lemma): THEOREMS: A PLACE THAT IS MADE AS A SEAT MAKES IT IS
A DRAW WITH MOVES BEHIND IT: the draw's block, and then a LIST of blocks without a round, joined by
a fold of Block.andThen under one name, each block dressed anew (its name and its place turned).
  IsMoves        a block without a round whose yes is a yes of a row of moves.
  isMoves_addsStep   a step of adding (Batch/Objects.lean):
                 [add (gather ws cut runs), quiet behind].
                 (The step's own counts stand in no move: the moves are WEAKER than the step: right
                 for this direction: a yes has passed them.)
  isMoves_quiet  a block whose decision reads neither rounds nor groups: one quiet move.
  isMoves_tests  the tests behind the adding (Batch/Tests.lean: testsBehind): one quiet move.
  isMoves_dress, staged_dress   a block with the same rounds and the same decision (another name,
                 place, plan's test, lists): the same.
  staged_foldl   the fold.
  drawMoves_joined   **DrawMoves (Law/Moves.lean) at
                 (qs.map (·.1)).foldl (fun acc x => acc.andThen name x) draw'**, draw' a dressed
                 K9.drawAlone, each q.1 a block that is the moves q.2.
That is the text by which the seat for the adding joins a place's steps ("joined": a fold of andThen
over the steps' blocks, each { b with name, place }). ONLY rounds AND decide ARE READ: what the
joined blocks state (claims, after, before, planOk) is not looked at. NOT CLAIMED: that any seat's
table hands just such blocks: that is read off the seat's own file, by whoever holds it.

-/
import Johnson.Desc.First.Batch.Law.MovesBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where drawAlone addsStep gather RunOf Window testsBehind
  TLens TWhere)

variable {T Cl : Type}

/-- A block without a round whose yes is a yes of a row of moves. -/
structure IsMoves (X : Lens T) (ms : List (Move T)) (q : Block T Cl) : Prop where
  rounds : q.rounds = []
  dec : ∀ t rs gs t', q.decide t rs gs = .ok t' → ∃ cls, MovesYes X ms t t' cls

theorem isMoves_addsStep (X : Lens T) (p : Where) (what : String)
    (counts : List (String × (T → Bool))) (ws : T → List Window) (cut : List (Nat × String))
    (runs : List (RunOf T)) (behind : T → Except String T) :
    IsMoves X [.add (gather ws cut runs), .quiet behind]
      (addsStep (Cl := Cl) X p what counts ws cut runs behind) where
  rounds := rfl
  dec := addsStep_moves X p what counts ws cut runs behind

theorem isMoves_quiet (X : Lens T) (q : Block T Cl) (hr : q.rounds = [])
    (f : T → Except String T) (hq : ∀ t rs gs, q.decide t rs gs = f t) :
    IsMoves X [.quiet f] q where
  rounds := hr
  dec := quiet_moves X q f hq

theorem isMoves_tests (X : Lens T) (Y : TLens T) (p : TWhere)
    (counts : List (String × (T → Bool)))
    (weights : Array Nat → HTailF2 → Fork → K9.Ans Fork) :
    IsMoves X [.quiet fun t => (testsBehind (Cl := Cl) Y p counts weights).decide t [] []]
      (testsBehind (Cl := Cl) Y p counts weights) :=
  isMoves_quiet X _ rfl _ fun _ _ _ => rfl

theorem isMoves_dress (X : Lens T) (ms : List (Move T)) (q q' : Block T Cl)
    (h : IsMoves X ms q) (hr : q'.rounds = q.rounds) (hd : q'.decide = q.decide) :
    IsMoves X ms q' where
  rounds := hr.trans h.rounds
  dec := by
    rw [hd]
    exact h.dec

theorem staged_dress (X : Lens T) (p : Where) (ms : List (Move T)) (b b' : Block T Cl)
    (h : Staged X p ms b) (hr : b'.rounds = b.rounds) (hd : b'.decide = b.decide) :
    Staged X p ms b' where
  rounds := hr.trans h.rounds
  dec := by
    rw [hd]
    exact h.dec

/-- The fold. -/
theorem staged_foldl (X : Lens T) (p : Where) (name : String) :
    ∀ (qs : List (Block T Cl × List (Move T))) (b : Block T Cl) (ms : List (Move T)),
      Staged X p ms b → (∀ q ∈ qs, IsMoves X q.2 q.1) →
      Staged X p (ms ++ qs.flatMap (·.2))
        ((qs.map (·.1)).foldl (fun acc x => acc.andThen name x) b)
  | [], b, ms, h, _ => by
    simpa using h
  | q :: qs, b, ms, h, hq => by
    have h1 := staged_then X p ms q.2 b q.1 name h (hq q List.mem_cons_self).rounds
      (hq q List.mem_cons_self).dec
    have h2 := staged_foldl X p name qs (b.andThen name q.1) (ms ++ q.2) h1
      fun r hr => hq r (List.mem_cons_of_mem _ hr)
    rw [List.flatMap_cons, ← List.append_assoc]
    exact h2

/-- **A place as a seat joins it is a draw with moves behind it.** -/
theorem drawMoves_joined (X : Lens T) (p : Where) (name : String) (draw' : Block T Cl)
    (hr : draw'.rounds = (drawAlone (Cl := Cl) X p).rounds)
    (hd : draw'.decide = (drawAlone (Cl := Cl) X p).decide)
    (qs : List (Block T Cl × List (Move T))) (hq : ∀ q ∈ qs, IsMoves X q.2 q.1) :
    DrawMoves X p (qs.flatMap (·.2))
      ((qs.map (·.1)).foldl (fun acc x => acc.andThen name x) draw') :=
  drawMoves_of_staged X p _ _
    (staged_foldl X p name qs draw' [] (staged_dress X p [] _ draw' (staged_draw X p) hr hd) hq)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.isMoves_addsStep
#print axioms VerifiableInference.Desc.K9L.isMoves_tests
#print axioms VerifiableInference.Desc.K9L.staged_foldl
#print axioms VerifiableInference.Desc.K9L.drawMoves_joined
