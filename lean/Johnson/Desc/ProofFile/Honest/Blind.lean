-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Blind.lean: a part's move is handed, beside the rounds shown, the
columns opened so far (`Seen.opened`, Honest/Frame.lean). This file says in one place what it means
that a move does not depend on the columns handed to it. Three definitions, over Honest/Frame.lean
alone, so that every file that wants them can import them.

  1  `Move.Blind`   the move's message is the same whatever columns it is handed. `Part.Blind`: all
     moves of the part are so. `Step.Blind`: the step's move is so, if it has one
  2  `Move.blind_of_rounds`   an example: a move that is written as a function of the rounds shown
     is blind, by `rfl`. `Move.not_blind_of_reads`: a negative example: a move whose message differs
     between no columns and some columns is not
  3  `Move.lift_blind`, `Part.lift_blind`   placing a move or a part in a wider input and state
     (`Move.lift`, `Part.lift`) keeps it blind
  4  `blind_zipIdx_fst`, `blind_zip_snd`, `Part.steps_blind`   the steps of a blind part
     (`Part.steps`) are blind. The first two are lemmas on lists

Limits.
  * Each definition is a statement over all coins, rounds, columns and states. It is not a test with
    code. For a part whose moves are written as in 2 it holds by `rfl`, one line for each move.
  * A part without a move is blind, and so is a move that returns one and the same error at every
    argument.
  * Only the message (`Move.say`) is spoken of. `Move.hand` is not handed the columns, by its type.
  * A hypothesis "every step before an address is blind" is false at each address behind the first
    part that reads the columns handed to it, and a lemma under it says nothing there. Once the
    parts of the kind K10 that read the columns are laid, that is the first chain behind the first
    of them, and all of the second chain wherever its start is reached through the first chain's
    rounds. There a lemma is to be stated of the walk's own state (`walk`, Honest/Walk.lean), with
    no hypothesis on the steps.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (OpenedColumn Oracle)

/-! ## 1 The three definitions -/

/-- The move's message does not depend on the columns handed to it. It is a definition. -/
def Move.Blind {C W X : Type} (mv : Move C W X) : Prop :=
  ∀ c rs o o' t, mv.say c ⟨rs, o⟩ t = mv.say c ⟨rs, o'⟩ t

/-- No move of the part depends on the columns handed to it. It is a definition. -/
def Part.Blind {V W X : Type} (p : Part V W X) : Prop := ∀ mv ∈ p.moves, mv.Blind

/-- The step's move, if it has one, does not depend on the columns handed to it. It is a
definition. -/
def Step.Blind {W X : Type} (s : Step W X) : Prop := ∀ mv, s.move = some mv → mv.Blind

/-! ## 2 An example and a negative example -/

/-- A move written as a function of the rounds shown is blind. -/
theorem Move.blind_of_rounds {C W X : Type}
    (f : C → List Fmt.RoundView → State W X → Except String Sending) (hand : State W X → X) :
    (⟨fun c sn t => f c sn.rounds t, hand⟩ : Move C W X).Blind :=
  fun _ _ _ _ _ => rfl

/-- An example: a move whose message differs between no columns and some columns is not blind. -/
theorem Move.not_blind_of_reads {C W X : Type} (c : C) (t : State W X) (hand : State W X → X) :
    ¬ (⟨fun _ sn _ => if sn.opened.isSome then .error "some" else .error "none", hand⟩ :
      Move C W X).Blind := by
  intro h
  have e := h c [] none (some []) t
  simp at e

/-! ## 3 Placing in a wider input and state -/

theorem Move.lift_blind {C W W' X Y : Type} (wit : W → W') (get : X → Y) (set : X → Y → X)
    {mv : Move C W' Y} (h : mv.Blind) : (Move.lift wit get set mv).Blind :=
  fun c rs o o' t => h c rs o o' (t.narrow wit get)

theorem Part.lift_blind {V V' W W' X Y : Type} (see : V → V') (wit : W → W') (get : X → Y)
    (set : X → Y → X) {p : Part V' W' Y} (h : p.Blind) : (Part.lift see wit get set p).Blind := by
  intro mv hmv
  obtain ⟨mv₀, h₀, rfl⟩ := List.mem_map.1 hmv
  exact Move.lift_blind wit get set (h mv₀ h₀)

/-! ## 4 The steps of a blind part -/

theorem blind_zipIdx_fst {α : Type} : ∀ (l : List α) (n : Nat) (r : α × Nat),
    r ∈ l.zipIdx n → r.1 ∈ l
  | [], _, _, h => by simp at h
  | a :: l, n, r, h => by
    have h' : r ∈ (a, n) :: l.zipIdx (n + 1) := h
    rcases List.mem_cons.1 h' with rfl | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (blind_zipIdx_fst l (n + 1) r h')

theorem blind_zip_snd {α β : Type} : ∀ (l₁ : List α) (l₂ : List β) (z : α × β),
    z ∈ l₁.zip l₂ → z.2 ∈ l₂
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l₁, b :: l₂, z, h => by
    have h' : z ∈ (a, b) :: l₁.zip l₂ := h
    rcases List.mem_cons.1 h' with rfl | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (blind_zip_snd l₁ l₂ z h')

/-- **The steps of a blind part are blind.** -/
theorem Part.steps_blind {V W X : Type} {p : Part V W X} (h : p.Blind) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    ∀ s ∈ p.steps name a rs v c, s.Blind := by
  intro s hs mv hmv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
  obtain rfl := Option.some.inj hmv
  have hm : r.1.2 ∈ p.moves := blind_zip_snd _ _ _ (blind_zipIdx_fst _ _ _ hr)
  exact fun _ q o o' t => h r.1.2 hm c q o o' t

end ProofFile.Honest

#print axioms ProofFile.Honest.Move.blind_of_rounds
#print axioms ProofFile.Honest.Move.not_blind_of_reads
#print axioms ProofFile.Honest.Move.lift_blind
#print axioms ProofFile.Honest.Part.lift_blind
#print axioms ProofFile.Honest.blind_zipIdx_fst
#print axioms ProofFile.Honest.blind_zip_snd
#print axioms ProofFile.Honest.Part.steps_blind
#print axioms ProofFile.Honest.Move.Blind
#print axioms ProofFile.Honest.Part.Blind
#print axioms ProofFile.Honest.Step.Blind
