-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/RowParts.lean: which part's number each played round of a
lookup's row bears. Theorems, with two definitions: first for every row, then at the lookup's row
(`lookRow`) and at the seated row (`proverSideOfLookupInChainAtOneOwner`, both in Honest/K3/Row.lean).

Terms. Honest/K3/GLOSSARY.md ("part", "play", "row", "stage"). In this file: `numbersOf ps j` lists
the parts' numbers from j on, each as often as the part has moves; `stageNumbers f` lists the
stages' numbers in the row, each as often as the stage has rounds.

What is shown.
  `stepsFrom_parts`, `rowSteps_parts`: the steps of a row bear the parts' numbers, each as often as
    the part has moves, where there are rounds for all moves.
  `yields_parts`: rounds that were played on steps which all have a move bear the steps' numbers.
  `played_parts`: the played rounds of a row bear the parts' numbers, each as often as the part has
    moves. This holds of every run of `play` on the row's steps that returns.
  `numbers_row`: at a row over stages with their numbers, these are the stages' numbers.
  `lookRow_parts`, `lookSeat_parts`: at the lookup's row, and at the seated row: the stages' numbers
    in the row, each as often as the stage has rounds.

Hypotheses that remain.
  `h`: the run of `play` on the row's steps has returned.
  `hl`: there are rounds for all moves.
  `hg`: (in `numbers_row`) each part has as many moves as its stage has rounds.

Imported. Honest/Frame.lean, Honest/Side.lean and Honest/Law/Play.lean, whose notions these
statements use.

Users. The frame finds a part's rounds in a run by place and by the part's number (`Played.isAt`,
Honest/Side.lean). So a caller that uses "the row plays" at one member of a side needs the numbers
too. Honest/K3/Law/RowLends.lean imports this file.

Limits. The statements speak of a run that has returned; that it returns is shown in
Honest/K3/Law/RowPlays.lean and Honest/K3/Law/RowSeated.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.RowSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Oracle Place)

variable {V W X C : Type}

theorem stepsFrom_parts (name : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (n : Nat) (c : C) :
    ∀ (l : List ((Fmt.DeclaredRound × List Oracle) × Move C W X)) (k : Nat),
      (stepsFrom name a bad hid n c l k).map (·.addr.part) = List.replicate l.length a.part
  | [], _ => rfl
  | r :: l, k => by
    have e : stepsFrom name a bad hid n c (r :: l) k =
        ⟨name, a, r.1.1, r.1.2, bad, hid, k, k + 1 == n, some ⟨fun _ => r.2.say c, r.2.hand⟩⟩ ::
          stepsFrom name a bad hid n c l (k + 1) := by
      simp [stepsFrom, List.zipIdx_cons]
    rw [e, List.map_cons, stepsFrom_parts name a bad hid n c l (k + 1), List.length_cons,
      List.replicate_succ]

/-- The parts' numbers from j on, each as often as the part has moves. -/
def numbersOf : List (Part V W X) → Nat → List Nat
  | [], _ => []
  | p :: ps, j => List.replicate p.moves.length j ++ numbersOf ps (j + 1)

theorem rowSteps_parts (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps), (ps.map (·.moves.length)).sum ≤ rs.length →
      (rowSteps name a v ps j rs c).map (·.addr.part) = numbersOf ps j
  | [], _, _, _, _ => rfl
  | p :: ps, j, rs, c, h => by
    simp only [List.map_cons, List.sum_cons] at h
    have e := stepsFrom_parts name ⟨a, j⟩ p.bad (fun f o => v.bind fun w => p.hid w f o)
      p.moves.length c.1 ((rs.take p.moves.length).zip p.moves) 0
    have hl : ((rs.take p.moves.length).zip p.moves).length = p.moves.length := by
      rw [List.length_zip, List.length_take]; omega
    rw [hl] at e
    rw [rowSteps, List.map_append, numbersOf,
      rowSteps_parts name a v ps (j + 1) _ c.2 (by rw [List.length_drop]; omega)]
    exact congrArg (· ++ numbersOf ps (j + 1)) e

theorem yields_parts : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → (∀ s ∈ ss, s.move.isSome = true) →
    ps.map (·.part) = ss.map (·.addr.part)
  | [], [], _, [], _, _ => rfl
  | s :: ss, d :: ds, back, p :: ps, h, hs => by
    have h' : s.Yields back.head? d p ∧ Yields ss ds back.tail ps := h
    obtain ⟨_, _, _, h4, _⟩ := h'.1
    rw [List.map_cons, List.map_cons, (h4 (hs s List.mem_cons_self)).1,
      yields_parts ss ds back.tail ps h'.2 fun s' hs' => hs s' (List.mem_cons_of_mem _ hs')]
  | [], [], _, _ :: _, h, _ => h.elim
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim
  | _ :: _, _ :: _, _, [], h, _ => h.elim

/-- **The played rounds of a row bear the parts' numbers, each as often as the part has moves.** -/
theorem played_parts (name : String) (a : Place) (v : Option V) (ps : List (Part V W X)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins ps) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X)
    (h : play (rowSteps name a v ps j rs c) ds back m = .ok y)
    (hl : (ps.map (·.moves.length)).sum ≤ rs.length) :
    y.1.map (·.part) = numbersOf ps j := by
  rw [yields_parts _ _ _ _ (play_yields _ _ _ _ _ h)
    fun s hs => (rowSteps_mem name a v ps j rs c s hs).2.1]
  exact rowSteps_parts name a v ps j rs c hl

/-- The stages' numbers in the row, each as often as the stage has rounds. -/
def stageNumbers (f : LFace) : List Nat :=
  (stages f).zipIdx.flatMap fun s => List.replicate (s.1.rounds f) s.2

theorem numbers_row (f : LFace) (g : Stage × Nat → Part V W X)
    (hg : ∀ x, (g x).moves.length = x.1.rounds f) :
    ∀ (ss : List Stage) (off : Nat), numbersOf ((ss.zipIdx off).map g) off =
      (ss.zipIdx off).flatMap fun s => List.replicate (s.1.rounds f) s.2
  | [], _ => rfl
  | s :: ss, off => by
    show List.replicate (g (s, off)).moves.length off ++
        numbersOf ((ss.zipIdx (off + 1)).map g) (off + 1) =
      List.replicate (s.rounds f) off ++
        (ss.zipIdx (off + 1)).flatMap fun s => List.replicate (s.1.rounds f) s.2
    rw [hg, numbers_row f g hg ss (off + 1)]

/-- **At the lookup's row.** -/
theorem lookRow_parts (J : LookJobs W) (a : At) (name : String) (v : Option V)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins (lookRow (V := V) Rd J a))
    (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W Unit) (y : List Played × Mid W Unit)
    (h : play (rowSteps name a.place v (lookRow Rd J a) 0 rs c) ds back m = .ok y)
    (hl : ((stages a.face).map (Stage.rounds a.face)).sum ≤ rs.length) :
    y.1.map (·.part) = stageNumbers a.face := by
  rw [played_parts name a.place v _ 0 rs c ds back m y h (by rw [lookRow_moves]; exact hl)]
  exact numbers_row a.face (fun x => partOf Rd J a x.1 x.2)
    (fun x => partOf_moves _ _ _ _ _) (stages a.face) 0

/-- **At the seated row.** -/
theorem lookSeat_parts {V₁ W₁ X₁ : Type} (J : LookJobs W) (wit : W₁ → W) (a : At) (name : String)
    (v : Option V₁) (rs : List (Fmt.DeclaredRound × List Oracle))
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) Rd J wit a).parts) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W₁ X₁) (y : List Played × Mid W₁ X₁)
    (h : play (rowSteps name a.place v (proverSideOfLookupInChainAtOneOwner Rd J wit a).parts 0 rs c) ds back m = .ok y)
    (hl : ((stages a.face).map (Stage.rounds a.face)).sum ≤ rs.length) :
    y.1.map (·.part) = stageNumbers a.face := by
  rw [played_parts name a.place v _ 0 rs c ds back m y h (by rw [proverSideOfLookupInChainAtOneOwner_moves]; exact hl)]
  have e : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) Rd J wit a).parts =
      ((stages a.face).zipIdx 0).map fun x =>
        (partOf (V := Unit) Rd J a x.1 x.2).lift (fun _ => ()) wit (fun _ => ()) fun x _ => x := by
    simp [proverSideOfLookupInChainAtOneOwner, lookRow, List.map_map, Function.comp_def]
  rw [e]
  exact numbers_row a.face _ (fun x => by
    simp only [Part.lift, List.length_map]
    exact partOf_moves _ _ _ _ _) (stages a.face) 0

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.played_parts
#print axioms ProofFile.Honest.K3.Law.lookRow_parts
#print axioms ProofFile.Honest.K3.Law.lookSeat_parts
#print axioms ProofFile.Honest.K3.Law.stepsFrom_parts
#print axioms ProofFile.Honest.K3.Law.rowSteps_parts
#print axioms ProofFile.Honest.K3.Law.yields_parts
#print axioms ProofFile.Honest.K3.Law.numbers_row
