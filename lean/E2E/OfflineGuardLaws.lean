-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineGuardLaws.lean: WHERE COLUMNS ARE HANDED, A HALF BEHIND THE GUARD PLAYS AS THE PLAIN HALF. The guard
(`Move.needsField`, `Part.needsField`, `Placed.needsField`: Johnson/Desc/ProofFile/Honest/K12/FieldGuard.lean) errs at a move where
the state's field `opened` is none, and else lets the move through. General in the list of parts. It imports that file's
definitions alone, and every name here stands in this file's own namespace.

WHOSE TEXT. The statements and their proofs are those of Johnson/Desc/ProofFile/Honest/K12/FieldGuardLift.lean, sections 1 to 4, copied
under other names: nothing is new here. They are laid apart so that a file over them can be imported beside any file that
declares a step behind the guard under a name of its own.

  `guardedStep`          a step with its move, if any, behind the guard
  `tell_behindGuard`, `hear_behindGuard`, `play_behindGuard`   at a field that is some, `play` over guarded steps is `play` over
                         the plain ones: the same rounds played and the same end state
  `coinsBehindGuard`     the coins of a list of parts, as coins of the list behind the guard
  `partSteps_behindGuard`, `rowSteps_behindGuard`, `placedSteps_behindGuard`   a half's steps behind the guard are its plain steps,
                         each guarded
  `lendPart_behindGuard`, `lendRow_behindGuard`, `lendRowPlaced_behindGuard`   the book lends behind the guard as it lends the plain
                         parts, the coins carried over
  `chainSteps_behindGuard`, `chainStop_behindGuard`   the same at one sub-protocol, stops included

Limits. The guard tests that the field is there; nothing here reads what it holds. `chainSteps_behindGuard` is at a list of one
sub-protocol. No property of a prover or a protocol: nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FieldGuard
import Johnson.Desc.ProofFile.Honest.Law.ThreadC
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.WalkOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Oracle)

variable {S Cl V W X Pb : Type}

/-! ## 1 Play -/

/-- **A step with its move, if any, behind the guard.** -/
def guardedStep (s : Step W X) : Step W X := { s with move := s.move.map Move.needsField }

/-- At a field that is some, a guarded step tells what the step tells. -/
theorem tell_behindGuard (s : Step W X) (back : Option Fmt.RoundView) (m : Mid W X) (cs : List OpenedColumn)
    (h : m.opened = some cs) : (guardedStep s).tell back m = s.tell back m := by
  rcases s with ⟨name, addr, decl, oracles, bad, hid, nth, last, move⟩
  cases move with
  | none => rfl
  | some mv =>
    have e : mv.needsField.say () m.shown m.st = mv.say () m.shown m.st :=
      needsField_some mv () m.shown m.st cs h
    simp only [guardedStep, Option.map_some, Step.tell, Step.stop, e]

/-- A guarded step hears as the step does. -/
theorem hear_behindGuard (s : Step W X) (x : Told) (d : Fmt.Drawn) (m : Mid W X) :
    (guardedStep s).hear x d m = s.hear x d m := by
  rcases s with ⟨name, addr, decl, oracles, bad, hid, nth, last, move⟩
  cases move <;> rfl

/-- **At a field that is some, `play` over guarded steps is `play` over the steps.** -/
theorem play_behindGuard : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (cs : List OpenedColumn), m.opened = some cs →
    play (ss.map guardedStep) ds back m = play ss ds back m
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _ => by simp [play]
  | s :: ss, [], _, _, _, _ => by
    rw [List.map_cons]
    simp [play]
  | s :: ss, d :: ds, back, m, cs, h => by
    rw [List.map_cons, play, play, tell_behindGuard s _ m cs h]
    cases ht : s.tell back.head? m with
    | error e => rfl
    | ok x =>
      show ((guardedStep s).hear x d m).bind _ = (s.hear x d m).bind _
      rw [hear_behindGuard]
      cases hh : s.hear x d m with
      | error e => rfl
      | ok m' =>
        show Except.map _ (play (ss.map guardedStep) ds back.tail m') =
          Except.map _ (play ss ds back.tail m')
        rw [play_behindGuard ss ds back.tail m' cs ((hear_opened hh).trans h)] <;> rfl

/-! ## 2 A half's steps -/

/-- Mapping the second list of a zip, in a list with its numbers. -/
theorem zipIdx_zip_behindGuard {A B B' C : Type} (f : B → B') (F : (A × B') × Nat → C)
    (G : (A × B) × Nat → C) (hFG : ∀ a b n, F ((a, f b), n) = G ((a, b), n)) :
    ∀ (rs : List A) (ms : List B) (k : Nat),
      ((rs.zip (ms.map f)).zipIdx k).map F = ((rs.zip ms).zipIdx k).map G
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | r :: rs, m :: ms, k => by
    have ih := zipIdx_zip_behindGuard f F G hFG rs ms (k + 1)
    show F ((r, f m), k) :: ((rs.zip (ms.map f)).zipIdx (k + 1)).map F =
      G ((r, m), k) :: ((rs.zip ms).zipIdx (k + 1)).map G
    rw [hFG, ih]

/-- A part's steps behind the guard are its steps, each guarded. -/
theorem partSteps_behindGuard (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    p.needsField.steps name a rs v c = (p.steps name a rs v c).map guardedStep := by
  have hl := needsField_length p
  unfold Part.steps
  rw [hl, List.map_map]
  refine zipIdx_zip_behindGuard Move.needsField _ _ ?_ rs p.moves 0
  intro r mv n
  rfl

/-- **The coins of a list of parts, as coins of the list behind the guard.** -/
def coinsBehindGuard : (ps : List (Part V W X)) → RowCoins ps → RowCoins (ps.map Part.needsField)
  | [], _ => ()
  | _ :: ps, c => (c.1, coinsBehindGuard ps c.2)

/-- A list's steps behind the guard are its steps, each guarded. -/
theorem rowSteps_behindGuard (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps),
      rowSteps name a v (ps.map Part.needsField) j rs (coinsBehindGuard ps c) =
        (rowSteps name a v ps j rs c).map guardedStep
  | [], _, _, _ => rfl
  | p :: ps, j, rs, c => by
    have e : rowSteps name a v ((p :: ps).map Part.needsField) j rs (coinsBehindGuard (p :: ps) c) =
        p.needsField.steps name ⟨a, j⟩ (rs.take p.needsField.moves.length) v c.1 ++
          rowSteps name a v (ps.map Part.needsField) (j + 1)
            (rs.drop p.needsField.moves.length) (coinsBehindGuard ps c.2) := rfl
    have e' : rowSteps name a v (p :: ps) j rs c =
        p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
          rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2 := rfl
    rw [e, e', needsField_length, List.map_append, partSteps_behindGuard,
      rowSteps_behindGuard name a v ps]

/-- A half's steps behind the guard are its steps, each guarded. -/
theorem placedSteps_behindGuard (h : Placed V W X) (b : Block S Cl) (v : Option V)
    (c : RowCoins h.parts) :
    h.needsField.steps b v (coinsBehindGuard h.parts c) = (h.steps b v c).map guardedStep :=
  rowSteps_behindGuard b.name b.place v h.parts 0 (b.rounds.zip b.oracles) c

/-! ## 3 The book -/

/-- `lendPart` reads no move: behind the guard it is the plain one. -/
theorem lendPart_behindGuard (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Addr) (p : Part V W X) :
    lendPart B rows look a p.needsField =
      (lendPart B rows look a p : Except String p.needsField.Coins) := by
  cases p with
  | mk t s c b h o1 o2 m =>
    dsimp only [Part.needsField, lendPart]
    by_cases hd : (t != dueAt rows a) = true
    · simp only [if_pos hd] <;> rfl
    · simp only [if_neg hd]
      cases (look a).2.cut ⟨0, 0⟩ t <;> rfl

/-- **`lendRow` behind the guard is the plain one, the coins carried over.** -/
theorem lendRow_behindGuard (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) : ∀ (ps : List (Part V W X)) (j : Nat),
    lendRow B rows look a (ps.map Part.needsField) j =
      (lendRow B rows look a ps j).map (coinsBehindGuard ps)
  | [], _ => rfl
  | p :: ps, j => by
    have e : lendRow B rows look a ((p :: ps).map Part.needsField) j =
        ((lendPart B rows look ⟨a, j⟩ p.needsField).mapError
          fun e => "part " ++ toString j ++ ": " ++ e).bind
          fun c => (lendRow B rows look a (ps.map Part.needsField) (j + 1)).map
            fun r => ((c, r) : RowCoins (p.needsField :: ps.map Part.needsField)) := rfl
    have e' : lendRow B rows look a (p :: ps) j =
        ((lendPart B rows look ⟨a, j⟩ p).mapError
          fun e => "part " ++ toString j ++ ": " ++ e).bind
          fun c => (lendRow B rows look a ps (j + 1)).map
            fun r => ((c, r) : RowCoins (p :: ps)) := rfl
    rw [e, e', lendPart_behindGuard, lendRow_behindGuard B rows look a ps (j + 1)]
    cases lendPart B rows look ⟨a, j⟩ p with
    | error _ => rfl
    | ok c =>
      cases lendRow B rows look a ps (j + 1) with
      | error _ => rfl
      | ok r => rfl

/-- The same at a half's parts. -/
theorem lendRowPlaced_behindGuard (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) (h : Placed V W X) (j : Nat) :
    lendRow B rows look a h.needsField.parts j =
      (lendRow B rows look a h.parts j).map (coinsBehindGuard h.parts) :=
  lendRow_behindGuard B rows look a h.parts j

theorem rounds_behindGuard (h : Placed V W X) : h.needsField.rounds = h.rounds := by
  have e : ∀ (ps : List (Part V W X)) (n : Nat),
      (ps.map Part.needsField).foldl (fun n p => n + p.moves.length) n =
        ps.foldl (fun n p => n + p.moves.length) n := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro n
      show (ps.map Part.needsField).foldl _ (n + p.needsField.moves.length) =
        ps.foldl _ (n + p.moves.length)
      rw [needsField_length, ih]
  exact e h.parts 0

theorem cut_behindGuard (h : Placed V W X) :
    h.needsField.parts.map (·.moves.length) = h.parts.map (·.moves.length) := by
  show (h.parts.map Part.needsField).map _ = _
  rw [List.map_map]
  exact List.map_congr_left fun p _ => needsField_length p

theorem partsLength_behindGuard (h : Placed V W X) :
    h.needsField.parts.length = h.parts.length := List.length_map _

/-! ## 4 One sub-protocol -/

/-- **`chainSteps` behind the guard, at one sub-protocol.** hs has at b's place the half h behind the
guard, hs' the half h. Every error of the one is the other's; where both return, the steps of the
one are those of the other, each guarded. -/
theorem chainSteps_behindGuard (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs hs' : List (Placed V W X)) (h : Placed V W X)
    (hf : (hs.find? fun g => g.place == b.place) = some h.needsField)
    (hf' : (hs'.find? fun g => g.place == b.place) = some h) :
    chainSteps B rows look v [b] hs =
      (chainSteps B rows look v [b] hs').map (·.map guardedStep) := by
  simp only [chainSteps, hf, hf', rounds_behindGuard, cut_behindGuard, partsLength_behindGuard]
  by_cases c1 : (b.oracles.length != b.rounds.length) = true
  · simp only [if_pos c1] <;> rfl
  by_cases c2 : (h.rounds != b.rounds.length) = true
  · simp only [if_neg c1, if_pos c2] <;> rfl
  by_cases c3 : (B.cuts.lookup b.place != some (h.parts.map (·.moves.length))) = true
  · simp only [if_neg c1, if_neg c2, if_pos c3] <;> rfl
  by_cases c4 : (rows.any fun r =>
      r.1.place == b.place && decide (h.parts.length ≤ r.1.part)) = true
  · simp only [if_neg c1, if_neg c2, if_neg c3, if_pos c4] <;> rfl
  by_cases c5 : (B.ahead.any fun e =>
      e.spender.place == b.place && decide (h.parts.length ≤ e.spender.part)) = true
  · simp only [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5] <;> rfl
  simp only [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, lendRowPlaced_behindGuard]
  cases hl : lendRow B rows look b.place h.parts 0 with
  | error e => rfl
  | ok c =>
    show Except.ok (h.needsField.steps b v (coinsBehindGuard h.parts c) ++ []) =
      Except.ok ((h.steps b v c ++ []).map guardedStep)
    rw [placedSteps_behindGuard, List.append_nil, List.append_nil]

theorem partStop_behindGuard (p : Part V W X) (v : Option V) (loc ds : List Fmt.Drawn) :
    p.needsField.stopAt v loc ds = p.stopAt v loc ds := by
  unfold Part.stopAt
  rw [needsField_length] <;> rfl

theorem rowStop_behindGuard (v : Option V) : ∀ (ps : List (Part V W X)) (loc ds : List Fmt.Drawn),
    rowStopAt v (ps.map Part.needsField) loc ds = rowStopAt v ps loc ds
  | [], _, _ => rfl
  | p :: ps, loc, ds => by
    show (p.needsField.stopAt v loc (ds.take p.needsField.moves.length)).or
        (rowStopAt v (ps.map Part.needsField) (loc ++ ds.take p.needsField.moves.length)
          (ds.drop p.needsField.moves.length)) =
      (p.stopAt v loc (ds.take p.moves.length)).or
        (rowStopAt v ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length))
    rw [needsField_length, partStop_behindGuard, rowStop_behindGuard v ps]

/-- The stops read nothing of the guard. -/
theorem chainStop_behindGuard (v : Option V) (b : Block S Cl) (hs hs' : List (Placed V W X))
    (h : Placed V W X) (hf : (hs.find? fun g => g.place == b.place) = some h.needsField)
    (hf' : (hs'.find? fun g => g.place == b.place) = some h) (loc ds : List Fmt.Drawn) :
    chainStopAt v [b] hs loc ds = chainStopAt v [b] hs' loc ds := by
  have e : rowStopAt v h.needsField.parts loc (ds.take b.rounds.length) =
      rowStopAt v h.parts loc (ds.take b.rounds.length) := rowStop_behindGuard v h.parts _ _
  show ((hs.find? fun g => g.place == b.place).bind
        fun g => rowStopAt v g.parts loc (ds.take b.rounds.length)).or
      (chainStopAt v [] hs (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length)) =
    ((hs'.find? fun g => g.place == b.place).bind
        fun g => rowStopAt v g.parts loc (ds.take b.rounds.length)).or
      (chainStopAt v [] hs' (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length))
  rw [hf, hf']
  exact congrArg (fun o => Option.or o none) e

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.guardedStep
#print axioms AtPublicFiles.OfflineRows.tell_behindGuard
#print axioms AtPublicFiles.OfflineRows.hear_behindGuard
#print axioms AtPublicFiles.OfflineRows.play_behindGuard
#print axioms AtPublicFiles.OfflineRows.zipIdx_zip_behindGuard
#print axioms AtPublicFiles.OfflineRows.partSteps_behindGuard
#print axioms AtPublicFiles.OfflineRows.coinsBehindGuard
#print axioms AtPublicFiles.OfflineRows.rowSteps_behindGuard
#print axioms AtPublicFiles.OfflineRows.placedSteps_behindGuard
#print axioms AtPublicFiles.OfflineRows.lendPart_behindGuard
#print axioms AtPublicFiles.OfflineRows.lendRow_behindGuard
#print axioms AtPublicFiles.OfflineRows.lendRowPlaced_behindGuard
#print axioms AtPublicFiles.OfflineRows.rounds_behindGuard
#print axioms AtPublicFiles.OfflineRows.cut_behindGuard
#print axioms AtPublicFiles.OfflineRows.partsLength_behindGuard
#print axioms AtPublicFiles.OfflineRows.chainSteps_behindGuard
#print axioms AtPublicFiles.OfflineRows.partStop_behindGuard
#print axioms AtPublicFiles.OfflineRows.rowStop_behindGuard
#print axioms AtPublicFiles.OfflineRows.chainStop_behindGuard
