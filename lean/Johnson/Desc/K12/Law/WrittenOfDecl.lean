-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/WrittenOfDecl.lean: a file's declared rounds written out
(`Johnson.G.OfPlan.writtenOf`, Johnson/G/RoundsOfPlan.lean), chain by chain, in the form that
WrittenOfG.lean takes.

Two functions bear the name `writtenOf`. `Johnson.G.OfPlan.writtenOf` makes of a file's three lists
of declared rounds three lists of rounds as readers take them, each with its stored trees, or a
refusal. `H2K.Pub.writtenOf` (PubOk.lean) makes of one place's numbers its written rounds for the
law of a proximity test.
Main names:
  `earlierOf D`: the roots and run values that stand in for the two earlier chains of a file, as the
    first function lays them.
  `mapM_round_of_ok`: one chain: from the maker with refusals to the plain one.
  `chains_of_written`: a yes of the first function gives, for each of the three chains, what readers
    take of its declared rounds.
Limits: on the maker's text alone. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.WrittenOfG
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
namespace H2K.Pub
open Johnson.G.OfPlan (Decl3 rootsOf)
open OnBytes.Three (tagRoot tagRun)

/-- The roots and run values that stand in for the two earlier chains of a file. -/
def earlierOf (D : Decl3) : List (List ByteArray × ByteArray) :=
  [((List.range (rootsOf D.1)).map tagRoot, tagRun 1),
   ((List.range (rootsOf D.2.1)).map tagRoot, tagRun 2)]

/-- One chain: from the maker with refusals to the plain one. -/
theorem mapM_round_of_ok {ε : Type} (e : List (List ByteArray × ByteArray))
    (no : Fmt.DeclaredRound → ε) : ∀ (l : List Fmt.DeclaredRound) (R : List (Fmt.Round × List Fmt.Stored)),
    (l.mapM fun r => match r.round e with
      | some x => (pure (x, r.stored) : Except ε (Fmt.Round × List Fmt.Stored))
      | none => throw (no r)) = .ok R →
    l.mapM (·.round e) = some (R.map (·.1))
  | [], R, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | r :: l, R, h => by
    rw [List.mapM_cons] at h
    cases hr : r.round e with
    | none =>
      simp only [hr] at h
      cases h
    | some x =>
      simp only [hr] at h
      cases hl : (l.mapM fun r => match r.round e with
        | some x => (pure (x, r.stored) : Except ε (Fmt.Round × List Fmt.Stored))
        | none => throw (no r)) with
      | error z =>
        rw [hl] at h
        cases h
      | ok R' =>
        rw [hl] at h
        cases h
        rw [List.mapM_cons, hr, mapM_round_of_ok e no l R' hl]
        rfl

/-- **A file's declared rounds written out, chain by chain.** -/
theorem chains_of_written {file : String} {D : Decl3}
    {R : OnBytes.Params.Rounds × OnBytes.Params.Rounds × OnBytes.Params.Rounds}
    (h : Johnson.G.OfPlan.writtenOf file D = .ok R) :
    D.1.mapM (·.round []) = some (R.1.map (·.1)) ∧
      D.2.1.mapM (·.round []) = some (R.2.1.map (·.1)) ∧
      D.2.2.mapM (·.round (earlierOf D)) = some (R.2.2.map (·.1)) := by
  unfold Johnson.G.OfPlan.writtenOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i R1 h1
    split at h
    · cases h
    · rename_i R2 h2
      split at h
      · cases h
      · rename_i R3 h3
        cases h
        exact ⟨mapM_round_of_ok _ _ _ _ h1, mapM_round_of_ok _ _ _ _ h2,
          mapM_round_of_ok _ _ _ _ h3⟩

end H2K.Pub

#print axioms H2K.Pub.chains_of_written
