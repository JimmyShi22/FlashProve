-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/OkPlayed.lean: the words of rounds that the frame has
played are below the prime: the library's test `okRoundsE` (Johnson/Top/H/K3LawKind.lean) accepts
them. The statements are general: they name no kind, no half's text and no description. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: rounds that the frame has played are what `play`
(Honest/Frame.lean) returns, as a view shows them (`roundsOf`, there).

What is shown.
  `ok_tell`: the items of one round that was told have their words below the prime.
  `ok_play`: so have the items of all rounds played; and their challenges are those handed in.
  `okRounds_played`: conditional on the play's return and on the test on the challenges, the
    library's test accepts the rounds as a view shows them.
  `okRounds_moved`: the same from the sentence on the prover's side of a sub-protocol's step
    (`Thread.Moved`, Honest/Thread/Pays.lean).

Hypotheses that remain.
  `hy`: `play` returns (in `okRounds_moved`: `hM`, `Thread.Moved`).
  `hd`: the challenges pass the frame's test (`drawsFit`, Honest/Frame.lean).
  `h`: (in `ok_tell`) the step's telling returns.

How the proof goes. `Step.tell` (Honest/Frame.lean) writes what a move says into the words below the
prime that are read as it (`Said.got`); where no half stands and no stored run is at hand, the round
shows no item. The challenges pass the frame's test (`drawsFit`), which asks that of every word.

Imported: Honest/Frame.lean and the files under Honest/Thread/.

Users. `lays_stands` (Honest/K3/Law/Thread/LaysStands.lean) calls `okRounds_moved`.

Limits. At a play without a stored run to fall back on (the list "back" is empty), as in the
sentences on a step of Honest/Thread/Pays.lean. No instance of these hypotheses is exhibited in this
file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OkRounds
import Johnson.Desc.ProofFile.Honest.Thread.Pays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Maker (okGot)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.OnPublicFiles (okRoundsE)

variable {W X : Type}

/-- The items of one round that was told, with no stored round to fall back on. -/
theorem ok_tell (s : Step W X) (m : Mid W X) (x : Told) (h : s.tell none m = .ok x) :
    x.vals.all okGot = true := by
  unfold Step.tell at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          rw [List.all_eq_true]
          intro g hg
          obtain ⟨z, _, rfl⟩ := List.mem_map.1 hg
          exact okGot_said z
    · cases h
      rfl

/-- The items of all rounds played; and their challenges are those handed in. -/
theorem ok_play : ∀ (l : List (Step W X)) (ds : List Fmt.Drawn) (m : Mid W X)
    (y : List Played × Mid W X), play l ds [] m = .ok y →
    (∀ p ∈ y.1, p.vals.all okGot = true) ∧ y.1.map (·.drawn) = ds
  | [], [], m, y, h => by
    simp only [play, Except.ok.injEq] at h
    subst h
    exact ⟨fun p hp => by simp at hp, rfl⟩
  | [], _ :: _, m, y, h => by simp [play] at h
  | _ :: _, [], m, y, h => by simp [play] at h
  | s :: ss, d :: ds, m, y, h => by
    unfold play at h
    cases ht : s.tell ([] : List Fmt.RoundView).head? m with
    | error e => rw [ht] at h; cases h
    | ok x =>
      rw [ht] at h
      have h1 : ((s.hear x d m).bind fun m' =>
          (play ss ds ([] : List Fmt.RoundView).tail m').map fun y =>
            ((⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals, x.tables,
              d⟩ : Played) :: y.1, y.2)) = .ok y := h
      cases hh : s.hear x d m with
      | error e => rw [hh] at h1; cases h1
      | ok m' =>
        rw [hh] at h1
        have h2 : ((play ss ds [] m').map fun y =>
            ((⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals, x.tables,
              d⟩ : Played) :: y.1, y.2)) = .ok y := h1
        cases hp : play ss ds [] m' with
        | error e => rw [hp] at h2; cases h2
        | ok y' =>
          rw [hp] at h2
          obtain ⟨a, b⟩ := ok_play ss ds m' y' hp
          cases h2
          refine ⟨fun p hpm => ?_, by simp [b]⟩
          rcases List.mem_cons.1 hpm with e | e
          · rw [e]
            exact ok_tell s m x ht
          · exact a p e

/-- **The words of the rounds played are below the prime.** Conditional on the play's return and on
the frame's test on the challenges. No instance of these hypotheses is exhibited in this file. -/
theorem okRounds_played {l : List (Step W X)} {ds : List Fmt.Drawn} {m : Mid W X}
    {y : List Played × Mid W X} {zs : List Fmt.DeclaredRound} (hy : play l ds [] m = .ok y)
    (hd : drawsFit zs ds = true) : okRoundsE (roundsOf y.1) = true := by
  obtain ⟨a, b⟩ := ok_play l ds m y hy
  have hw := ok_drawn zs ds hd
  unfold okRoundsE roundsOf
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  rw [Bool.and_eq_true]
  refine ⟨a p hp, hw p.drawn ?_⟩
  rw [← b]
  exact List.mem_map.2 ⟨p, hp, rfl⟩

/-- The same from the sentence on the prover's side of a sub-protocol's step (`Thread.Moved`).
Conditional on that sentence and on the test on the challenges. -/
theorem okRounds_moved {S Cl V Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    {blk : Block S Cl} {k : Coins Bk} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn} (hM : T.Moved blk k m E ds y cols)
    (hd : drawsFit blk.rounds ds = true) : okRoundsE (roundsOf y.1) = true := by
  obtain ⟨⟨l, _, hy⟩, _⟩ := hM
  exact okRounds_played hy hd

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.ok_tell
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_play
#print axioms ProofFile.Honest.K3.Law.AtThr.okRounds_played
#print axioms ProofFile.Honest.K3.Law.AtThr.okRounds_moved
