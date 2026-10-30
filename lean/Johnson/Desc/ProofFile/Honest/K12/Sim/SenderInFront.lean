-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/SenderInFront.lean: the tables of a sending's first round, as
played, in front of a later round of the shared chain: where the frame's `ready` has returned, the
filling's side at a sub-protocol's place is one lifted sending's part, by the authors of the honest
side of the linear claim's shared rounds (K14) (`sendingPart`, Honest/K14/Sendings.lean), and `play`
has returned over rounds that reach beyond that sub-protocol's first: the played round holds
`sentTables` at the rows that the sending's job makes of the stand in front of that round and of the
part's own values; and these values are the cut of the part's own row of the book's look-up. General
in the description, the book, the filling and the sending's job.

OF WHAT KIND IT IS. A tie between terms: it names no value and states no law over random values.
With `cuts_atU` (CutOfBookAt.lean) it becomes a tie between what one part is handed of a run's
values and what another part is handed of them.

  `own_of_lendPart`   what a part is handed as its own is the cut of its own row of the look-up
  `send_first_says`   the first move of a sending's part, lifted: no item in the clear; the tables
  `sender_in_front`   the statement

By what. `block_steps_at_ready` (FirstPlayAtRun.lean); `played_round`, `tell_move`
(Sim/RoundInFront.lean); the frame's authors' `lendRow_cons_ok` (Honest/Law/Rule/RowModel.lean),
`exBind_ok`, `exMap_ok` (Honest/Law/Play.lean).

Limits. That the sender "was called" is not asked: all rounds in front of a stand that `play`
returns are play's own. Nothing says that `ready` or `play` returns, or that a filling holds such a
side. The premise hplay is a `play` from the chain's start over several sub-protocols; of the walk
(`runC`) nothing is said here: `played_at_run` (Sim/PlayedAtRun.lean) ends in a walk, not in such a
play. The first round alone. What a table's column is in words is not treated. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.RoundInFront
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtRun
import Johnson.Desc.ProofFile.Honest.K14.Sendings

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block FileDescription Oracle)
open ProofFile.Honest
open ProofFile.Honest.K14 (SendJob sendingPart sentTables takesOf Ask)

/-- **What a part is handed as its own is the cut of its own row of the look-up.** By `lendPart`'s
text. -/
theorem own_of_lendPart {V W X : Type} {Bk : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {a : Addr} {p : Part V W X} {c : p.Coins}
    (h : lendPart Bk rows look a p = .ok c) : (look a).2.cut ⟨0, 0⟩ p.takes = some c.1 := by
  unfold lendPart at h
  simp only at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i own hown
  obtain ⟨sp, -, h⟩ := exBind_ok h
  obtain ⟨ca, -, e⟩ := exMap_ok h
  subst e
  exact hown

/-- **The first move of a sending's part, lifted**: it says no item in the clear and the tables
`sentTables` at the rows that the sending's job makes of the narrowed state and the part's own
values. -/
theorem send_first_says {V W X : Type} (J : SendJob) (see : V → Empty) (wit : W → Ask)
    (get : X → Unit) (set : X → Unit → X)
    (c : ((sendingPart J).lift see wit get set : Part V W X).Coins) (sn : Seen) (t : State W X) :
    ∃ mv, ((sendingPart J).lift see wit get set : Part V W X).moves[0]? = some mv ∧
      mv.say c sn t = .ok ⟨[], sentTables J.Q.codes J.Q.sent
        (J.rows (t.narrow wit get) (coinsE c.1).toArray)⟩ := ⟨_, rfl, rfl⟩

/-- **THE TABLES OF A SENDING's FIRST ROUND, AS PLAYED, IN FRONT OF A LATER ROUND.** `ready` has
returned R. b: a sub-protocol of the shared chain, with pre in front; the filling's side at its
place is one lifted sending's part (hg). n: a number of rounds beyond b's first. `play` over the
first n rounds has returned (pl, m). Then, with i the number of the rounds in front of b: there are
the stand that `play` returns over the first i rounds, the part's own values, which are the cut of
the part's own row of the book's look-up, and the played round number i, whose tables are
`sentTables` at the rows that the job makes of that stand's input and challenges heard and of these
values. -/
theorem sender_in_front {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (J : SendJob) (wit : Common W₀ Rc Ky → Ask) (set : X₀ → Unit → X₀)
    (hg : (P.shared.find? fun g => g.place == b.place) =
      some ⟨b.place, [(sendingPart J).lift (fun v => v) wit (fun _ => ()) set]⟩)
    (n : ℕ) (hn : (pre.flatMap (·.rounds)).length < n) (pl : List Played)
    (m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
    (hplay : play (R.shared.take n) (ρ.shared.take n) [] (R.start₂ P) = .ok (pl, m)) :
    ∃ (mᵢ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (own : Cs (takesOf J.Q.codes J.Q.sent J.sort)) (q : Played),
      play (R.shared.take (pre.flatMap (·.rounds)).length)
          (ρ.shared.take (pre.flatMap (·.rounds)).length) [] (R.start₂ P) =
        .ok (pl.take (pre.flatMap (·.rounds)).length, mᵢ) ∧
      (sharedLook Bk k.shared ⟨b.place, 0⟩).2.cut ⟨0, 0⟩ (takesOf J.Q.codes J.Q.sent J.sort) =
        some own ∧
      pl[(pre.flatMap (·.rounds)).length]? = some q ∧
      q.tables = (sentTables J.Q.codes J.Q.sent
        (J.rows ⟨wit mᵢ.st.input, mᵢ.st.heard, ()⟩ (coinsE own).toArray)).map some := by
  obtain ⟨c, l₁, l₂, hl, hsh, hl₁, hor⟩ := block_steps_at_ready hR pre b t hcut _ hg
  obtain ⟨hlp, -⟩ := lendRow_cons_ok hl
  -- the first row of the sub-protocol
  obtain ⟨d, ds, hd⟩ : ∃ d ds, b.rounds = d :: ds := by
    cases hr : b.rounds with
    | nil => exact absurd hr hb
    | cons d ds => exact ⟨d, ds, rfl⟩
  obtain ⟨o, os, ho⟩ : ∃ o os, b.oracles = o :: os := by
    cases hr : b.oracles with
    | nil =>
      rw [hr, hd] at hor
      cases hor
    | cons o os => exact ⟨o, os, rfl⟩
  -- the Step at the number i
  have e1 : (⟨b.place, [(sendingPart J).lift (fun v => v) wit (fun _ => ()) set]⟩ :
      Placed Empty (Common W₀ Rc Ky) X₀).steps b (Face.shared.sees R.common) c =
      ((sendingPart J).lift (fun v => v) wit (fun _ => ()) set :
        Part Empty (Common W₀ Rc Ky) X₀).steps b.name ⟨b.place, 0⟩
          ((b.rounds.zip b.oracles).take 2) (Face.shared.sees R.common) c.1 ++ [] := rfl
  obtain ⟨s, rest, e2⟩ : ∃ s rest,
      ((sendingPart J).lift (fun v => v) wit (fun _ => ()) set :
        Part Empty (Common W₀ Rc Ky) X₀).steps b.name ⟨b.place, 0⟩
          ((b.rounds.zip b.oracles).take 2) (Face.shared.sees R.common) c.1 = s :: rest := by
    rw [hd, ho]
    exact ⟨_, _, rfl⟩
  have hs0 : (((sendingPart J).lift (fun v => v) wit (fun _ => ()) set :
      Part Empty (Common W₀ Rc Ky) X₀).steps b.name ⟨b.place, 0⟩
        ((b.rounds.zip b.oracles).take 2) (Face.shared.sees R.common) c.1)[0]? = some s := by
    rw [e2]
    rfl
  have hs : (R.shared.take n)[(pre.flatMap (·.rounds)).length]? = some s := by
    rw [List.getElem?_take_of_lt hn, hsh, e1, e2, ← hl₁,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  obtain ⟨mᵢ, x', q, h1, h2, h3, h4, -, -⟩ := played_round _ _ _ _ hplay _ s hs
  obtain ⟨mv, hmv, hsay⟩ := send_first_says (V := Empty) J (fun v => v) wit (fun _ => ()) set c.1
    mᵢ.shown mᵢ.st
  obtain ⟨z, hz, -, hzt, -, -⟩ := tell_move _ _ _ _ _ c.1 0 s hs0 mv hmv mᵢ x' h2
  obtain rfl := Except.ok.inj (hz.symm.trans hsay)
  refine ⟨mᵢ, c.1.1, q, ?_, own_of_lendPart hlp, h3, h4.trans hzt⟩
  rw [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hn)] at h1
  exact h1

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.own_of_lendPart
#print axioms ProofFile.Honest.K12.Light.send_first_says
#print axioms ProofFile.Honest.K12.Light.sender_in_front
