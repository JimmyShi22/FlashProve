-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Steps.lean: which rounds `chainSteps` (Honest/Frame.lean)
prepares. One main lemma, `chainSteps_rows`: where `chainSteps` returns, its rounds are, in order,
the sub-protocols' declared rounds with their oracle messages, each at its sub-protocol's place,
with a move exactly where a prover's side is defined at that place.

On the way: `map_zipIdx_fst`, `map_zip_fst`, `any_eq_find` (on lists); `foldl_moves` (the number of
rounds of a list of parts as a sum); `Part.steps_rows`, `rowSteps_rows`, `Placed.steps_rows` (the
same lemma for a part, for a list of parts, and for a prover's side at its sub-protocol).

Limits.
  * Nothing is said of a move's definition, of coins or of stops.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W X : Type}

/-! ## On lists -/

theorem map_zipIdx_fst {α β : Type} (f : α → β) : ∀ (l : List α) (n : Nat),
    (l.zipIdx n).map (fun r => f r.1) = l.map f
  | [], _ => rfl
  | a :: l, n => congrArg (f a :: ·) (map_zipIdx_fst f l (n + 1))

theorem map_zip_fst {α β γ : Type} (f : α → γ) : ∀ (l : List α) (m : List β),
    l.length ≤ m.length → (l.zip m).map (fun r => f r.1) = l.map f
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: l, _ :: m, h => congrArg (f a :: ·) (map_zip_fst f l m (Nat.le_of_succ_le_succ h))

theorem any_eq_find {α : Type} (p : α → Bool) : ∀ l : List α, l.any p = (l.find? p).isSome
  | [] => rfl
  | a :: l => by
    cases h : p a <;> simp [List.any_cons, h, any_eq_find p l]

/-! ## A part, a list of parts -/

theorem foldl_moves : ∀ (ps : List (Part V W X)) (k : Nat),
    ps.foldl (fun n p => n + p.moves.length) k = k + (ps.map (·.moves.length)).sum
  | [], k => by simp
  | p :: ps, k => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_moves ps, Nat.add_assoc]

theorem Part.steps_rows (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins)
    (h : rs.length ≤ p.moves.length) :
    (p.steps name a rs v c).map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) =
      rs.map fun z => (z.1, z.2, a.place, true) := by
  unfold Part.steps
  rw [List.map_map]
  exact (map_zipIdx_fst
    (fun (y : (Fmt.DeclaredRound × List Oracle) × Move (Handed p.takes p.spends p.carries) W X) =>
      (y.1.1, y.1.2, a.place, true)) (rs.zip p.moves) 0).trans
    (map_zip_fst (fun (z : Fmt.DeclaredRound × List Oracle) => (z.1, z.2, a.place, true)) rs p.moves h)

theorem rowSteps_rows (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps), (ps.map (·.moves.length)).sum = rs.length →
    (rowSteps name a v ps j rs c).map
        (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) =
      rs.map fun z => (z.1, z.2, a, true)
  | [], _, rs, _, h => by
    cases rs with
    | nil => rfl
    | cons r rs => simp at h
  | p :: ps, j, rs, c, h => by
    simp only [List.map_cons, List.sum_cons] at h
    have h1 : (rs.take p.moves.length).length ≤ p.moves.length := by
      rw [List.length_take]
      exact Nat.min_le_left _ _
    have h2 : (ps.map (·.moves.length)).sum = (rs.drop p.moves.length).length := by
      rw [List.length_drop]
      omega
    have e1 := Part.steps_rows p name ⟨a, j⟩ (rs.take p.moves.length) v c.1 h1
    have e2 := rowSteps_rows name a v ps (j + 1) (rs.drop p.moves.length) c.2 h2
    show (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
      rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2).map _ = _
    rw [List.map_append, e1, e2, ← List.map_append, List.take_append_drop]

/-- **A prover's side's rounds at its sub-protocol**: if the list of parts has as many moves as the
sub-protocol has rounds, and the sub-protocol has a list of oracle messages for each round (these
are two of the three clauses of `Side.fits`, Honest/Side.lean), they are the sub-protocol's declared
rounds with their oracle messages, at its place, each with a move. -/
theorem Placed.steps_rows (g : Placed V W X) (b : Block S Cl) (v : Option V)
    (c : RowCoins g.parts) (hr : g.rounds = b.rounds.length)
    (ho : b.oracles.length = b.rounds.length) :
    (g.steps b v c).map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) =
      (b.rounds.zip b.oracles).map fun z => (z.1, z.2, b.place, true) := by
  have hsum : (g.parts.map (·.moves.length)).sum = (b.rounds.zip b.oracles).length := by
    unfold Placed.rounds at hr
    rw [foldl_moves, Nat.zero_add] at hr
    rw [hr, List.length_zip, ho, Nat.min_self]
  exact rowSteps_rows b.name b.place v g.parts 0 _ c hsum

/-! ## A chain -/

theorem chainSteps_rows {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} : ∀ (bs : List (Block S Cl)) (hs : List (Placed V W X)) (ss : List (Step W X)),
    chainSteps B rows look v bs hs = .ok ss →
      (∀ b ∈ bs, b.oracles.length = b.rounds.length) ∧
      ss.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) =
        bs.flatMap fun b => (b.rounds.zip b.oracles).map fun z =>
          (z.1, z.2, b.place, hs.any fun h => h.place == b.place)
  | [], hs, ss, h => by
    simp only [chainSteps] at h
    cases h
    exact ⟨fun b hb => (by cases hb), rfl⟩
  | b :: bs, hs, ss, h => by
    simp only [chainSteps] at h
    split at h
    · cases h
    rename_i hlen
    have hlen' : b.oracles.length = b.rounds.length := by simpa using hlen
    have hall : ∀ l, chainSteps B rows look v bs hs = .ok l →
        ∀ b' ∈ b :: bs, b'.oracles.length = b'.rounds.length := by
      intro l hl b' hb'
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact hlen'
      · exact (chainSteps_rows bs hs l hl).1 _ hb'
    split at h
    · rename_i hnone
      cases hrec : chainSteps B rows look v bs hs with
      | error e => simp [hrec, Except.map] at h
      | ok l =>
        simp only [hrec, Except.map] at h
        cases h
        refine ⟨hall l hrec, ?_⟩
        rw [List.flatMap_cons, ← (chainSteps_rows bs hs l hrec).2, any_eq_find, hnone,
          List.map_append, List.map_map]
        rfl
    · rename_i g hg
      split at h
      · cases h
      rename_i hr
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      cases hc : lendRow B rows look b.place g.parts 0 with
      | error e => simp [hc, Except.mapError, Except.bind] at h
      | ok c =>
        cases hrec : chainSteps B rows look v bs hs with
        | error e => simp [hc, hrec, Except.mapError, Except.bind, Except.map] at h
        | ok l =>
          simp only [hc, hrec, Except.mapError, Except.bind, Except.map] at h
          cases h
          refine ⟨hall l hrec, ?_⟩
          have h0 : g.rounds = b.rounds.length := by simpa using hr
          rw [List.flatMap_cons, ← (chainSteps_rows bs hs l hrec).2, any_eq_find, hg,
            List.map_append]
          exact congrArg (· ++ _) (Placed.steps_rows g b v c h0 hlen')

end ProofFile.Honest

#print axioms ProofFile.Honest.map_zipIdx_fst
#print axioms ProofFile.Honest.map_zip_fst
#print axioms ProofFile.Honest.any_eq_find
#print axioms ProofFile.Honest.foldl_moves
#print axioms ProofFile.Honest.Part.steps_rows
#print axioms ProofFile.Honest.rowSteps_rows
#print axioms ProofFile.Honest.Placed.steps_rows
#print axioms ProofFile.Honest.chainSteps_rows
