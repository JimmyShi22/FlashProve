-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/WalkTake.lean: a walk over the first rounds of a chain, held against
the walk over all of them: what the shorter walk has produced is the longer walk's rounds before a
place. A step on the way to the statement `Tie2` (Ties.lean), which names the available tables by
`roundsAhead` of a run's played rounds, where `fieldAt_walk` (FieldWalk.lean) names them by the
rounds that the shorter walk has produced.

  `walk_laid_places`   the places of the rounds produced are the places of the steps walked
  `walk_take`   where a walk returns, so does the walk over its first `n` steps, and what that one
     has produced is a prefix
  `laid_ahead`   **where the steps are cut at a place** (none of the first steps stands at it, the
     next one does) **the shorter walk has produced just `roundsAhead` of the longer one's rounds**

By what, of others: `heard_laid` (Law/WalkOn.lean), `walk_cons_ok`, `walk_append_ok`
(Law/Rule/WalkLaw.lean), `K12.walk_lengths`, `K12.walk_laid_prefix` (K12/LiveField.lean).

Limits.
  * Conditional: nothing shows that a walk returns.
  * The lemmas are about lists of rounds. They prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.WalkHeard
import Johnson.Desc.ProofFile.Honest.Ties
import Johnson.Desc.ProofFile.Honest.K12.LiveField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

variable {S Cl W Y : Type}

/-- The places of the rounds produced are the places of the steps walked. -/
theorem walk_laid_places (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' →
    z'.laid.map (·.place) = z.laid.map (·.place) ++ ss.map (·.addr.place)
  | [], [], z, z', h => by
    obtain rfl := walk_nil_ok h
    simp
  | s :: ss, d :: ds, z, z', h => by
    obtain ⟨x, z₁, -, h1, h2⟩ := walk_cons_ok h
    rw [walk_laid_places L ss ds z₁ z' h2, heard_laid h1, List.map_append, List.map_cons,
      List.append_assoc]
    rfl
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h

/-- Where a walk returns, so does the walk over its first `n` steps; what it has produced is a
prefix. -/
theorem walk_take {L : Lay} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {a z : ChainProgress S Cl W Y}
    (h : walk L ss ds a = .ok z) (n : Nat) :
    ∃ z₁, walk L (ss.take n) (ds.take n) a = .ok z₁ ∧ z₁.laid <+: z.laid := by
  have hl := K12.walk_lengths L ss ds a z h
  have h' : walk L (ss.take n ++ ss.drop n) (ds.take n ++ ds.drop n) a = .ok z := by
    rw [List.take_append_drop, List.take_append_drop]
    exact h
  obtain ⟨z₁, h1, h2⟩ := walk_append_ok (ss.drop n) (ds.drop n) (ss.take n) (ds.take n) a z
    (by rw [List.length_take, List.length_take, hl]) h'
  exact ⟨z₁, h1, K12.walk_laid_prefix L _ _ z₁ z h2⟩

/-- **Where the steps are cut at a place, the shorter walk has produced just the longer one's rounds
before that place.** `ha`: the walks start with no round produced. -/
theorem laid_ahead {L : Lay} {l₁ l' : List (Step W Y)} {s₀ : Step W Y} {ds : List Fmt.Drawn}
    {a z z₁ : ChainProgress S Cl W Y} {p : Place} (ha : a.laid = [])
    (h : walk L (l₁ ++ s₀ :: l') ds a = .ok z)
    (h1 : walk L ((l₁ ++ s₀ :: l').take l₁.length) (ds.take l₁.length) a = .ok z₁)
    (hn : ∀ s ∈ l₁, s.addr.place ≠ p) (h0 : s₀.addr.place = p) :
    z₁.laid = roundsAhead z.laid p := by
  obtain ⟨z₁', h1', r, hr⟩ := walk_take h l₁.length
  obtain rfl : z₁' = z₁ := Except.ok.inj (h1'.symm.trans h1)
  have e1 := walk_laid_places L _ _ a z₁' h1
  have e2 := walk_laid_places L _ _ a z h
  rw [ha, List.map_nil, List.nil_append, List.take_left] at e1
  rw [ha, List.map_nil, List.nil_append, ← hr, List.map_append, List.map_append, e1] at e2
  have e3 := List.append_cancel_left e2
  have n1 : ∀ q ∈ z₁'.laid, (q.place != p) = true := by
    intro q hq
    have hq' : q.place ∈ z₁'.laid.map (·.place) := List.mem_map.2 ⟨q, hq, rfl⟩
    rw [e1] at hq'
    obtain ⟨s, hs, es⟩ := List.mem_map.1 hq'
    rw [bne_iff_ne, ← es]
    exact hn s hs
  cases r with
  | nil => simp at e3
  | cons q r' =>
    have eq : q.place = p := by
      simp only [List.map_cons, List.cons.injEq] at e3
      rw [e3.1, h0]
    unfold roundsAhead
    rw [← hr, List.takeWhile_append_of_pos n1, List.takeWhile_cons_of_neg, List.append_nil]
    rw [eq]
    simp

end ProofFile.Honest

#print axioms ProofFile.Honest.walk_laid_places
#print axioms ProofFile.Honest.walk_take
#print axioms ProofFile.Honest.laid_ahead
