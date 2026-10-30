-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverNew.lean: WHAT A CANONICAL GATE's TEST SAYS ANEW. The
canonical gates' tests (Honest/Law/CoverChain.lean) ask «by the chain's first n rounds the run has
met a fall». Here: where that is false at n and true at n + k: the walk over the first n rounds
holds a verifier's state s', and THE MEMBERS THAT ARE STILL TO DO MEET A FALL FROM s', ON THE ROUNDS
AND COLUMNS LAID SINCE. So what is asked at a gate is a sentence on the members from that gate's own
on, at one state in front: no earlier member, no earlier round.

WHAT THIS IS. Lemmas on the frame's own `frontsOf`, `chainFall` (Honest/Fall.lean) and `walk`
(Honest/Walk.lean), and on the library's `foldBlocks`. No measure is in this file. None of the
library's goals.

  1  `frontsOf_cons`, `frontsOf_few`, `frontsOf_err`, `frontsOf_ok`   one member
  2  `behind`, `fronts_append`   the states in front of pre ++ rest: those of pre, then those of
     rest from the fold's end
  3  `new_entry`   on views
  4  `new_fall`   on walks

BESIDE WHOSE LEMMAS. Another thread of this project has typed, on the same `frontsOf`: frontsOf_fold
| frontsOf_local (Honest/K8/FrontsAgree.lean), frontsOf_zero | frontsOf_step (FrontsStep.lean),
frontsOf_drop | frontsOf_between (FrontsBetween.lean; the three files are not in the sealed
library): they take an entry of one list apart. `fronts_append` says what the whole list over pre ++
rest is; none of theirs is repeated here. From `new_fall`'s end their frontsOf_zero | frontsOf_step
lead on to «the member's own step returns t».

Limits. Nothing says that the state s' meets a thread's sentence. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverFile
import Johnson.Desc.ProofFile.Honest.Law.WalkFold
import Johnson.Desc.ProofFile.Honest.Law.AcceptC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl W Y : Type}

/-! ## 1 One member -/

theorem frontsOf_cons (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) : frontsOf ft (b :: l) s rs cols =
      if (rs.take b.rounds.length).length != b.rounds.length then [] else
      (b.place, s, (rs.take b.rounds.length).map (·.drawn)) ::
        match b.step ft s (rs.take b.rounds.length) cols with
        | .error _ => []
        | .ok (s', k) => frontsOf ft l s' (rs.drop b.rounds.length) (cols.drop k) := by
  conv_lhs => unfold frontsOf
  rfl

theorem frontsOf_few (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : rs.length < b.rounds.length) :
    frontsOf ft (b :: l) s rs cols = [] := by
  rw [frontsOf_cons, if_pos]
  rw [List.length_take, Nat.min_eq_right (Nat.le_of_lt h)]
  exact bne_iff_ne.2 (Nat.ne_of_lt h)

theorem frontsOf_err (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (e : String)
    (hm : (rs.take b.rounds.length).length = b.rounds.length)
    (hs : b.step ft s (rs.take b.rounds.length) cols = .error e) :
    frontsOf ft (b :: l) s rs cols = [(b.place, s, (rs.take b.rounds.length).map (·.drawn))] := by
  rw [frontsOf_cons, if_neg (by rw [hm]; simp), hs]

theorem frontsOf_ok (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s s' : S) (k : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hm : (rs.take b.rounds.length).length = b.rounds.length)
    (hs : b.step ft s (rs.take b.rounds.length) cols = .ok (s', k)) :
    frontsOf ft (b :: l) s rs cols = (b.place, s, (rs.take b.rounds.length).map (·.drawn)) ::
      frontsOf ft l s' (rs.drop b.rounds.length) (cols.drop k) := by
  rw [frontsOf_cons, if_neg (by rw [hm]; simp), hs]

/-! ## 2 pre ++ rest -/

/-- The states in front of the members of rest, from a fold's end; none where the fold refuses. -/
def behind (ft : Nat) (rest : List (Block S Cl)) (r₂ : List Fmt.RoundView) (c₂ : List OpenedColumn) :
    Except String (S × List Fmt.RoundView × List OpenedColumn) → List (Place × S × List Fmt.Drawn)
  | .ok z => frontsOf ft rest z.1 r₂ c₂
  | .error _ => []

/-- **The states in front of the members of pre ++ rest**: those of pre, over pre's own rounds and
owed columns; then those of rest, from the fold's end over pre, over what stands behind. -/
theorem fronts_append (ft : Nat) (rest : List (Block S Cl)) (r₂ : List Fmt.RoundView) (c₂ : List OpenedColumn) :
    ∀ (pre : List (Block S Cl)) (s : S) (r₁ : List Fmt.RoundView) (c₁ : List OpenedColumn),
    r₁.length = (pre.flatMap (·.rounds)).length → c₁.length = owed ft pre r₁ →
    frontsOf ft (pre ++ rest) s (r₁ ++ r₂) (c₁ ++ c₂) =
      frontsOf ft pre s r₁ c₁ ++ behind ft rest r₂ c₂ (foldBlocks ft pre s r₁ c₁)
  | [], s, r₁, c₁, hr, hc => by
    have e1 : r₁ = [] := List.eq_nil_of_length_eq_zero hr
    have e2 : c₁ = [] := by
      rw [owed_nil] at hc
      exact List.eq_nil_of_length_eq_zero hc
    subst e1
    subst e2
    rfl
  | b :: pre, s, r₁, c₁, hr, hc => by
    rw [List.flatMap_cons, List.length_append] at hr
    rw [owed_cons] at hc
    have hn : b.rounds.length ≤ r₁.length := by omega
    have hw : (b.want ft (r₁.take b.rounds.length)).length ≤ c₁.length := by omega
    have hm : (r₁.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    have hm' : ((r₁ ++ r₂).take b.rounds.length).length = b.rounds.length := by
      rw [List.take_append_of_le_length hn]
      exact hm
    rw [List.cons_append, foldBlocks_eq, if_neg (by rw [hm]; simp)]
    cases hs : b.step ft s (r₁.take b.rounds.length) c₁ with
    | error e =>
      have hs' : b.step ft s ((r₁ ++ r₂).take b.rounds.length) (c₁ ++ c₂) = .error e := by
        rw [List.take_append_of_le_length hn, step_more ft b s _ c₁ c₂ hw]
        exact hs
      rw [frontsOf_err ft b _ s _ _ e hm' hs', frontsOf_err ft b _ s _ _ e hm hs,
        List.take_append_of_le_length hn]
      rfl
    | ok z =>
      obtain ⟨s', k⟩ := z
      have hk := ((step_iff ft b s s' _ c₁ k).1 hs).2.2
      subst hk
      have hs' : b.step ft s ((r₁ ++ r₂).take b.rounds.length) (c₁ ++ c₂) =
          .ok (s', (b.want ft (r₁.take b.rounds.length)).length) := by
        rw [List.take_append_of_le_length hn, step_more ft b s _ c₁ c₂ hw]
        exact hs
      rw [frontsOf_ok ft b _ s s' _ _ _ hm' hs', frontsOf_ok ft b _ s s' _ _ _ hm hs,
        List.take_append_of_le_length hn, List.drop_append_of_le_length hn,
        List.drop_append_of_le_length hw,
        fronts_append ft rest r₂ c₂ pre s' _ _ (by rw [List.length_drop]; omega)
          (by rw [List.length_drop]; omega)]
      rfl

/-! ## 3 On views -/

/-- **A fall that is met anew is met by the members behind, from the fold's end.** r₁, c₁: pre's own
rounds and owed columns. u, v: what a shorter view has behind them; r₂, c₂: a longer one. The
shorter view lists no member of rest. -/
theorem new_entry (fs : List (Fall S)) (ft : Nat) (pre rest : List (Block S Cl)) (s : S)
    (r₁ u r₂ : List Fmt.RoundView) (c₁ v c₂ : List OpenedColumn)
    (hr : r₁.length = (pre.flatMap (·.rounds)).length) (hc : c₁.length = owed ft pre r₁)
    (h0 : chainFall fs ft (pre ++ rest) s ⟨r₁ ++ u, c₁ ++ v⟩ = none)
    (h1 : (chainFall fs ft (pre ++ rest) s ⟨r₁ ++ r₂, c₁ ++ c₂⟩).isSome = true) :
    ∃ z, foldBlocks ft pre s r₁ c₁ = .ok z ∧ (chainFall fs ft rest z.1 ⟨r₂, c₂⟩).isSome = true := by
  unfold chainFall at h0 h1
  simp only at h0 h1
  rw [fronts_append ft rest u v pre s r₁ c₁ hr hc, List.findSome?_append] at h0
  rw [fronts_append ft rest r₂ c₂ pre s r₁ c₁ hr hc, List.findSome?_append] at h1
  have a0 := (or_none h0).1
  rw [a0] at h1
  cases hf : foldBlocks ft pre s r₁ c₁ with
  | error e =>
    rw [hf] at h1
    cases h1
  | ok z =>
    rw [hf] at h1
    exact ⟨z, rfl, h1⟩

/-! ## 4 On walks -/

/-- **WHAT A CANONICAL GATE's TEST SAYS ANEW.** z: the walk over the rounds in front; z': the walk
on from there. v₀: the chain's first state. Where the view of what z has laid meets no fall and that
of z' meets one: z holds a verifier's state s', and the members that z has still to do meet a fall
from s' on the rounds that z has laid for the first of them and those laid since, and on the columns
filled since. -/
theorem new_fall (fs : List (Fall S)) (L : Lay) (bs : List (Block S Cl)) (s₀ : S)
    {z z' : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    (ht : ChainProgress.Tied L bs (some s₀) z.todo z) (hw : walk L ss ds z = .ok z')
    (h0 : chainFall fs L.firstTree bs s₀ ⟨roundsOf z.laid, z.cols⟩ = none)
    (h1 : (chainFall fs L.firstTree bs s₀ ⟨roundsOf z'.laid, z'.cols⟩).isSome = true) :
    ∃ s' ps cs, z.ver = some s' ∧ z'.laid = z.laid ++ ps ∧ z'.cols = z.cols ++ cs ∧
      (chainFall fs L.firstTree z.todo s' ⟨roundsOf (z.own ++ ps), cs⟩).isSome = true := by
  obtain ⟨done, front, e1, e2, e3, e4, e5⟩ := ht
  obtain ⟨ps, cs, g1, g2⟩ := walk_grows L ss ds z z' hw
  have hr : (roundsOf front).length = (done.flatMap (·.rounds)).length := by
    rw [roundsOf_length]
    exact e3
  have h0' : chainFall fs L.firstTree (done ++ z.todo) s₀
      ⟨roundsOf front ++ roundsOf z.own, z.cols ++ []⟩ = none := by
    rw [← e1, ← roundsOf_append, ← e2, List.append_nil]
    exact h0
  have h1' : (chainFall fs L.firstTree (done ++ z.todo) s₀
      ⟨roundsOf front ++ roundsOf (z.own ++ ps), z.cols ++ cs⟩).isSome = true := by
    rw [← e1, ← roundsOf_append, ← List.append_assoc, ← e2, ← g1, ← g2]
    exact h1
  obtain ⟨y, hy, hz⟩ := new_entry fs L.firstTree done z.todo s₀ _ _ _ _ _ _ hr e4 h0' h1'
  refine ⟨y.1, ps, cs, ?_, g1, g2, hz⟩
  rw [e5]
  show (foldBlocks L.firstTree done s₀ (roundsOf front) z.cols).toOption.map (·.1) = some y.1
  rw [hy]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.frontsOf_cons
#print axioms ProofFile.Honest.frontsOf_few
#print axioms ProofFile.Honest.frontsOf_err
#print axioms ProofFile.Honest.frontsOf_ok
#print axioms ProofFile.Honest.fronts_append
#print axioms ProofFile.Honest.new_entry
#print axioms ProofFile.Honest.new_fall
