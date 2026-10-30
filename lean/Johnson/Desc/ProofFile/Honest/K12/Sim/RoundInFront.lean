-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/RoundInFront.lean: two general sentences, with a helper each,
on the frame's `play` (Honest/Frame.lean), for whoever wants to say what a part IN FRONT of another
has laid in a run: a round among those that a play has produced, and what a part's Step tells.

  `played_len`     as many played rounds as steps
  `played_round`   where `play` returns, at each number i below the rounds' count: the rounds in
                 front are the play of the first i, at a stand mᵢ; the round's Step tells something
                 there; and the played round holds what was told
  `step_move`      the move of a part's Step number k says what the part's move number k says, at
                 the values that the part is handed
  `tell_move`      where a part's Step number k tells something, the part's move number k has
                 returned a message, that message has the shape that the Step states, and what is
                 told is made of it

By what. `play_split` (Honest/Small/PlayedTo.lean), `play_lengths`, `tell_inv`
(Honest/Small/PlayRow.lean), the frame's authors' `play_cons_ok` (Honest/Law/Play.lean): both
sentences are short calls of these.

Limits. No stored run to fall back on (`back := []`). Nothing says that a play returns. General in
the input, the state and the part: no kind of sub-protocol is named. Nothing on completeness,
soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.Small.PlayedTo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.Small (play_split play_lengths tell_inv)

/-- Where `play` has returned, there are as many played rounds as steps. -/
theorem played_len {W X : Type} : ∀ (l : List (Step W X)) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X), play l ds back m = .ok y →
    y.1.length = l.length
  | [], [], _, _, y, h => by
    simp only [play] at h
    rw [← Except.ok.inj h]
    rfl
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: l, d :: ds, back, m, y, h => by
    obtain ⟨x, m', z, -, -, h3, rfl⟩ := play_cons_ok h
    show z.1.length + 1 = l.length + 1
    rw [played_len l ds back.tail m' z h3]

/-- **A round among those that a play has produced.** -/
theorem played_round {W X : Type} (ss : List (Step W X)) (ds : List Fmt.Drawn) (m₀ : Mid W X)
    (y : List Played × Mid W X) (h : play ss ds [] m₀ = .ok y) (i : ℕ) (s : Step W X)
    (hs : ss[i]? = some s) :
    ∃ (mᵢ : Mid W X) (x : Told) (q : Played),
      play (ss.take i) (ds.take i) [] m₀ = .ok (y.1.take i, mᵢ) ∧ s.tell none mᵢ = .ok x ∧
      y.1[i]? = some q ∧ q.tables = x.tables ∧ q.vals = x.vals ∧ q.told = x.told := by
  have hl := play_lengths ss ds [] m₀ y h
  obtain ⟨hi, hsi⟩ := List.getElem?_eq_some_iff.1 hs
  have hid : i < ds.length := hl ▸ hi
  have es : ss.take i ++ s :: ss.drop (i + 1) = ss := by
    rw [← hsi, List.getElem_cons_drop, List.take_append_drop]
  have ed : ds.take i ++ ds[i] :: ds.drop (i + 1) = ds := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have h' : play (ss.take i ++ s :: ss.drop (i + 1)) (ds.take i ++ ds[i] :: ds.drop (i + 1)) []
      m₀ = .ok y := by
    rw [es, ed]
    exact h
  have hlt : (ds.take i).length = (ss.take i).length := by
    rw [List.length_take, List.length_take, hl]
  obtain ⟨y₁, z, e1, e2, rfl⟩ := play_split hlt h'
  obtain ⟨x, m', z', t1, -, -, rfl⟩ := play_cons_ok e2
  have hy : y₁.1.length = i := by
    rw [played_len _ _ _ _ _ e1, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  refine ⟨y₁.2, x,
    ⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals, x.tables, ds[i]⟩,
    ?_, t1, ?_, rfl, rfl, rfl⟩
  · rw [e1]
    show Except.ok y₁ = Except.ok ((y₁.1 ++ _).take i, y₁.2)
    rw [List.take_left' hy]
  · show (y₁.1 ++ _ :: _)[i]? = _
    rw [List.getElem?_append_right (Nat.le_of_eq hy), hy, Nat.sub_self]
    rfl

/-- The move of a part's Step number k. -/
theorem step_move {V W X : Type} (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) (k : ℕ) (s : Step W X)
    (hs : (p.steps name a rs v c)[k]? = some s) (mv : Move p.Coins W X)
    (hmv : p.moves[k]? = some mv) : s.move = some ⟨fun _ => mv.say c, mv.hand⟩ := by
  unfold Part.steps at hs
  rw [List.getElem?_map] at hs
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hs
  rw [List.getElem?_zipIdx] at hr
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hr
  obtain ⟨-, h2⟩ := List.getElem?_zip_eq_some.1 hq
  have e : q.2 = mv := Option.some.inj (h2.symm.trans hmv)
  show some (⟨fun _ => q.2.say c, q.2.hand⟩ : Move Unit W X) = _
  rw [e]

/-- **What a part's Step number k tells is what the part's move number k says**, at the values that
the part is handed: where it returns, the move has returned a message; that message has the shape
that the Step states; and what is told is made of it. General in the part. -/
theorem tell_move {V W X : Type} (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) (k : ℕ) (s : Step W X)
    (hs : (p.steps name a rs v c)[k]? = some s) (mv : Move p.Coins W X)
    (hmv : p.moves[k]? = some mv) (m : Mid W X) (x : Told) (hx : s.tell none m = .ok x) :
    ∃ z : Sending, mv.say c m.shown m.st = .ok z ∧ z.fits s.decl s.oracles = true ∧
      x.tables = z.tables.map some ∧ x.vals = z.vals.map Said.got ∧ x.told = true := by
  obtain ⟨z, h1, h2, rfl⟩ := tell_inv (step_move p name a rs v c k s hs mv hmv) hx
  exact ⟨z, h1, h2, rfl, rfl, rfl⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.played_len
#print axioms ProofFile.Honest.K12.Light.played_round
#print axioms ProofFile.Honest.K12.Light.step_move
#print axioms ProofFile.Honest.K12.Light.tell_move
