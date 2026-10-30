-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Dry.lean: the part of the state of a chain's run that reads
no coin and nothing that was sent (Honest/Frame.lean: `Mid.st`, `Mid.loc`), as a fold of
`State.hears` and `Move.hand` alone: no coin, no message and no test of the verifier's is among its
arguments. And `play` and `midIn` lead to exactly that fold's value, where they return without an
error (`play_dry`, `midIn_dry`).

  1  `dryStep`, `dryFold`, `Step.hand`, `hear_dry`, `play_dry`   the fold; after a run of `play`
  2  `Step.key`, `rowKeys`, `chainKeys`, `Part.steps_keys`, `rowSteps_keys`,
     `chainSteps_keys`   each round's address and what it passes on, computed from the description's
     list and the prover's sides alone, whatever coins `chainSteps` has put in
  3  `takeWhile_key`, `any_key`, `midIn_dry`   before the part at an address

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Steps
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place Oracle)

variable {S Cl V W X : Type}

/-! ## 1 The fold -/

/-- The state after a round's challenge. `h`: what the round's move passes on, if it has a move. -/
def dryStep (h : Option (State W X → X)) (d : Fmt.Drawn) (t : State W X) : State W X :=
  match h with
  | some f => { t.hears d with own := f (t.hears d) }
  | none => t.hears d

/-- The state after several rounds' challenges. Where the two lists differ in length, it ends with
the shorter one. -/
def dryFold : List (Option (State W X → X)) → List Fmt.Drawn → State W X → State W X
  | h :: hs, d :: ds, t => dryFold hs ds (dryStep h d t)
  | _, _, t => t

/-- What a round's move passes on. -/
def Step.hand (s : Step W X) : Option (State W X → X) := s.move.map (·.hand)

theorem hear_dry {s : Step W X} {x : Told} {d : Fmt.Drawn} {m m' : Mid W X}
    (h : s.hear x d m = .ok m') : m'.st = dryStep s.hand d m.st ∧ m'.loc = m.loc ++ [d] := by
  unfold Step.hear at h
  unfold Step.hand dryStep
  cases hm : s.move with
  | none =>
    simp only [hm] at h
    cases h
    exact ⟨rfl, rfl⟩
  | some mv =>
    simp only [hm] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl⟩

/-- **After a run of `play`**: the state is the fold's; the challenges that the stops may read are
the earlier ones and the run's own. -/
theorem play_dry : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play ss ds back m = .ok y →
    y.2.st = dryFold (ss.map Step.hand) ds m.st ∧ y.2.loc = m.loc ++ ds
  | [], [], _, m, y, h => by
    simp only [play] at h
    cases h
    exact ⟨rfl, (List.append_nil _).symm⟩
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: ss, d :: ds, back, m, y, h => by
    obtain ⟨x, m', z, -, hm, hz, rfl⟩ := play_cons_ok h
    obtain ⟨a1, a2⟩ := hear_dry hm
    obtain ⟨b1, b2⟩ := play_dry ss ds back.tail m' z hz
    refine ⟨?_, ?_⟩
    · show z.2.st = dryFold (s.hand :: ss.map Step.hand) (d :: ds) m.st
      rw [b1, a1]
      rfl
    · show z.2.loc = m.loc ++ d :: ds
      rw [b2, a2, List.append_assoc]
      rfl

/-! ## 2 Each round's address and what it passes on -/

/-- A round's address, and what its move passes on. -/
def Step.key (s : Step W X) : Addr × Option (State W X → X) := (s.addr, s.hand)

/-- The same for a list of parts. `j`: the first part's number. `rs`: the place's rounds from there
on. -/
def rowKeys (a : Place) : List (Part V W X) → Nat → List (Fmt.DeclaredRound × List Oracle) →
    List (Addr × Option (State W X → X))
  | [], _, _ => []
  | p :: ps, j, rs =>
    ((rs.take p.moves.length).zip p.moves).map (fun z => ((⟨a, j⟩ : Addr), some z.2.hand)) ++
      rowKeys a ps (j + 1) (rs.drop p.moves.length)

/-- The same for a chain, computed from the description's list and the prover's sides alone. At a
place without a prover's side each round gets the part number 0 and `none`: there is no move. -/
def chainKeys (bs : List (Block S Cl)) (hs : List (Placed V W X)) :
    List (Addr × Option (State W X → X)) :=
  bs.flatMap fun b =>
    match hs.find? fun h => h.place == b.place with
    | none => (b.rounds.zip b.oracles).map fun _ => ((⟨b.place, 0⟩ : Addr), none)
    | some h => rowKeys b.place h.parts 0 (b.rounds.zip b.oracles)

theorem Part.steps_keys (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    (p.steps name a rs v c).map Step.key = (rs.zip p.moves).map fun z => (a, some z.2.hand) := by
  unfold Part.steps
  rw [List.map_map]
  exact map_zipIdx_fst
    (fun (y : (Fmt.DeclaredRound × List Oracle) × Move (Handed p.takes p.spends p.carries) W X) =>
      (a, some y.2.hand)) (rs.zip p.moves) 0

theorem rowSteps_keys (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps), (rowSteps name a v ps j rs c).map Step.key = rowKeys a ps j rs
  | [], _, _, _ => rfl
  | p :: ps, j, rs, c => by
    show (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
      rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2).map Step.key = _
    rw [List.map_append, Part.steps_keys, rowSteps_keys name a v ps (j + 1) _ c.2]
    rfl

/-- **Whatever coins `chainSteps` has put in**, its rounds' addresses and what they pass on are
these. -/
theorem chainSteps_keys {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} : ∀ (bs : List (Block S Cl)) (hs : List (Placed V W X)) (ss : List (Step W X)),
    chainSteps B rows look v bs hs = .ok ss → ss.map Step.key = chainKeys bs hs
  | [], hs, ss, h => by
    simp only [chainSteps] at h
    cases h
    rfl
  | b :: bs, hs, ss, h => by
    simp only [chainSteps] at h
    split at h
    · cases h
    split at h
    · rename_i hnone
      cases hrec : chainSteps B rows look v bs hs with
      | error e => simp [hrec, Except.map] at h
      | ok l =>
        simp only [hrec, Except.map] at h
        cases h
        unfold chainKeys
        rw [List.flatMap_cons, hnone, List.map_append, List.map_map]
        exact congrArg₂ (· ++ ·) rfl (chainSteps_keys bs hs l hrec)
    · rename_i g hg
      split at h
      · cases h
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
          unfold chainKeys
          rw [List.flatMap_cons, hg, List.map_append]
          exact congrArg₂ (· ++ ·) (rowSteps_keys b.name b.place v g.parts 0 _ c)
            (chainSteps_keys bs hs l hrec)

/-! ## 3 Before the part at an address -/

theorem takeWhile_key (a : Addr) : ∀ ss : List (Step W X),
    (ss.takeWhile fun s => s.addr != a).length =
      ((ss.map Step.key).takeWhile fun y => y.1 != a).length
  | [] => rfl
  | s :: ss => by
    have hk : ((Step.key s).1 != a) = (s.addr != a) := rfl
    cases h : s.addr != a with
    | true =>
      have h' : ((Step.key s).1 != a) = true := hk.trans h
      simp only [List.map_cons, List.takeWhile_cons, h, h', if_true, List.length_cons,
        takeWhile_key a ss]
    | false =>
      have h' : ((Step.key s).1 != a) = false := hk.trans h
      simp only [List.map_cons, List.takeWhile_cons, h, h', Bool.false_eq_true, if_false]
      rfl

theorem any_key (a : Addr) (ss : List (Step W X)) :
    ss.any (·.addr == a) = (ss.map Step.key).any (·.1 == a) := by
  rw [List.any_map]
  rfl

/-- **The state of a chain's run before the part at an address**: state and challenges are computed
from the rounds' keys, the challenges and the start alone. -/
theorem midIn_dry {ss : List (Step W X)} {ds : List Fmt.Drawn} {back : List Fmt.RoundView}
    {m m' : Mid W X} {a : Addr} (h : midIn ss ds back m a = .ok m') :
    m'.st = dryFold (((ss.map Step.key).take
        ((ss.map Step.key).takeWhile fun y => y.1 != a).length).map (·.2))
        (ds.take ((ss.map Step.key).takeWhile fun y => y.1 != a).length) m.st ∧
      m'.loc = m.loc ++ ds.take ((ss.map Step.key).takeWhile fun y => y.1 != a).length := by
  unfold midIn at h
  obtain ⟨-, h⟩ := exIte_ok h
  obtain ⟨y, hy, rfl⟩ := exMap_ok h
  obtain ⟨e1, e2⟩ := play_dry _ _ _ _ _ hy
  rw [takeWhile_key a ss] at e1 e2
  have e : ∀ n : Nat, ((ss.map Step.key).take n).map (·.2) = (ss.take n).map Step.hand := by
    intro n
    simp [List.map_take, List.map_map, Function.comp_def, Step.key]
  exact ⟨by rw [e1, e], e2⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.hear_dry
#print axioms ProofFile.Honest.play_dry
#print axioms ProofFile.Honest.Part.steps_keys
#print axioms ProofFile.Honest.rowSteps_keys
#print axioms ProofFile.Honest.chainSteps_keys
#print axioms ProofFile.Honest.takeWhile_key
#print axioms ProofFile.Honest.any_key
#print axioms ProofFile.Honest.midIn_dry
