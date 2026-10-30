-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/DealMade.lean: the test on the plan `dealOk` (DealOk.lean) says yes wherever
the block's own test on the plan does.

Statements and proofs.
Main names:
  `ownN_eq`: the test sends one tree beside its switches' where the first fold sends its own mask,
    else none.
  `oneL_ok`, `cuts`, `fold_none`, `walk_later`: the clauses of dealOk's walk, at the rounds as
    MadeRounds.lean writes them out. `ok_app`, `ok_tag`: tools.
  `dealOk_made`: H2U.roundsOfNums p.nums = some rds and p.oracles.length = rds.length give dealOk p
    = true.
  `rounds_of_planOk`: these two premises are clauses of the frame's test on the plan (`proximityTestKind`,
    Johnson/Desc/K12/Frame.lean), whatever the parts.
  `dealOk_of_planOk`: (proximityTestKind X p).planOk = true gives dealOk p = true, whatever the parts X.
What it means: `dealOk_made` holds at every p whose numbers give rounds, with as many lists of
oracle messages. So dealOk was never a test of a place: it holds the text that makes the rounds
(roundsOfNums) against the law's arithmetic of dealing, and no plan whose numbers give rounds, with
as many lists of oracle messages, can fail it. The controls of DealOk.lean's lines that come out
false spoil dealOn's arguments, not p.
What it pays: the premise hdeal : dealOk p = true of `accK_yes_place`, `accK_yes_real_const`,
`accK_yes_real_own` (AccKPlace.lean, AccKConst.lean, AccKOwn.lean) and of what they call; and, in
four files: the fields AtPlace.deal (Johnson/Desc/K12/Coin/Sheet.lean)
and AtPlaceOwn.deal (Johnson/Desc/K12/Coin/OwnArm.lean),
each beside its own field planOk; the fifth conjunct of PlaceB
(Johnson/Desc/K12/Coin/Bools.lean) and of PlaceOwnB
(Johnson/Desc/K12/Coin/BoolsOwn.lean).
Limits: dealOk is not the constant true: where the numbers give no rounds, or the lists of oracle
messages are fewer than the rounds, it says no (by reading DealOk.lean; no theorem here shows it; in
a run it came out false at 30 of 420 places with a number changed). That planOk says yes at a real
place is not shown here: it has been seen in runs only. No soundness is claimed, and nothing is said
on hiding.
-/
import Johnson.Desc.K12.Law.MadeRounds

set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (rEps rTwo rSeed rCs rLambda rBase laterRounds wMid)
open H2K.First

theorem ok_app (a b : Clauses) : ok (a ++ b) = true ↔ ok a = true ∧ ok b = true := by
  unfold ok
  rw [List.all_append, Bool.and_eq_true]

theorem ok_tag (j : Nat) (l : Clauses) : ok (tagJ j l) = ok l := by
  unfold ok tagJ
  rw [List.all_map]
  rfl

/-- The trees that the test sends beside its switches': one where the first fold sends its own
mask, else none. -/
theorem ownN_eq (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = s :: next :: rest) : ownN p = if p.nums.ownMask then 1 else 0 := by
  unfold ownN H2U.TestNums.sent
  rw [hs]
  cases p.nums.ownMask <;> simp

/-- The five clauses on a later stage's one opening, at the tree as it is told. -/
theorem oneL_ok (p : P12) (j : Nat) (cut : List Fmt.DeclaredRound) (a W : Nat)
    (hs : p.nums.sent[ownN p + (j - 1)]? = some (a, W))
    (hf : cut.flatMap (·.opens) = [p.nums.own a W (p.nums.free + (ownN p + (j - 1)))])
    (hst : cut.all (·.stored.isEmpty) = true) : ok (oneL p 0 j cut) = true := by
  unfold oneL
  simp only [hf]
  simp [ok, hst, hs, H2U.TestNums.own, Nat.add_assoc]

theorem cuts (l : Laid) (A : List Fmt.DeclaredRound) (S C : Fmt.DeclaredRound) (R' : List Fmt.DeclaredRound)
    (k : Nat) (hA : A.length = 1 + k) (hl : l.map (·.1) = A ++ (S :: C :: R')) :
    (l.take (1 + k)).map (·.1) = A ∧ ((l.drop (1 + k)).take 2).map (·.1) = [S, C] ∧
      (l.drop (k + 3)).map (·.1) = R' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_take, hl, List.take_left' hA]
  · rw [List.map_take, List.map_drop, hl, List.drop_left' hA]
    rfl
  · have e : k + 3 = (1 + k) + 2 := by omega
    rw [List.map_drop, hl, e, ← List.drop_drop, List.drop_left' hA]
    rfl

theorem fold_none (e e' : Fmt.Entry) (k : Nat) :
    nOpenB ((⟨e, [], []⟩ : Fmt.DeclaredRound) :: List.replicate k (⟨e', [], []⟩ : Fmt.DeclaredRound)) = 0
        := by
  simp [nOpenB]

/-- The walk from a stage j ≥ 1 on. -/
theorem walk_later (p : P12) (own : Bool) (work : Nat) : ∀ (rest : List Fmt.M1.Stage)
    (cur : Fmt.M1.Stage) (j tree W : Nat) (l : Laid) (R : List Fmt.DeclaredRound), j ≠ 0 →
    H2U.layOpens own true (laterRounds work tree W cur rest)
      (((told p.nums).drop (ownN p + (j - 1))).map ([·])) = some R →
    l.map (·.1) = R → ok (dealWalk p 0 j cur rest l) = true
  | [], cur, j, tree, W, l, R, hj, h, hl => by
    obtain ⟨x, hx, _, rfl⟩ := lay_base own work tree W cur _ R h
    obtain ⟨a, W', hs, rfl, _⟩ := told_drop _ _ _ _ hx
    have hj' : (j == 0) = false := by simpa using hj
    have hlen : l.length = 2 := by simpa using congrArg List.length hl
    unfold dealWalk
    rw [ok_app, ok_tag, hj']
    refine ⟨oneL_ok p j _ a W' hs (by rw [hl]; simp) (by rw [hl]; simp), ?_⟩
    simp [ok, hlen]
  | nxt :: rest, cur, j, tree, W, l, R, hj, h, hl => by
    obtain ⟨x, t, R', hx, _, h', rfl⟩ := lay_stage own true work tree W cur nxt rest _ R h
    obtain ⟨a, W', hs, rfl, rfl⟩ := told_drop _ _ _ _ hx
    have hj' : (j == 0) = false := by simpa using hj
    obtain ⟨c1, c2, c3⟩ := cuts l _ _ _ R' cur.k (by simp [Nat.add_comm]) hl
    unfold dealWalk
    dsimp only
    rw [ok_app, ok_tag, ok_app, hj', c1, c2, if_neg (by simp)]
    refine ⟨⟨?_, oneL_ok p j _ a W' hs (by simp) (by simp)⟩,
      walk_later p own work rest nxt (j + 1) (tree + 1) (wMid nxt) _ R' (by omega) ?_ c3⟩
    · simp [ok, fold_none]
    · have e : ownN p + (j + 1 - 1) = ownN p + (j - 1) + 1 := by omega
      rw [e]
      exact h'

/-- **dealOk is a theorem.** -/
theorem dealOk_made (p : P12) (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds)
    (hlen : p.oracles.length = rds.length) : dealOk p = true := by
  obtain ⟨s, next, rest, R, hs, hR, rfl⟩ := rounds_top p.nums rds hr
  have hl : (laidB p).map (·.1) = R := by
    unfold laidB
    rw [hr, Option.getD_some, List.map_drop, List.map_fst_zip (by omega)]
    rfl
  obtain ⟨x, t, R', hx, hne, h', rfl⟩ := lay_stage _ _ _ _ _ _ _ _ _ R hR
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨c1, c2, c3⟩ := cuts (laidB p) _ _ _ R' s.k (by simp [Nat.add_comm]) hl
  unfold dealOk dealOn
  rw [hs]
  show ok (dealWalk p 0 0 s (next :: rest) (laidB p)) = true
  unfold dealWalk
  dsimp only
  rw [ok_app, ok_tag, ok_app, c1, c2]
  refine ⟨⟨by simp [ok, fold_none], ?_⟩,
    walk_later p p.nums.ownMask p.nums.work rest next 1 (0 + 1) (wMid next) _ R' (by omega) ?_ c3⟩
  · simpa [ok] using hne
  · rw [ownN_eq p s next rest hs]
    cases ho : p.nums.ownMask
    · rw [ho] at h'
      simpa using h'
    · rw [ho] at h'
      simpa using h'

/-- What the frame's own test on the plan holds of the rounds, whatever the parts. -/
theorem rounds_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) :
    ∃ rds, H2U.roundsOfNums p.nums = some rds ∧ p.oracles.length = rds.length := by
  unfold proximityTestKind at hp
  split at hp
  · rename_i first rest rs os h1 h2 h3
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨rs, h2, hp.1.1.2⟩
  · cases hp

/-- **The block's test on the plan holds dealOk**, whatever the parts. -/
theorem dealOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : dealOk p = true := by
  obtain ⟨rds, hr, hl⟩ := rounds_of_planOk X p hp
  exact dealOk_made p rds hr hl

end H2K.Made

#print axioms H2K.Made.dealOk_made
#print axioms H2K.Made.dealOk_of_planOk
