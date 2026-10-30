-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/NumsOfRounds.lean: three of the seven numbers of a proximity test's place (the
trees of the test's group, the first free own number, the first tree's number) are read off the
place's declared rounds. General: no file, no size, no test on the plan. Statements and proofs; no
definition.

Why it holds. `H2U.roundsOfNums N` (Johnson/Desc/K12/TestEntries.lean) lays, at the rounds that open
trees, first the trees of the group and then the trees that the test sends, as they are told; the
i-th of these is told as the chain's own tree number `N.free + i`, with `N.firstTree + (N.free + i)`
as its number in the leaves' hashes. A test of two stages or more sends a tree. So both numbers
stand in the declared rounds.
Main names.
  `opens_of_rounds`: what the declared rounds open, in order, is `N.first ++ told N`.
  `nums_of_rounds`: two places with the same stages, the same own mask and the same declared rounds
    have the same `first`, `free` and `firstTree`.
What it is for. Where a place that a planner makes is to be held against a closed place, and the two
have the same declared rounds, no separate fact on these three numbers is wanted: at a key file's
three later places (Sizes/KeyClosedAtScope.lean) and just so at a proof file's.
Over `rounds_top`, `told`, `told_at` (MadeRounds.lean) and `layOpens_flat`
(Johnson/Desc/K12/Coin/LikeOf.lean). Kin: a fourth number, the rows, stands in the first declared
round (`rows_of_rounds`, in H2K12/CondAtLast.lean); `first_reads`
(Sizes/ClosedAtScope.lean) has the trees of the group alone, through the block's test on the plan at
both places.
What it is not. Nothing says that two places have the same declared rounds. The other four numbers
(rows, work, stages, own mask) are not concluded: two of them are premises. No soundness is claimed.
Nothing on hiding.

-/
import Johnson.Desc.K12.Law.MadeRounds
import Johnson.Desc.K12.Coin.LikeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes

/-- A list of one-member lists, joined, is the list. -/
theorem flatten_singles {α : Type} : ∀ l : List α, (l.map fun x => [x]).flatten = l
  | [] => rfl
  | a :: t => by
    rw [List.map_cons, List.flatten_cons, flatten_singles t]
    rfl

/-- What the declared rounds of a proximity test open, in order: the trees of the test's group, then
the trees that the test sends, as they are told. -/
theorem opens_of_rounds (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some rds) :
    rds.flatMap (·.opens) = N.first ++ H2K.Made.told N := by
  obtain ⟨s, next, rest, R, _, hR, rfl⟩ := H2K.Made.rounds_top N rds h
  have e := VerifiableInference.Desc.K12.Coin.layOpens_flat _ _ _ _ _ hR
  rw [List.flatMap_cons, e]
  show [] ++ _ = _
  rw [List.nil_append, List.flatten_cons, List.append_assoc, flatten_singles]
  congr 1
  cases N.ownMask with
  | false => rfl
  | true => exact List.take_append_drop 1 _

/-- As many trees are told as are sent. -/
theorem told_length (N : H2U.TestNums) : (H2K.Made.told N).length = N.sent.length := by
  unfold H2K.Made.told
  rw [List.length_map, List.length_zipIdx]

/-- **Three numbers of a place are read off its declared rounds**: two places with the same stages,
the same own mask and the same declared rounds have the same trees of the group, the same first free
own number and the same first tree's number. -/
theorem nums_of_rounds {N M : H2U.TestNums} {rds : List Fmt.DeclaredRound}
    (hN : H2U.roundsOfNums N = some rds) (hM : H2U.roundsOfNums M = some rds)
    (hs : N.stages = M.stages) (hm : N.ownMask = M.ownMask) :
    N.first = M.first ∧ N.free = M.free ∧ N.firstTree = M.firstTree := by
  have e : N.first ++ H2K.Made.told N = M.first ++ H2K.Made.told M :=
    (opens_of_rounds N rds hN).symm.trans (opens_of_rounds M rds hM)
  have hsent : N.sent = M.sent := by
    unfold H2U.TestNums.sent
    rw [hs, hm]
  have hl : (H2K.Made.told N).length = (H2K.Made.told M).length := by
    rw [told_length, told_length, hsent]
  obtain ⟨e1, e2⟩ := List.append_inj' e hl
  obtain ⟨s, next, rest, _, hst, _, _⟩ := H2K.Made.rounds_top N rds hN
  -- the test sends a tree
  obtain ⟨x, hx⟩ : ∃ x, N.sent[0]? = some x := by
    have hpos : 0 < N.sent.length := by
      unfold H2U.TestNums.sent
      rw [hst]
      simp
    exact ⟨_, List.getElem?_eq_getElem hpos⟩
  have a0 : (H2K.Made.told N)[0]? = some (N.own x.1 x.2 (N.free + 0)) := by
    rw [H2K.Made.told_at, hx]
    rfl
  have b0 : (H2K.Made.told M)[0]? = some (M.own x.1 x.2 (M.free + 0)) := by
    rw [H2K.Made.told_at, ← hsent, hx]
    rfl
  rw [e2] at a0
  have ee : N.own x.1 x.2 (N.free + 0) = M.own x.1 x.2 (M.free + 0) :=
    Option.some.inj (a0.symm.trans b0)
  have h2 : N.free + 0 = M.free + 0 := Fmt.TreeSource.own.inj (congrArg Prod.snd ee)
  have h1 : N.firstTree + (N.free + 0) = M.firstTree + (M.free + 0) :=
    congrArg (fun y => y.1.tree) ee
  exact ⟨e1, by omega, by omega⟩

end H2K.Sizes

#print axioms H2K.Sizes.opens_of_rounds
#print axioms H2K.Sizes.nums_of_rounds
