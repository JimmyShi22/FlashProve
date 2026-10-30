-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/RoundsOfSent.lean: IN WHICH ROUNDS A CHAIN's TREES GO, WITHOUT THEIR TAGS.
General laws on `sentAt` (Johnson/G/RoundsOfPlan.lean). Statements with proofs. Nothing is
evaluated.

`treesSent` holds, behind the `mapM` of `sentAt`, two tests on the sorted trees: at every round as
many trees as the plan's entry has roots; every tree's round below the number of rounds. Both read
of a tree its round alone. Every tree of a sending bears one round, the sending's entry less one
less the offset, whatever its tag; how many trees a sending has is the number of shapes that the
planner's `layTrees` lays. The sort's key is the round. So the sorted trees' rounds are a sorted
list of numbers, made of the sendings' entries and `layTrees` alone: what `sendTag` answers at a
label is not read.

  `roundsAt`, `roundsOfChain`: that list, at a sending and at a chain.
  `sentAt_rounds`, `flatten_rounds`: at a sending, and along a chain's sendings.
  `sortedW_rounds`: the rounds of `sortedW l e` (a name for the sorted trees:
    Johnson/Unfolds/TreesLaw.lean), by `List.map_mergeSort`.
IT TAKES A RETURN: that the `mapM` of `sentAt` returns at any chain is not shown here.
Limits. Nothing on the trees' tags, depths, widths or classes. The two tests themselves, as tests
on a list of numbers, are another file's to state. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.Core
import Johnson.Unfolds.TreesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending)
open Johnson.G.OfPlan
open Johnson.Unfolds (sortedW)

/-- The rounds of one sending's trees: one round, as often as the planner lays trees. -/
def roundsAt (codes : Codes) (off : Nat) (x : Sending) : List Nat :=
  match layTrees codes x.sent.toArray with
  | some L => List.replicate L.shapes.size (x.entry - 1 - off)
  | none => []

/-- The rounds of a chain's trees, with those that go in a round of their own, sorted. -/
def roundsOfChain (c : ChainSends) (off : Nat) (e : List Sent) : List Nat :=
  (c.sends.flatMap (roundsAt c.codes off) ++ e.map (·.round)).mergeSort fun a b => decide (a ≤ b)

/-- (R1) Where `sentAt` returns, its trees' rounds are `roundsAt`'s. -/
theorem sentAt_rounds {a : String} {codes : Codes} {off : Nat} {x : Sending} {s : List Sent}
    (h : sentAt a codes off x = .ok s) : s.map (·.round) = roundsAt codes off x := by
  unfold sentAt at h
  dsimp only at h
  split at h
  · obtain ⟨tag, _, h⟩ := ok_of_bind h
    split at h
    · rename_i L hlt
      obtain ⟨L', hL', h⟩ := ok_of_bind h
      obtain rfl := Except.ok.inj hL'
      have hs := Except.ok.inj h
      unfold roundsAt
      rw [hlt, ← hs, List.map_map]
      dsimp only
      rw [List.map_congr_left (g := fun _ => x.entry - 1 - off) (by rintro ⟨t, i⟩ _; rfl),
        List.map_const', List.length_zipIdx, Array.length_toList]
    · obtain ⟨_, hy, _⟩ := ok_of_bind h
      exact nomatch hy
  · obtain ⟨_, hy, _⟩ := ok_of_bind h
    exact nomatch hy

/-- The same along a chain's sendings. -/
theorem flatten_rounds (a : String) (codes : Codes) (off : Nat) :
    ∀ (xs : List Sending) (ls : List (List Sent)), xs.mapM (sentAt a codes off) = .ok ls →
      ls.flatten.map (·.round) = xs.flatMap (roundsAt codes off)
  | [], ls, h => by
    rw [List.mapM_nil] at h
    obtain rfl := Except.ok.inj h
    rfl
  | x :: xs, ls, h => by
    rw [List.mapM_cons] at h
    obtain ⟨s, hs, h⟩ := ok_of_bind h
    obtain ⟨ss, hss, h⟩ := ok_of_bind h
    obtain rfl := Except.ok.inj h
    rw [List.flatten_cons, List.map_append, List.flatMap_cons, sentAt_rounds hs,
      flatten_rounds a codes off xs ss hss]

/-- (R2) The sorted trees' rounds are the sorted rounds. -/
theorem sortedW_rounds {a : String} {c : ChainSends} {off : Nat} {l : List (List Sent)}
    (e : List Sent) (hl : c.sends.mapM (sentAt a c.codes off) = .ok l) :
    (sortedW l e).map (·.round) = roundsOfChain c off e := by
  unfold sortedW roundsOfChain
  rw [List.map_mergeSort (s := fun a b => decide (a ≤ b)) (fun _ _ _ _ => rfl), List.map_append,
    flatten_rounds a c.codes off c.sends l hl]

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.sentAt_rounds
#print axioms Johnson.AtFull.KeyBack.flatten_rounds
#print axioms Johnson.AtFull.KeyBack.sortedW_rounds
