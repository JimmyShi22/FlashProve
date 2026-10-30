-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/FirstOpensTaken.lean: WHAT THE FIRST SWITCH's CUT OPENS IS THE PLACE's OWN LIST
`nums.first`, then the first fold's own mask's tree if the fold sends one: by the make of the place's
declared rounds, from the block's own test on the plan (`open_top`, `Dealt.cons`,
Johnson/Desc/K12/OpenLaws.lean).

Why. `firstOpens_of` (Johnson/Desc/K12/Coin/FirstOpensOf.lean) takes as a premise that every opening of the
first switch's cut is of a tree that is taken over. Here that premise is carried to the place's list.
  `opensOf_lists`   opensOf π a.k is the head of `listsOf π.nums`
  `opensOf_first`   where the first fold sends no mask of its own: opensOf π a.k = π.nums.first
  `taken_of_first`  **so `taken` follows from: every member of π.nums.first is taken over**
Limits. What π.nums.first is at a place is the plan's road's. Nothing on soundness.

-/
import Johnson.Desc.K12.OpenLaws
import Johnson.Desc.K12.Law.FirstOk
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The first switch's cut opens the head of the lists that the rounds' maker lays in. -/
theorem opensOf_lists (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hs : π.nums.stages = a :: next :: rest) :
    H2K.First.opensOf π a.k =
      π.nums.first ++ (if π.nums.ownMask then
        ((π.nums.sent.zipIdx.map fun t => π.nums.own t.1.1 t.1.2 (π.nums.free + t.2)).take 1)
        else []) := by
  obtain ⟨first, rest', ds, hs', hr, -, hd⟩ := open_top (Cl := Unit) guardedProximityTestParts π hp
  rw [hs] at hs'
  obtain ⟨rfl, rfl⟩ := List.cons.inj hs'
  have e := Dealt.cons (x := π.nums.first ++ (if π.nums.ownMask then
        ((π.nums.sent.zipIdx.map fun t => π.nums.own t.1.1 t.1.2 (π.nums.free + t.2)).take 1)
        else [])) hd
  unfold H2K.First.opensOf
  rw [hr, Option.getD_some, List.flatMap_def, List.map_take, List.map_drop]
  have e' : List.map (fun x => x.1.opens) (List.drop 1 (ds.zip π.oracles)) = _ := e
  rw [e', List.drop_left' (by rw [List.length_replicate])]
  simp

/-- Where the first fold sends no mask of its own. -/
theorem opensOf_first (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hs : π.nums.stages = a :: next :: rest)
    (ho : π.nums.ownMask = false) : H2K.First.opensOf π a.k = π.nums.first := by
  rw [opensOf_lists π hp a next rest hs, ho]
  simp

/-- **The premise `taken`, from the place's list.** -/
theorem taken_of_first (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (ho : π.nums.ownMask = false) (h2 : 2 ≤ π.nums.stages.length)
    (hf : ∀ o ∈ π.nums.first, ∃ c n, o.2 = .taken c n) :
    ∀ a rest, π.nums.stages = a :: rest →
      ∀ o ∈ H2K.First.opensOf π a.k, ∃ c n, o.2 = .taken c n := by
  intro a rest hs o hO
  cases rest with
  | nil =>
    rw [hs] at h2
    have h2' : 2 ≤ 1 := h2
    omega
  | cons next rest =>
    rw [opensOf_first π hp a next rest hs ho] at hO
    exact hf o hO

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.opensOf_lists
#print axioms VerifiableInference.Desc.K12.Coin.opensOf_first
#print axioms VerifiableInference.Desc.K12.Coin.taken_of_first
