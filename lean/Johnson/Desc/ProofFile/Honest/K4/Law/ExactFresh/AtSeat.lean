-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtSeat.lean: ON LISTS AND TESTS ALONE: what
Law/ExactFresh/AtSide.lean and AtSideGood.lean show at the side that `k4Side` makes, once more under
lighter premises: at every sub-protocol b whose rounds' entries are those of the verifier's table of
K4's rounds and that passes the description's own test on its shape (`Block.shaped`,
Johnson/Desc/Block.lean); that test from the description's test on a chain's list (`blocksOk`); and
both premises at the sub-protocol that K4's lot lays (`k4Block`,
Johnson/Desc/ProofFile/Lot/K4.lean). Statements and proofs.

Limits. No statement here is on a law of coins. `k4Side` asks three things; of these the statements
on `exact` read the one on the entries alone: here that one stands by itself (he). THE LOT's OWN
SUB-PROTOCOL IS NOT YET A DESCRIPTION's MEMBER: what a description's makers do to it behind the lot
is not read here: where they keep its rounds and its lists of oracle messages, `k4Block_entries` and
`k4Block_shaped` carry over; that they do is not shown. No property is claimed.

  `block_roots`, `block_count`, `block_stated_shaped`   at a sub-protocol with the table's entries.
  `seated_mem`, `shaped_of_blocksOk`   the side's sub-protocol is of the list; the test on its shape
      from the test on the list.
  `shaped_plain`, `k4Block_entries`, `k4Block_shaped`   **at the sub-protocol that K4's lot lays.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtSideGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Place blocksOk)

section
variable {S Cl : Type} (Q : K4Pub) (b : Block S Cl)
  (he : b.rounds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
include he

/-- No round states a root. -/
theorem block_roots : ∀ r ∈ b.rounds, r.entry.roots = 0 := fun _ hr =>
  entries_roots Q _ (he ▸ List.mem_map_of_mem hr)

/-- It has as many rounds as K4's row has moves. -/
theorem block_count : b.rounds.length = ((k4RowIn Q).map (·.moves.length)).sum := by
  have e := congrArg List.length he
  unfold OnBytes.Desc.First.K4.entries at e
  rw [List.length_map, List.length_map] at e
  rw [e, table_length, rowIn_moves]

/-- **The test on the rounds accepts**, under the description's own test on the shape. -/
theorem block_stated_shaped (hs : b.shaped = true) :
    k4StatedAllB Q (b.rounds.zip b.oracles) = true := by
  obtain ⟨ho, hno⟩ := oracles_of_shaped b hs (block_roots Q b he)
  refine k4_stated_entries Q _ ?_ fun r hr => hno r.2 (List.of_mem_zip hr).2
  have e : (b.rounds.zip b.oracles).map (·.1) = b.rounds := map_fst_zip_same _ _ ho.symm
  have e2 : (b.rounds.zip b.oracles).map (·.1.entry) =
      ((b.rounds.zip b.oracles).map (·.1)).map (·.entry) := by
    rw [List.map_map]
    rfl
  rw [e2, e]
  exact he

end

/-- The sub-protocol of the side that `Side.seated` makes is of the list. -/
theorem seated_mem {S Cl V W X Pb : Type} {bs : List (Block S Cl)} {a : Place}
    {row : List (Part V W X × Sim Pb)} {fs : List (Fall S)} {σ : Side S Cl V W X Pb}
    (h : Side.seated bs a row fs = some σ) : σ.block ∈ bs := by
  unfold Side.seated at h
  cases hf : bs.find? (fun b => b.place == a) with
  | none =>
    rw [hf] at h
    cases h
  | some b =>
    rw [hf] at h
    obtain rfl := Option.some.inj h
    exact List.mem_of_find?_eq_some hf

/-- The description's test on a chain's list gives the test on each member's shape. -/
theorem shaped_of_blocksOk {S Cl : Type} {bs : List (Block S Cl)} (h : blocksOk bs = true)
    {b : Block S Cl} (hb : b ∈ bs) : b.shaped = true := by
  have e := List.all_eq_true.1 h b hb
  rw [Bool.and_eq_true] at e
  exact e.2

/-- A sub-protocol whose rounds are made of entries that state no root, with an empty list of oracle
messages at each, passes the test on its shape. -/
theorem shaped_plain {S Cl : Type} (es : List Fmt.Entry) (h : ∀ e ∈ es, e.roots = 0)
    (b : Block S Cl) (hr : b.rounds = es.map fun e => { entry := e })
    (ho : b.oracles = es.map fun _ => []) : b.shaped = true := by
  unfold Block.shaped
  rw [hr, ho, List.length_map, List.length_map, beq_self_eq_true, Bool.true_and,
    List.all_eq_true, List.zip_map']
  intro p hp
  obtain ⟨e, hm, rfl⟩ := List.mem_map.1 hp
  show (([] : List VerifiableInference.Desc.Oracle).length == e.roots && _) = true
  rw [h e hm]
  rfl

/-- **The rounds of the sub-protocol that K4's lot lays have the table's entries.** -/
theorem k4Block_entries (x : Bool × OnBytes.Desc.First.K4.Par) :
    (ProofFile.k4Block x).rounds.map (·.entry) = OnBytes.Desc.First.K4.entries x.2.P x.2.hp x.2.g := by
  show ((OnBytes.Desc.First.K4.entries x.2.P x.2.hp x.2.g).map fun e =>
    ({ entry := e } : Fmt.DeclaredRound)).map (·.entry) = _
  rw [List.map_map]
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_id _)

/-- **It passes the description's test on its shape.** -/
theorem k4Block_shaped (x : Bool × OnBytes.Desc.First.K4.Par) : (ProofFile.k4Block x).shaped = true :=
  shaped_plain (OnBytes.Desc.First.K4.entries x.2.P x.2.hp x.2.g)
    (fun e he => by
      unfold OnBytes.Desc.First.K4.entries at he
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
      rfl) _ rfl rfl

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.block_roots
#print axioms ProofFile.Honest.K4.ExactFresh.block_count
#print axioms ProofFile.Honest.K4.ExactFresh.block_stated_shaped
#print axioms ProofFile.Honest.K4.ExactFresh.seated_mem
#print axioms ProofFile.Honest.K4.ExactFresh.shaped_of_blocksOk
#print axioms ProofFile.Honest.K4.ExactFresh.shaped_plain
#print axioms ProofFile.Honest.K4.ExactFresh.k4Block_entries
#print axioms ProofFile.Honest.K4.ExactFresh.k4Block_shaped
