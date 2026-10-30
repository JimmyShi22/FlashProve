-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/TreesValue.lean: TWO LAWS ON `treesSent` (Johnson/G/RoundsOfPlan.lean), SO THAT
ITS RETURN AND ITS VALUE CAN BE HAD WITHOUT A WALK OVER A CHAIN's ROUNDS. Its own check lays an
array of one cell a round and reads it by index at every round: at the proof file's first chain,
48,293 rounds, that is the square of the length in Lean's kernel.
  `treesSent_value`: where it returns, its value is the sendings' trees (`sentAt` at each sending),
    with the extra ones, sorted by round and numbered: the plan is read for one number alone: how
    many of its entries are no rounds.
  `trees_of_decl`: where the proof file's declared rounds are made (`declPOf m = .ok D`), it has
    returned at all three chains, at the very arguments at which `firstsOfPlan` and `placesLater`
    call it. `ok_of_bind`: a tool.
Limits. Nothing says that `declPOf` returns; and `declPOf` calls `treesSent` (through `fileOf`) at
the three chains, so whoever shows its return at given values pays that walk: the cost is moved
into the premise, not taken away. Nothing on soundness or on hiding.
-/
import Johnson.Desc.K12.Law.FirstTreeOfMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc
open OnBytes OnBytes.Params Johnson.G.OfPlan

/-- A bind of two steps that returns: both return. -/
theorem ok_of_bind {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **Where `treesSent` returns, at which value.** -/
theorem treesSent_value {at_ : String} {c : Johnson.G.ChainSends} {P : Fmt.Plan}
    {extra : List Sent} {ts : List (Sent × Nat)} (h : treesSent at_ c P extra = .ok ts) :
    ∃ l, c.sends.mapM (sentAt at_ c.codes (P.entries.length - P.rounds.length)) = .ok l ∧
      ts = ((l.flatten ++ extra).mergeSort fun a b => decide (a.round ≤ b.round)).zipIdx := by
  unfold treesSent at h
  dsimp only at h
  cases hl : c.sends.mapM (sentAt at_ c.codes (P.entries.length - P.rounds.length)) with
  | error e => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      swap
      · cases h
      · cases h
        exact ⟨l, rfl, rfl⟩

/-- **Where the proof file's declared rounds are made, `treesSent` has returned at its three
chains.** -/
theorem trees_of_decl {m : Made} {D : Decl3} (h : declPOf m = .ok D) :
    ∃ t0 t1 t2,
      treesSent "proof file, first chain" m.proof.1 m.p.chains.proof.first.given.plan [] =
        .ok t0 ∧
      treesSent "proof file, shared chain" m.proof.2.1 m.p.chains.proof.shared.given.plan
        (ownMasks m.proof.2.1.codes m.p.chains.made.sized.proof.batch.shape
          m.p.chains.proof.shared.given.plan.rounds) = .ok t1 ∧
      treesSent "proof file, second chain" m.proof.2.2 m.p.chains.proof.second.given.plan [] =
        .ok t2 := by
  unfold declPOf fileOf at h
  dsimp only at h
  obtain ⟨t0, h0, h⟩ := ok_of_bind h
  obtain ⟨t1, h1, h⟩ := ok_of_bind h
  obtain ⟨t2, h2, h⟩ := ok_of_bind h
  exact ⟨t0, t1, t2, h0, h1, h2⟩

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.ok_of_bind
#print axioms Johnson.AtFull.Desc.treesSent_value
#print axioms Johnson.AtFull.Desc.trees_of_decl
