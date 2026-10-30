-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/OwedPaid.lean: THE ROWS THAT ARE OWED A COUNT ARE PAID BY THE ONE
EQUATION's YES: behind a yes of the third of a link's three pieces no count waits. The mirror of
`owed_made` (OwedRides.lean). Theorems on the block's step, at the first chain's record.

Why. The table's promise at the boundary behind that block asks, in its test on the record's shape,
that no count of rows waits. So «the promise rides over the block's yes» wants this fact of the yes.

What is said.
  `door_owed`: the door's return owes nothing. `owed_paid`: **behind a yes of a block each of whose
    yeses is the one equation's, the record owes no count: `rowsOwed = none`; so `noneWaits`, and
    `K9.owedOf` gives nothing.**

Limits. One fact on one block. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OwedRides
import Johnson.Desc.First.Batch.Law.Hout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where owedOf door)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)

/-- The door's return owes nothing. -/
theorem door_owed {X : Type} (owed : K9.RowsOwed) (laid : Option ℕ) (L : LinkCtx) (F : Fork)
    (d : K9.St X) (o : K9.Out X) (h : door owed laid L F d = .ok o) : o.owed = none := by
  unfold door at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]

/-- **Behind the one equation's yes no count waits.** -/
theorem owed_paid {Cl : Type} (pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₃.step ft s rs cols = .ok (s', k)) :
    s'.rowsOwed = none ∧ s'.noneWaits = true ∧ owedOf s' = none := by
  obtain ⟨a0, out, _, hdoor, rfl⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ h)
  have e : (atS.set s { a0 with owed := out.owed, L := out.L, F := out.F, d := out.d }).rowsOwed =
      none := door_owed _ _ _ _ _ _ hdoor
  refine ⟨e, ?_, ?_⟩
  · unfold S.noneWaits
    rw [e]
  · unfold owedOf
    rw [e]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.door_owed
#print axioms VerifiableInference.Desc.LinkJoin.owed_paid
