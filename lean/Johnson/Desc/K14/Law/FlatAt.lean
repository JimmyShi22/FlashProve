-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/FlatAt.lean: IN THE SHARED CHAIN's FLAT LIST THE KIND's EIGHT BLOCKS STAND AS
THEY ARE, at the places 1 to 8. Theorems.

WHY. Chain.blocksInOrder (Johnson/Desc/Block.lean) lays each block of a chain's front or back in a wrap: its
test on the plan also asks that it states no run of claims. A law on a block b of blocks P is owed
at the block that the chain holds. Each of the eight states no such run: so the wrap is the identity
at it, and the chain holds b itself.

  bareOf          the wrap, by name. bareOf_self: at a block that states no run it changes nothing.
  own_bare        each of the eight states no run.
  flat_at         **the flat list**: the front block, wrapped; the eight, AS THEY ARE; the tests and
                  the closing block, wrapped.
  flat_get        **general in the place**: the k-th of the eight, from 0, is the flat list's member
                  number 1 + k.
What is not claimed. Anything of the tests' blocks or the closing block: they are arguments. Nothing
on soundness.

-/
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block)

/-- The wrap that Chain.blocksInOrder lays on a block of a chain's front or back. -/
def bareOf {S Cl : Type} : Block S Cl → Block S Cl :=
  fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

/-- At a block that states no run of claims the wrap changes nothing. -/
theorem bareOf_self {S Cl : Type} (b : Block S Cl) (h : b.hasNoClaimsAndNothingAfter = true) : bareOf b = b := by
  unfold bareOf
  simp only [h, Bool.and_true]

/-- Each of the eight states no run of claims, and none behind a batching. -/
theorem own_bare (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    b1.hasNoClaimsAndNothingAfter = true ∧ b2.hasNoClaimsAndNothingAfter = true ∧ b3.hasNoClaimsAndNothingAfter = true ∧ b4.hasNoClaimsAndNothingAfter = true ∧ b5.hasNoClaimsAndNothingAfter = true ∧
      b6.hasNoClaimsAndNothingAfter = true ∧ b7.hasNoClaimsAndNothingAfter = true ∧ b8.hasNoClaimsAndNothingAfter = true := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The shared chain's flat list.** -/
theorem flat_at (c : Model.Verify.Chains) (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (chainOf c P tests last).blocksInOrder = bareOf (frontBlock c) ::
      ([b1, b2, b3, b4, b5, b6, b7, b8] ++
        (tests ++ [last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests)]).map bareOf) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := own_bare P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have hflat : (chainOf c P tests last).blocksInOrder = bareOf (frontBlock c) ::
      ([b1, b2, b3, b4, b5, b6, b7, b8].map bareOf ++
        (tests ++ [last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests)]).map bareOf) := by
    simp [chainOf, VerifiableInference.Desc.Chain.blocksInOrder, blocksOr, hb, bareOf]
  rw [hflat]
  simp only [List.map_cons, List.map_nil, bareOf_self _ h1, bareOf_self _ h2, bareOf_self _ h3,
    bareOf_self _ h4, bareOf_self _ h5, bareOf_self _ h6, bareOf_self _ h7, bareOf_self _ h8]

/-- **General in the place.** -/
theorem flat_get (c : Model.Verify.Chains) (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (k : Nat) (b : Block St Unit)
    (hk : [b1, b2, b3, b4, b5, b6, b7, b8][k]? = some b) :
    (chainOf c P tests last).blocksInOrder[1 + k]? = some b := by
  rw [flat_at c P b1 b2 b3 b4 b5 b6 b7 b8 tests last hb, Nat.add_comm, List.getElem?_cons_succ,
    List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
  exact hk

end Desc.K14.Law
