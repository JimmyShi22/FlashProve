-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontStored.lean: the stored columns that the written view hands to the link's
front sub-protocols (lStoredCols, Johnson/Prover/Link/LinkAll.lean) are the columns of the two
stored strings: under the key of stored table 0 or 1, at a position in range, the column is what
storedOf (OnBytes/Slice/Unfold.lean) reads of the strings there. This is the premise hop of front_at
(Johnson/Prover/Link/FrontAt.lean). Statements and proofs.

Main names (namespace Johnson.Prover.Link).
  storedOf_lStoredCols   the statement, general: the prover's columns are yCol of the strings, and
    the stored tables' trees have the strings' depth.
  stored_full   at the full size, at the input made of an instance, the strings and the two
    polynomials: the premise hop to the letter.

Limits. Only the list lStoredCols is spoken of: no column of a tree that is sent. Nothing on
soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.LinkYesStm
import OnBytes.Slice.FullRecBlkFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open _root_.Desc.K15 (P15 frP readsAtLink)
open OnBytes.Flat (RecFull)
open _root_.Run.PQ (SgX)
open _root_.Iop (twoExternalStrings)

/-- **Each stored column of the written view is the strings' column at its position.** -/
theorem storedOf_lStoredCols (P : P15) (S : Sz) (X : LIn S) (D : ℕ → Fmt.Drawn) (a : ℕ)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (ha : P.S.table.tree.a = a) (hy : X.y = yCol a y) :
    ∀ o ∈ lStoredCols P S X D,
      (o.1 = Fmt.storedKey 0 → storedOf a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf a y 1 o.2.1 = some o.2.2) := by
  subst ha
  intro o ho
  unfold lStoredCols readsAtLink at ho
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at ho
  rcases ho with ho | ho
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
    have hlt : z % 2 ^ P.S.table.tree.a < 2 ^ P.S.table.tree.a :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    refine ⟨fun _ => ?_,
      fun h => absurd (show Fmt.storedKey 0 = Fmt.storedKey 1 from h) (by decide)⟩
    show storedOf P.S.table.tree.a y 0 (z % 2 ^ P.S.table.tree.a) = some (X.y false _)
    rw [hy]
    unfold storedOf yCol
    rw [dif_pos hlt, dif_pos hlt]
    rfl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
    have hlt : z % 2 ^ P.S.table.tree.a < 2 ^ P.S.table.tree.a :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    refine ⟨fun h => absurd (show Fmt.storedKey 1 = Fmt.storedKey 0 from h) (by decide),
      fun _ => ?_⟩
    show storedOf P.S.table.tree.a y 1 (z % 2 ^ P.S.table.tree.a) = some (X.y true _)
    rw [hy]
    unfold storedOf yCol
    rw [dif_pos hlt, dif_pos hlt]
    rfl

/-- **At the full size**: the premise hop of front_at. -/
theorem stored_full (rr : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (M₀ M₁ : (Fin frS.P.v → Bool) → frS.Co → GE) (D : ℕ → Fmt.Drawn) :
    ∀ o ∈ lStoredCols frP frS (linOf rr y M₀ M₁) D,
      (o.1 = Fmt.storedKey 0 → storedOf frS.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf frS.P.T.a y 1 o.2.1 = some o.2.2) :=
  storedOf_lStoredCols frP frS _ D frS.P.T.a y fr_linkSizesR.logN rfl

end Johnson.Prover.Link
