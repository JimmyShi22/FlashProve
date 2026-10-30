-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkJoinC.lean: THE JOIN, THIRD PART: THE STORED COLUMNS. At the view's look-up
the columns that "LINK" is owed are linkAll's own lStoredCols, where what linkNext is handed as the
stored tables' columns is the stored strings' (yCol, LinkYesStm.lean). Statement and proof, general
in the shape but for one premise: the tables' depth.
The join: the proof of link_yes (LinkJoinF.lean), in six files: LinkJoinA to LinkJoinF.

  stored_cols    colsFor (lookV ...) (linkWant P.S r3) = some (lStoredCols P S X D), where r3 drew
                 D 3

By: colsFor_map (LinkJoinB.lean) · look_stored (LinkLook.lean) · readsAtLink's text.
Not shown here. Nothing on a decision, on soundness or on what any value discloses or does not
disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkJoinB

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Plain.One (colsFor)
open _root_.Desc.K15 (P15 readsAtLink)
open TypedOracleCompiler.Run.PQ (RD)
open _root_.Run.PQ (SgX storedKey)
open _root_.Iop (twoExternalStrings)

theorem stored_cols (P : P15) (S : Sz) (X : LIn S) (D : ℕ → Fmt.Drawn) (ds : List RD) (a : ℕ)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn)
    (r3 : Fmt.RoundView) (h3 : r3.drawn = D 3) (ha : P.S.table.tree.a = a) (hy : X.y = yCol a y) :
    colsFor (lookV ds a next y Ds) (linkWant P.S r3) = some (lStoredCols P S X D) := by
  subst ha
  rw [colsFor_map _ (fun w => yCol P.S.table.tree.a y (w.1 == Fmt.storedKey 1) w.2.1)]
  · unfold linkWant lStoredCols partWant readsAtLink
    rw [h3, hy]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_map]
    rfl
  · intro w hw
    unfold linkWant readsAtLink at hw
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hw
    rcases hw with hw | hw
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
      have hlt : z % 2 ^ P.S.table.tree.a < 2 ^ P.S.table.tree.a :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have := look_stored ds P.S.table.tree.a next y Ds false _ hlt
      show lookV ds P.S.table.tree.a next y Ds (storedKey false) _ = _
      rw [this]
      unfold yCol
      rw [dif_pos hlt]
      rfl
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
      have hlt : z % 2 ^ P.S.table.tree.a < 2 ^ P.S.table.tree.a :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have := look_stored ds P.S.table.tree.a next y Ds true _ hlt
      show lookV ds P.S.table.tree.a next y Ds (storedKey true) _ = _
      rw [this]
      unfold yCol
      rw [dif_pos hlt]
      rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.stored_cols
