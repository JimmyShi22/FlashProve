-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FoldTools.lean: four tools on a block's yes and on the fold over a
list of blocks. They name no seat.
  andThen_yes: a yes of two blocks joined is a yes of the first and, from its record, of the second.
  fold_one: where the fold over one block returns, the block's decision said yes.
  fold_next: the fold over one entry more of a list goes through the fold over the entries in front.
  fold_back: where the fold over the first k + 1 entries returns, the fold over the first k does.
USERS, among them: ListsAtDraw.lean, ListsEnds.lean, OwnAt.lean; OpenWalk.lean imports this file and calls none of its four tools (all four files in Johnson/IMR/).
No soundness.
-/
import Johnson.Goal.Meaning.RecWalk
import Johnson.Desc.StatementGrows
import Johnson.Desc.ProofFile.LotCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

theorem andThen_yes {T C : Type} {n : String} {p q : Block T C} {s t : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (Block.andThen n p q).decide s rs gs = .ok t) :
    ∃ u, p.decide s (rs.take p.rounds.length) (gs.take p.openings) = .ok u ∧
      q.decide u (rs.drop p.rounds.length) (gs.drop p.openings) = .ok t := Keeps.ebind_ok h


theorem fold_one {ft : Nat} {b : Block S Cl} {s : S} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft [b] s rs cols = .ok r) : ∃ rs' gs', b.decide s rs' gs' = .ok r.1 := by
  simp only [foldBlocks] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i s' k hs
      cases h
      exact ChainEnd.step_decide ft b s s' _ cols k hs


theorem fold_next {ft k : Nat} {bs : List (Block S Cl)} {b : Block S Cl} (hb : bs[k]? = some b)
    {s t t' : S} {rs r r' : List Fmt.RoundView} {cols c c' : List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (bs.take k) s rs cols = .ok (t, r, c))
    (h' : foldBlocks ft (bs.take (k + 1)) s rs cols = .ok (t', r', c')) :
    ∃ rs' gs', b.decide t rs' gs' = .ok t' := by
  rw [List.take_add_one, hb] at h'
  obtain ⟨u, r₁, c₁, g0, g1⟩ := Keeps.foldBlocks_split ft [b] _ _ _ _ _ h'
  rw [h] at g0
  cases g0
  exact fold_one g1


theorem fold_back {ft k : Nat} {bs : List (Block S Cl)} {s t' : S} {rs r' : List Fmt.RoundView}
    {cols c' : List VerifiableInference.Desc.OpenedColumn}
    (h' : foldBlocks ft (bs.take (k + 1)) s rs cols = .ok (t', r', c')) :
    ∃ t r c, foldBlocks ft (bs.take k) s rs cols = .ok (t, r, c) := by
  rw [List.take_add_one] at h'
  obtain ⟨u, r₁, c₁, g0, -⟩ := Keeps.foldBlocks_split ft _ _ _ _ _ _ h'
  exact ⟨u, r₁, c₁, g0⟩


end Meaning.K2
