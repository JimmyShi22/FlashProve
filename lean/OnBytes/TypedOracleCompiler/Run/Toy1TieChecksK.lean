-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/Toy1TieChecksK.lean: THE CHECKS THAT THE VERIFIER FORMS FROM A PARSER's OPENING ARE
checksOf, FOR ONE TREE AMONG SEVERAL OF A ROUND.
After Run/Toy1TieChecks.lean's checksComp_at, whose hypotheses speak of ALL positions
of the round (hread: "read" means "listed"; the opening at p is the record's at place p): true where
a round has one tree. Here they are asked ALONG posAt ALONE: of the position at each number below 2
^ a: the other trees' positions are not spoken of.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.Toy1TieChecks

namespace TypedOracleCompiler.Run.TieTree
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch Octopus _root_.Run.WalkTie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.TieTree

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {r : Round}

theorem checksComp_atK (posAt : ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : Dig 256) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening 256 (r.Sym p)))
    (sym : (p : r.Pos) → List UInt64 → Option (r.Sym p))
    (sy : ℕ → List UInt64 → L.Bd) (run : ByteArray) (Ob : OpenB) (sb W : ℕ)
    (hok : Ob.ok sb W = true)
    (hpos : ∀ j, j < 2 ^ Ob.a → ∃ p, posAt j = some p ∧ isRead p = decide (j ∈ Ob.idx) ∧
      f p = Ob.at (sym p) run j ∧ ∀ col ∈ Ob.cols, ∃ y, sym p col = some y ∧ emb p y = sy j col) :
    checksComp posAt Ob.a emb rt isRead f (List.range (2 ^ Ob.a)) =
      some (checksOf sy run rt Ob) := by
  obtain ⟨hc, hs, -, -, -⟩ := ok_spec Ob sb W hok
  obtain ⟨hp, hb, hcw⟩ := ok_list Ob sb W hok
  have hpl : Ob.paths.length = Ob.idx.length := length_fill _ _ _
  have hkeys : (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))).map Prod.fst = Ob.idx :=
    List.map_fst_zip (by simp only [List.length_zip]; omega)
  rw [checksComp_of posAt Ob.a emb rt isRead f (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths)))
      (fun j e =>
        (⟨⟨sy j e.1, leafSalt run e.2.1⟩, j, e.2.2, rt, Ob.a⟩ : Check 256 L))]
  · rw [List.range_eq_range',
      filterMap_lookup _ (2 ^ Ob.a) 0 _ (by rw [hkeys]; exact hp) fun e he =>
        ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact hb _ (List.of_mem_zip he).1⟩]
    rfl
  · intro j hj
    obtain ⟨p, h1, hrd, hf, hsym⟩ := hpos j (List.mem_range.1 hj)
    refine ⟨p, h1, ?_⟩
    by_cases hm : j ∈ Ob.idx
    · left
      obtain ⟨v, hv, hmem⟩ := lookup_isSome_of_mem
        (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))) j (by rw [hkeys]; exact hm)
      obtain ⟨y, hy, he⟩ := hsym v.1 (List.of_mem_zip (List.of_mem_zip hmem).2).1
      refine ⟨by rw [hrd]; simpa using hm, ⟨y, leafSalt run v.2.1, v.2.2⟩, v, ?_, hv, ?_⟩
      · rw [hf]
        unfold OpenB.at OpenB.atP
        rw [hv]
        simp only [hy, Option.map_some]
      · simp only [he]
    · right
      exact ⟨by rw [hrd]; simpa using hm,
        lookup_none_of_not_mem _ j (by rw [hkeys]; exact hm)⟩

end

end TypedOracleCompiler.Run.TieTree
