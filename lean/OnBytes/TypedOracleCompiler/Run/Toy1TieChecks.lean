-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/Toy1TieChecks.lean.
Run/Toy1TieChecks.lean: the checks that the compiled verifier forms from a parser's openings are the
list checksOf of Run/Toy1TieTree.lean; and a small toy of our own meets that file's hypotheses.

Definitions, statements as theorems, and proofs. The verifier forms its checks by checksComp, which
goes over all 2^a numbers of a tree of depth a.

Sources. The leaf's label (Fmt.leafPlace) was written against the format page
(docs/format/FORMAT.md, R2.1); this file has not been held against the page as it ships, and may
differ from it.


1. What the file contains. sy1, colBytes3: the small toy's symbols and columns (the toy:
Run/ToyQ.lean, Run/ParseToy1.lean).

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   Generic (any round r, any ambient interface L).
     filterMap_lookup     Going through the numbers s, s + 1, .., s + n - 1 and looking each up in a
                          table with strictly increasing keys in that range gives the table's
                          entries in their order. Auxiliary: lookup_none_of_lt,
                          lookup_isSome_of_mem, lookup_none_of_not_mem.
     checksComp_of        The verifier's list of checks, if at every number it is known what
                          happens.
     checksComp_at        If Ob passes the parser's own test; every number below 2^a is a position's
                          number; A POSITION IS READ EXACTLY IF ITS NUMBER IS LISTED; and sym turns
                          each of Ob's columns into a symbol whose body is sy's: then checksComp at
                          the openings Ob.at is some (checksOf sy run rt Ob).
   At the small toy.
     toy_leaf             The toy's spelling PD.leaf of a symbol is (Fmt.leafPlace 0 3 5: tree 0,
                          three words, a salt of five words; 2^4 + x; the column of three words with
                          its empty fill). This is the hypothesis of forestV_checksOf and
                          forestV_reader.
     toy_checks           checksComp_at at these terms: the wire of round 1 with its work; the
                          embedding of a symbol of round 1; the openings by the toy's typing T.
     toy_forest           forestV_reader at the toy: on what the page's reader returns for the toy's
                          tree, forestV at famOf O PD 2 on checksOf = decide (the reader's root =
                          the sent root).

4. What is not claimed.
   THAT THE VERIFIER'S RUN AT THE TOY REACHES EXACTLY THE CALL OF checksComp THAT toy_checks NAMES,
   with isRead "the number is listed". The terms were written after a reading of the verifier's
   definition, and no theorem here unfolds Toy1.V.
   Nothing on the chain's queries, on the decision, or on refusals of a reader.

Terms: lean/GLOSSARY.md.

-/
import Run.Toy1TieChecks
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage160
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
import OnBytes.TypedOracleCompiler.Run.Toy1TieTree
import Run.ParseToy1
import Fmt.Rules1Laws

namespace TypedOracleCompiler.Run.TieTree
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch Octopus _root_.Run.WalkTie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.TieTree
export _root_.Run.TieTree (lookup_none_of_lt filterMap_lookup lookup_isSome_of_mem
    lookup_none_of_not_mem colBytes3)

/-! ### A list of numbers in a row, and a table with increasing keys -/

/-! ### The verifier's checks at a parser's openings -/

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {r : Round}

/-- the verifier's list of checks, if at every number of the list it is known what happens -/
theorem checksComp_of {β : Type} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig 256)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening 256 (r.Sym p)))
    (es : List (ℕ × β)) (mk : ℕ → β → Check 256 L) :
    ∀ js : List ℕ,
      (∀ j ∈ js, ∃ p,
        posAt j = some p ∧
        ((isRead p = true ∧
            ∃ op e,
              f p = some op ∧
              es.lookup j = some e ∧
              (⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩ : Check 256 L) = mk j e) ∨
          (isRead p = false ∧ es.lookup j = none))) →
      checksComp posAt depth emb rt isRead f js =
        some (js.filterMap fun j => (es.lookup j).map (mk j))
  | [], _ => rfl
  | j :: js, h => by
    have ih := checksComp_of posAt depth emb rt isRead f es mk js fun i hi => h i (by simp [hi])
    obtain ⟨p, hp, hc⟩ := h j (by simp)
    rw [checksComp, List.filterMap_cons]
    simp only [hp]
    rcases hc with ⟨hr, op, e, hf, hl, hm⟩ | ⟨hr, hl⟩
    · simp only [hr, if_true, hf, ih, hl, Option.map_some, hm]
    · simp only [hr, Bool.false_eq_true, if_false, ih, hl, Option.map_none]

/-- THE CHECKS THAT THE VERIFIER FORMS FROM A PARSER'S OPENINGS ARE checksOf. place: the number of a
position; every number below 2^a is a position's; a position is read exactly if its number is
listed; sym turns each of the opening's columns into a symbol whose body is sy's. -/
theorem checksComp_at (posAt : ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L)
    (rt : Dig 256) (isRead : r.Pos → Bool) (place : r.Pos → ℕ)
    (sym : (p : r.Pos) → List UInt64 → Option (r.Sym p))
    (sy : ℕ → List UInt64 → L.Bd) (run : ByteArray) (Ob : OpenB) (sb W : ℕ)
    (hok : Ob.ok sb W = true) (hpos : ∀ j, j < 2 ^ Ob.a → ∃ p, posAt j = some p ∧ place p = j)
    (hread : ∀ p, isRead p = decide (place p ∈ Ob.idx))
    (hsym : ∀ p col,
      col ∈ Ob.cols → ∃ y, sym p col = some y ∧ emb p y = sy (place p) col) :
    checksComp posAt Ob.a emb rt isRead
        (fun p => Ob.at (sym p) run (place p)) (List.range (2 ^ Ob.a)) =
      some (checksOf sy run rt Ob) := by
  obtain ⟨hc, hs, -, -, -⟩ := ok_spec Ob sb W hok
  obtain ⟨hp, hb, hcw⟩ := ok_list Ob sb W hok
  have hpl : Ob.paths.length = Ob.idx.length := length_fill _ _ _
  have hkeys : (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))).map Prod.fst = Ob.idx :=
    List.map_fst_zip (by simp only [List.length_zip]; omega)
  rw [checksComp_of posAt Ob.a emb rt isRead _ (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths)))
      (fun j e =>
        (⟨⟨sy j e.1, leafSalt run e.2.1⟩, j, e.2.2, rt, Ob.a⟩ : Check 256 L))]
  · rw [List.range_eq_range',
      filterMap_lookup _ (2 ^ Ob.a) 0 _ (by rw [hkeys]; exact hp) fun e he =>
        ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact hb _ (List.of_mem_zip he).1⟩]
    rfl
  · intro j hj
    obtain ⟨p, h1, h2⟩ := hpos j (List.mem_range.1 hj)
    refine ⟨p, h1, ?_⟩
    by_cases hm : j ∈ Ob.idx
    · left
      obtain ⟨v, hv, hmem⟩ := lookup_isSome_of_mem
        (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))) j (by rw [hkeys]; exact hm)
      obtain ⟨y, hy, he⟩ := hsym p v.1 (List.of_mem_zip (List.of_mem_zip hmem).2).1
      refine ⟨by rw [hread, h2]; simpa using hm, ⟨y, leafSalt run v.2.1, v.2.2⟩, v, ?_, hv, ?_⟩
      · unfold OpenB.at OpenB.atP
        rw [h2, hv]
        simp only [hy, Option.map_some]
      · simp only [he, h2]
    · right
      exact ⟨by rw [hread, h2]; simpa using hm,
        lookup_none_of_not_mem _ j (by rw [hkeys]; exact hm)⟩

end

/-! ### At the small toy: NOT SAID (sy1, toy_leaf, toy_checks, toy_forest: a closed toy's interface,
which the entry's clause does not hold) -/

end TypedOracleCompiler.Run.TieTree
