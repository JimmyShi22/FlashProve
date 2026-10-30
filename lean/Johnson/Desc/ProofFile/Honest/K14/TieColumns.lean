-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/TieColumns.lean: kind K14: THE TWO TEXTS OF A SENDING LAY THE SAME
COLUMNS, AS LISTS OF WORDS, AND SO THE SAME TABLES: this kind's columnOf and sentTables
(Honest/K14/Sendings.lean, on the program's elements, by the format's model encoder) against the
shared sending's col (Johnson/Prover/Send/Core.lean, in the field) and treeTables
(Honest/K1/Part.lean). Statements, each with its proof. General in the parameters P and in the rows,
where the two texts' rows agree, read, on the ranges that a column reads.

  symbols_tie     n rows' symbols: the format's words are the written form of the field's symbols
  column_tie      **columnOf P.codes P.sent L tree x = col P V tree x**
  trees_tie       the two texts read one list of trees
  sentTables_tie  **sentTables P.codes P.sent L = treeTables P V**: the same tables, as values

How it goes. One row's symbol by symE_written (Honest/K14/FreshSymbols.lean) and the library's
symG_congr (Johnson/Prover/Link/Base.lean). The two columns have one build: the tree's messages'
main rows' symbols, then their mask rows' symbols at the position modulo the mask code's length. The
shared text asks of which field a message's main rows are: where a message has a main row, RowsAgree
says: of the extension field.

What is assumed. RowsAgree P L V (Honest/K14/TieDefs.lean).
What is not claimed. That any rows agree: that is shown elsewhere. Nothing on roots, salts or paths.
Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.TieDefs
import Johnson.Desc.ProofFile.Honest.K14.FreshSymbols
import Johnson.Desc.ProofFile.Honest.K1.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E)
open OnBytes.Slice (GE rdE readE ofE codeOf)
open VerifiableInference.Desc (K1.Par)
open Johnson.Prover.Link (symG symG_congr words3)
open Johnson.Prover.Send (Rows shapeAt col mainSyms maskSyms)
open ProofFile.Honest.K1 (treeTables)

/-- **n rows' symbols**: the format's words are the written form of the field's symbols, at rows
that agree, read. -/
theorem symbols_tie (c : OnBytes.Code) (x n : Nat) (row tail : Nat → Nat → E)
    (m t : Nat → Nat → GE) (hm : ∀ r, r < n → ∀ j, j < c.ell → m r j = rdE.val (row r j))
    (ht : ∀ r, r < n → ∀ q, q < c.r → t r q = rdE.val (tail r q)) :
    symbolsOf c x n row tail =
      (List.range n).flatMap fun r => words3 (ofE (symG (codeOf c) x (m r) (t r))) := by
  unfold symbolsOf
  refine List.flatMap_congr fun r hr => ?_
  have hn : r < n := List.mem_range.1 hr
  show words3 (Fmt.M1.symE ⟨c.logN, c.ell, c.r⟩ x ((List.range c.ell).map fun j => (row r j).triple)
    ((List.range c.r).map fun q => (tail r q).triple)) = _
  rw [symE_written c x (row r) (tail r)]
  exact congrArg (fun y => words3 (ofE y))
    (symG_congr (codeOf c) x _ _ _ _ (fun j hj => (hm r hn j hj).symm)
      fun q hq => (ht r hn q hq).symm)

/-- **The two texts' columns are one list of words.** -/
theorem column_tie (P : K1.Par) (L : Nat → Laid) (V : Nat → Rows) (h : RowsAgree P L V)
    (tree x : Nat) : columnOf P.codes P.sent L tree x = col P V tree x := by
  unfold columnOf col
  dsimp only
  refine congrArg₂ (· ++ ·) (List.flatMap_congr fun k hm => ?_)
    (List.flatMap_congr fun k hm => ?_)
  · have hk : k < P.sent.size := List.mem_range.1 (List.mem_filter.1 hm).1
    refine (symbols_tie (P.codes.base.getD (shapeAt P k).code default) x (shapeAt P k).mainRows
      (L k).main (L k).mainTail (V k).mainE (V k).mainTlE (h.main k hk) (h.mainTail k hk)).trans ?_
    unfold mainSyms
    dsimp only
    refine List.flatMap_congr fun r hr => ?_
    have h0 : (shapeAt P k).mainRows ≠ 0 := by
      have := List.mem_range.1 hr
      omega
    have e3 : ((shapeAt P k).mainDeg == 3) = true := by
      rw [h.overE k hk h0]
      rfl
    rw [if_pos e3]
  · have hk : k < P.sent.size := List.mem_range.1 (List.mem_filter.1 hm).1
    exact symbols_tie (P.codes.mask.getD (shapeAt P k).maskCode default) _ (shapeAt P k).maskRows
      (L k).mask (L k).maskTail (V k).mask (V k).maskTl (h.mask k hk) (h.maskTail k hk)

/-- The two texts read one list of trees. -/
theorem trees_tie (P : K1.Par) :
    ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).shapes.toList = P.trees := by
  unfold VerifiableInference.Desc.K1.Par.trees
  cases VerifiableInference.Desc.Own.treesMade P.codes P.sent <;> rfl

/-- **The two texts' tables are the same, as values.** -/
theorem sentTables_tie (P : K1.Par) (L : Nat → Laid) (V : Nat → Rows) (h : RowsAgree P L V) :
    sentTables P.codes P.sent L = treeTables P V := by
  unfold sentTables treeTables
  rw [trees_tie]
  refine List.map_congr_left fun t _ => ?_
  simp only [column_tie P L V h]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.symbols_tie
#print axioms ProofFile.Honest.K14.column_tie
#print axioms ProofFile.Honest.K14.trees_tie
#print axioms ProofFile.Honest.K14.sentTables_tie
