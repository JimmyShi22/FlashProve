-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/TableShape.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: A TREE's TABLE HAS THE PLAN's LENGTH AND NUMBER OF WORDS. Statements and proofs
on treeTables (Honest/K1/Part.lean) as a term, and on the part's first move: free of any thread. No
definition.

  treeTables_shapes   the tables' (logLength, words), in order, are the plan's trees'
                (logN, mainWidth + maskWidth): at every plan and all rows: NO HYPOTHESIS
  treeTables_oracles   THEY ARE THE NUMBERS THAT K1's OWN BLOCK STATES FOR ITS FIRST ROUND's ORACLE
                MESSAGES (K1.oracles, Johnson/Desc/K1/Send.lean): the second clause of Sending.fits
                (Honest/Frame.lean), at that block's own list: NO HYPOTHESIS
  treeTables_length   so there are as many tables as the plan has trees
  treeTables_at   the table of tree number j: there is one, with that tree's two numbers
  col_length    a table's column has as many words as the table says (Table.col, Honest/Frame.lean:
                the frame's object; general in the table: if the frame gets its own law, this is a
                twin)
  treeTables_col_length   so a column of tree number j's table has mainWidth + maskWidth words
  first_say     where the job fits its place (sendFits), the part's first move says no item and just
                treeTables at the job's rows
  first_say_shapes   so what it says has the plan's trees' numbers

Limits. Of the first text's tables alone: the same of the second text treeTablesOf's is one
rewriting by treeTablesOf_eq (Honest/K1/TableArrLaw.lean): not stated here. The NUMBERS alone: of
what a word holds nothing is said here (that no default is read in a column under K1's own test on
the plan: length_col_tree, Honest/K1/TableWordLaw.lean). P.trees is empty where the trees cannot be
laid (K1.Par.trees, Johnson/Desc/K1/Send.lean): then there is no table. That a JOINED block's oracle
messages at a place are K1's own block's is not said here. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows)

variable {V W X : Type}

/-- **The tables' two numbers are the plan's trees'.** -/
theorem treeTables_shapes (P : K1.Par) (Vr : ℕ → Rows) :
    (treeTables P Vr).map (fun T => (T.logLength, T.words)) =
      P.trees.map fun t => (t.logN, t.mainWidth + t.maskWidth) := by
  unfold treeTables
  rw [List.map_map]
  have e : ((fun T : Table => (T.logLength, T.words)) ∘ fun x : TreeShape × ℕ =>
      ({ logLength := x.1.logN, words := x.1.mainWidth + x.1.maskWidth
         sym := fun pos i => toF ((Johnson.Prover.Send.col P Vr x.2 pos).getD i.val 0) } : Table)) =
      (fun t : TreeShape => (t.logN, t.mainWidth + t.maskWidth)) ∘ Prod.fst := rfl
  rw [e, ← List.map_map, List.zipIdx_map_fst]

/-- **They are the numbers that K1's own block states for its first round's oracle messages.** -/
theorem treeTables_oracles (P : K1.Par) (Vr : ℕ → Rows) :
    (treeTables P Vr).map (fun T => (T.logLength, T.words)) =
      ((K1.oracles P).headD []).map fun o => (o.logLength, o.words) := by
  rw [treeTables_shapes]
  unfold K1.oracles
  simp only [List.headD_cons, List.map_map]
  have e : P.trees.zipIdx.map Prod.fst = P.trees := by rw [List.zipIdx_map_fst]
  conv_lhs => rw [← e]
  rw [List.map_map]
  rfl

theorem treeTables_length (P : K1.Par) (Vr : ℕ → Rows) :
    (treeTables P Vr).length = P.trees.length := by
  have h := congrArg List.length (treeTables_shapes P Vr)
  simpa using h

/-- The table of tree number j. -/
theorem treeTables_at (P : K1.Par) (Vr : ℕ → Rows) (j : ℕ) (t : TreeShape)
    (h : P.trees[j]? = some t) :
    ∃ T, (treeTables P Vr)[j]? = some T ∧ T.logLength = t.logN ∧
      T.words = t.mainWidth + t.maskWidth := by
  have e := congrArg (·[j]?) (treeTables_shapes P Vr)
  simp only [List.getElem?_map, h, Option.map_some] at e
  cases hT : (treeTables P Vr)[j]? with
  | none => rw [hT] at e; cases e
  | some T =>
    rw [hT] at e
    have q := Option.some.inj e
    exact ⟨T, rfl, congrArg Prod.fst q, congrArg Prod.snd q⟩

theorem col_length (T : Table) (x : ℕ) : (T.col x).length = T.words := by
  unfold Table.col
  exact List.length_ofFn

theorem treeTables_col_length (P : K1.Par) (Vr : ℕ → Rows) (j : ℕ) (t : TreeShape)
    (h : P.trees[j]? = some t) (T : Table) (hT : (treeTables P Vr)[j]? = some T) (x : ℕ) :
    (T.col x).length = t.mainWidth + t.maskWidth := by
  obtain ⟨T', h1, _, h3⟩ := treeTables_at P Vr j t h
  rw [hT] at h1
  rw [Option.some.inj h1, col_length, h3]

/-- **The part's first move**, where the job fits its place: no item, and treeTables at the rows. -/
theorem first_say (J : SendJob W X) (hf : sendFits J.P J.ride = true) :
    ∃ m₁ m₂, (sendPart (V := V) J).moves = [m₁, m₂] ∧
      ∀ c s t, m₁.say c s t = .ok ⟨[], treeTables J.P (J.rows c.1 s t 0)⟩ := by
  refine ⟨_, _, rfl, fun c s t => ?_⟩
  simp [hf]

/-- So what it says has the plan's trees' numbers. -/
theorem first_say_shapes (J : SendJob W X) (hf : sendFits J.P J.ride = true) :
    ∃ m₁ m₂, (sendPart (V := V) J).moves = [m₁, m₂] ∧
      ∀ c s t, ∃ S, m₁.say c s t = .ok S ∧ S.vals = [] ∧
        S.tables.map (fun T => (T.logLength, T.words)) =
          J.P.trees.map fun t => (t.logN, t.mainWidth + t.maskWidth) := by
  obtain ⟨m₁, m₂, h, hs⟩ := first_say (V := V) J hf
  exact ⟨m₁, m₂, h, fun c s t => ⟨_, hs c s t, rfl, treeTables_shapes _ _⟩⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.treeTables_shapes
#print axioms ProofFile.Honest.K1.treeTables_oracles
#print axioms ProofFile.Honest.K1.treeTables_length
#print axioms ProofFile.Honest.K1.treeTables_at
#print axioms ProofFile.Honest.K1.col_length
#print axioms ProofFile.Honest.K1.treeTables_col_length
#print axioms ProofFile.Honest.K1.first_say
#print axioms ProofFile.Honest.K1.first_say_shapes
