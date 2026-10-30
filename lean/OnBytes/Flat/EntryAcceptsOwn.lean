-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/EntryAcceptsOwn.lean: the written statement of OnBytes/Flat/EntryAccepts.lean (two
stored tables of zeros, each with the record `recW`) in the language of the entry's own soundness
theorems, clause by clause.

Why. `entrySmall_sound` (OnBytes/Flat/EntrySound.lean) speaks of the language "the first table gives
no index with its record, or the copy has a collision at its record's seed, or both give the same
index", at the configuration `DecR.configurationOfStoredTable A R` of any claims A and rest R.
OnBytes/Flat/EntryAcceptsTrue.lean shows that the written statement is true by the last clause of
another language, that of the family's soundness, and leaves open which ways out of this one are
shut. Here each of the three clauses is settled.

Main theorems, for every A and R.
 `written_collA`   the second clause is false: the configuration's collision is the decoder's own,
                   by definition, and the table of zeros has none.
 `written_DA`      what the index decoder gives at the table of zeros with the record: the matrix
                   that A reads of the messages 0, if A counts it as in range; else nothing.
 `written_noneA`   so the first clause holds exactly if A does not count that matrix as in range.
 `written_ownA`    under "A counts it as in range": both ways out are shut and the last clause
                   holds at an index.

Not claimed. That any A counts the matrix of the messages 0 as in range: A is a letter. Where it
does not, the first table "gives no index", the statement lies in the language by that way out, and
the soundness theorem promises nothing of it. The two tables are equal and so are the two records.
All that the heads of OnBytes/Flat/EntryAccepts.lean and EntryAcceptsTrue.lean do not claim.


-/
import OnBytes.Flat.EntryAcceptsTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Flat
open Iop Prob Cb Cb.Ood Hiop _root_.Run _root_.Run.PQ Blocks OnBytes.Slice

variable {X : Type} (A : decW.Claims X) (R : decW.RelationsAndEncoding A)

/-- The second clause is false. -/
theorem written_collA : ¬ (DecR.configurationOfStoredTable A R).coll (tabW srS.P.T.a).2 recW.1 := not_coll_tabW _

open Classical in
/-- What the index decoder gives at the table of zeros with the record. -/
theorem written_DA : (DecR.configurationOfStoredTable A R).D (tabW srS.P.T.a).1 recW =
    if A.inRange (A.mat (decW.ix.view fun _ => 0)) then some (A.mat (decW.ix.view fun _ => 0))
    else none := by
  rw [DecR.conf_D, if_neg (not_coll_tabW _), dcd_tabW]
  rfl

/-- The first clause holds exactly if A does not count the matrix of the messages 0 as in range. -/
theorem written_noneA : (DecR.configurationOfStoredTable A R).D (tabW srS.P.T.a).1 recW = none ↔
    ¬ A.inRange (A.mat (decW.ix.view fun _ => 0)) := by
  classical
  rw [written_DA]
  by_cases h : A.inRange (A.mat (decW.ix.view fun _ => 0))
  · rw [if_pos h]
    exact ⟨fun e => absurd e (Option.some_ne_none _), fun n => absurd h n⟩
  · rw [if_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- **Where A counts that matrix as in range: both ways out are shut, and the last clause holds, at
an index.** -/
theorem written_ownA (h : A.inRange (A.mat (decW.ix.view fun _ => 0))) :
    (DecR.configurationOfStoredTable A R).D (tabW srS.P.T.a).1 recW ≠ none ∧
      ¬ (DecR.configurationOfStoredTable A R).coll (tabW srS.P.T.a).2 recW.1 ∧
      (DecR.configurationOfStoredTable A R).D (tabW srS.P.T.a).2 recW = (DecR.configurationOfStoredTable A R).D (tabW srS.P.T.a).1 recW ∧
      (DecR.configurationOfStoredTable A R).D (tabW srS.P.T.a).1 recW = some (A.mat (decW.ix.view fun _ => 0)) := by
  classical
  refine ⟨fun e => (written_noneA A R).1 e h, written_collA A R, rfl, ?_⟩
  rw [written_DA, if_pos h]

end OnBytes.Flat

#print axioms OnBytes.Flat.written_collA
#print axioms OnBytes.Flat.written_DA
#print axioms OnBytes.Flat.written_noneA
#print axioms OnBytes.Flat.written_ownA
