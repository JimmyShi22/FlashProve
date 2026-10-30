-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PosLater.lean: THE LAST CONJUNCT OF THE FIELD fuEq OF THE THREE SORTS'
TAKES
(PayLayers.lean, PayAttention.lean, PayHead.lean: "each place that a read names lies within its
table's vector's columns") OFF THE RUN's OWN YES: with it the premise okPos of `fuEq_full`
(FullEq.lean) is wanted no more. One definition and two theorems: calls of `eq_reads`
(Johnson/Desc/First/TailClaims/EquationsCover.lean: a yes of the list "K8.equations" says that every
place that a read names lies below the length that the structure holds for the vector).

  `okWidthB nU U cols`: ON THE PLAN ALONE: the lengths of the vectors U1 and U3 are at most the
columns
    of their arrays.
  `pos_later`: **equations front tl funs F = .ok (tl', F1, cls) · a structure ts with tl''s NM,
mats,
    ix.U · ts.nUF = tl'.nUF = nU · okWidthB nU ts.ix.U (colsU G) ⊢ ∀ x ∈ readsList ts funs, ∀ d <
    k, posOf ts x.1 x.2 d < colsU G (uOf ts x.1).**
  `pos_at_run`: the same at ts := tl'.
WHAT IT READS. No weight of a table, no sent value, no challenge: the run's yes, four planned
fields,
a look of the ledger G.
Limits. THE LIST OF TABLES IS ONE LETTER: that the state at which fuEq is asked finds the list that
the run was handed is the caller's. That ts has tl''s NM and mats, and that nU is the length that
tl' holds
(the run of self tests asks nU == ts.nUF of ITS structure), are premises. The test has run at no
data. No soundness
statement.

-/
import Johnson.Desc.First.TailClaims.EquationsCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (eq_reads tree_of_mem)

/-- On the plan alone: the two vectors' lengths are at most their arrays' columns. -/
def okWidthB (nU : Array ℕ) (U : Array (Option ℕ)) (cols : ℕ → ℕ) : Bool :=
  [0, 2].all fun un => decide (nU.getD un 0 ≤ cols ((U.getD un none).getD 0))

/-- **fuEq's LAST CONJUNCT, OFF THE RUN's OWN YES.** -/
theorem pos_later {front : ℕ} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) (ts : HTailF2)
    (hNM : ts.NM = tl'.NM) (hmats : ts.mats = tl'.mats)
    (nU : Array ℕ) (hn : tl'.nUF = nU) (G : Fork)
    (hw : okWidthB nU ts.ix.U (colsU G) = true) :
    ∀ x ∈ readsList ts funs, ∀ d, d < (ts.mats.getD x.1.mat {}).k →
      posOf ts x.1 x.2 d < colsU G (uOf ts x.1) := by
  have e1 : readsList ts funs = readsList tl' funs := by
    unfold readsList segsOf
    rw [hNM, hmats]
  have e2 : ∀ Fn sg d, posOf ts Fn sg d = posOf tl' Fn sg d := by
    intro Fn sg d
    unfold posOf HTailF2.tabAt
    rw [hNM, hmats]
  intro x hx d hd
  rw [e1] at hx
  rw [hmats] at hd
  obtain ⟨-, h1⟩ := eq_reads front tl tl' funs F F1 cls h x hx
  have h2 := h1 d hd
  rw [hn] at h2
  rw [e2]
  refine Nat.lt_of_lt_of_le h2 ?_
  have h3 : x.1.tree = 0 ∨ x.1.tree = 2 := tree_of_mem tl' funs x hx
  have h4 := List.all_eq_true.1 hw x.1.tree (by rcases h3 with e | e <;> simp [e])
  exact of_decide_eq_true h4

/-- The same at the structure that the run returns. -/
theorem pos_at_run {front : ℕ} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) (G : Fork)
    (hw : okWidthB tl'.nUF tl'.ix.U (colsU G) = true) :
    ∀ x ∈ readsList tl' funs, ∀ d, d < (tl'.mats.getD x.1.mat {}).k →
      posOf tl' x.1 x.2 d < colsU G (uOf tl' x.1) :=
  pos_later h tl' rfl rfl _ rfl G hw

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pos_later
#print axioms VerifiableInference.Desc.LinkJoin.pos_at_run
