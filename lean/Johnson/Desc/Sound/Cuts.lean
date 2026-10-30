-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/Cuts.lean: two stretches of a file's written rounds behind each other: what is
drawn, what the draws ask for, the test that no draw is shortened, a tree's shape and a tree's
column are made of those of the two stretches. Statements and proofs. No protocol occurs here.

It goes on from OnBytes/Tie/Pv/Lookup/Peel/FoPeelJoinT.lean (`Fo.Peel.joinR`: two written
transcripts as one of the joined list; `rvT_join`, `passT_join`, `rvT_length`: the view's rounds and
the tests of work). For rounds with at most one tree the like of `colAtST_join` is in
OnBytes/Slice/Unfold.lean.

Main names: `nTrees` · `drawnT_join`, `drawnT_length` · `wantsOf_append` · `fullOf_append` ·
`treeShT_append` · `colAtST_join`.

Limits: facts on lists of written rounds, at parameters: no file's rounds are shown to be cut so.
Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelJoinT
import OnBytes.Maker.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel
open _root_.Run.PQ (CK)

/-- How many trees a list of written rounds sends. -/
def nTrees (ds : List RDT) : ℕ := (ds.map (·.trees.length)).sum

theorem nTrees_cons (d : RDT) (ds : List RDT) : nTrees (d :: ds) = d.trees.length + nTrees ds := by
  simp [nTrees]

variable (C : CK)

/-- What is drawn in a joined transcript. -/
theorem drawnT_join : ∀ (ds es : List RDT) (τ : Iop.Tr (uLT C ds)) (σ : Iop.Tr (uLT C es)),
    drawnT C (ds ++ es) (rhoT C (ds ++ es) (joinR C ds es τ σ)) =
      drawnT C ds (rhoT C ds τ) ++ drawnT C es (rhoT C es σ)
  | [], _, _, _ => rfl
  | d :: ds, es, (m, c, τ), σ =>
    congrArg (drawnT C [d] (rhoT C [d] (m, c, ())) ++ ·) (drawnT_join ds es τ σ)

/-- As many draws as rounds. -/
theorem drawnT_length : ∀ (ds : List RDT) (ρ : Iop.Rho (uLT C ds)),
    (drawnT C ds ρ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, ρ) => congrArg (· + 1) (drawnT_length ds ρ)

/-- What the draws of two stretches ask for. -/
theorem wantsOf_append (a : ℕ) (dep : ℕ → Option ℕ) : ∀ (ds es : List RDT) (R₁ R₂ : List Fmt.Drawn),
    R₁.length = ds.length →
    wantsOf a dep (ds ++ es) (R₁ ++ R₂) = wantsOf a dep ds R₁ ++ wantsOf a dep es R₂
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => by cases h
  | _ :: _, _, [], _, h => by cases h
  | d :: ds, es, R :: Rs, R₂, h => by
    have ih := wantsOf_append a dep ds es Rs R₂ (Nat.succ.inj h)
    simp only [List.cons_append, wantsOf, ih, List.append_assoc]

/-- No draw is shortened in two stretches. -/
theorem fullOf_append : ∀ (ds es : List RDT) (R₁ R₂ : List Fmt.Drawn), R₁.length = ds.length →
    fullOf (ds ++ es) (R₁ ++ R₂) = (fullOf ds R₁ && fullOf es R₂)
  | [], _, [], _, _ => by simp [fullOf]
  | [], _, _ :: _, _, h => by cases h
  | _ :: _, _, [], _, h => by cases h
  | d :: ds, es, R :: Rs, R₂, h => by
    have ih := fullOf_append ds es Rs R₂ (Nat.succ.inj h)
    simp only [List.cons_append, fullOf, ih, Bool.and_assoc]

/-- A tree's shape. -/
theorem treeShT_append : ∀ (ds es : List RDT) (n : ℕ),
    treeShT (ds ++ es) n = if n < nTrees ds then treeShT ds n else treeShT es (n - nTrees ds)
  | [], es, n => by simp [nTrees]
  | d :: ds, es, n => by
    rw [List.cons_append, treeShT_cons, treeShT_cons, treeShT_append ds es, nTrees_cons]
    by_cases h1 : n < d.trees.length
    · have h2 : n < d.trees.length + nTrees ds := by omega
      simp only [h1, h2, if_true]
    · by_cases h2 : n - d.trees.length < nTrees ds
      · have h3 : n < d.trees.length + nTrees ds := by omega
        simp only [h1, h2, h3, if_true, if_false]
      · have h3 : ¬ n < d.trees.length + nTrees ds := by omega
        simp only [h1, h2, h3, if_false, Nat.sub_sub]

/-- A tree's column in a joined transcript. -/
theorem colAtST_join : ∀ (ds es : List RDT) (τ : Iop.Tr (uLT C ds)) (σ : Iop.Tr (uLT C es))
    (n x : ℕ),
    colAtST C (ds ++ es) (joinR C ds es τ σ) n x =
      if n < nTrees ds then colAtST C ds τ n x else colAtST C es σ (n - nTrees ds) x
  | [], es, _, σ, n, x => by
    show colAtST C es σ n x = _
    simp [nTrees]
  | d :: ds, es, (m, c, τ), σ, n, x => by
    have e1 : colAtST C (d :: ds ++ es) (joinR C (d :: ds) es (m, c, τ) σ) n x =
        if n < d.trees.length then (posAtT d.trees n x).map fun p => colT d.trees p (m.1 p)
        else colAtST C (ds ++ es) (joinR C ds es τ σ) (n - d.trees.length) x := rfl
    have e2 : colAtST C (d :: ds) (m, c, τ) n x =
        if n < d.trees.length then (posAtT d.trees n x).map fun p => colT d.trees p (m.1 p)
        else colAtST C ds τ (n - d.trees.length) x := rfl
    rw [e1, e2, colAtST_join ds es τ σ, nTrees_cons]
    by_cases h1 : n < d.trees.length
    · have h2 : n < d.trees.length + nTrees ds := by omega
      simp only [h1, h2, if_true]
    · by_cases h2 : n - d.trees.length < nTrees ds
      · have h3 : n < d.trees.length + nTrees ds := by omega
        simp only [h1, h2, h3, if_true, if_false]
      · have h3 : ¬ n < d.trees.length + nTrees ds := by omega
        simp only [h1, h2, h3, if_false, Nat.sub_sub]

end VerifiableInference.Desc.Sound
