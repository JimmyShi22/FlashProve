-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/SisterH.lean:
a second text of the one arm of the head's keys that holds long sums, and of the search for a
column's segment, with their factors read off rows that are handed in; and the theorems that, at
rows whose values are the library's own, it is the library's text. Definitions with code, and
theorems without a hypothesis but the one that is named.

Terms. Honest/K3/GLOSSARY.md. In this file: the library's text is `gamH`, `lg`, `kvOf` and `kvH` of
OnBytes/Tie/Pv/Lookup/Ends/H.lean. A row: `Row` (Honest/K3/Tab/SisterG.lean).

Why. A key of the segment HD0 holds two logits: the checked token's and its own entry's. The
library's text makes each as a sum over the model's channels whose two factors (`nrm`, `wH`) are
made anew from the cells; the checked token's logit is the same for all entries of a position. And
`kvOf` finds a key's segment by `colH`, which walks the segments' lists of positions anew for each
key.

This is a second text beside definitions of the library. It is kept as thin as could be: of `gamH`
the arm HD0 alone is written anew, with `lg`, and is tested first (in the library NF stands in front
of it); every other arm calls the library. `kvOfBy` is the text of `kvOf` but for `col q j` in the
place of `colH P.L q j`. `affH` is not touched.
It is typed for the honest prover's own sake, and for that alone.
`mul0` (Honest/K3/Tab/SisterG.lean) changes what a program evaluates, not the value: at a place
that is not real (a position that is not covered, an entry beyond the vocabulary) no logit is made.

What is defined.
  `InnerH`: the rows that the arm reads: the normalized activations of a position by channel, the
    head's weights of an entry by channel, the checked token's logit by position.
  `InnerH.Is`: the rows' values are the library's own. Meant as a hypothesis: the theorems'.
  `innerOfH`: the library's own values as rows with empty arrays.
  `lgBy`, `gamHBy`, `kvOfBy`, `kvHBy`: the second text.

What is shown.
  `innerOfH_is`: that hypothesis holds of `innerOfH`.
  `lgBy_of`, `gamHBy_of`: under `InnerH.Is` they are `lg` and `gamH`.
  `kvOfBy_of`: at `colH P.L` it is `kvOf`: by `rfl`.
  `kvHBy_of`: the last theorem, conditional on `InnerH.Is P cell I`: `kvHBy P cell I (colH P.L)` is
    `kvH P cell`.

Imported. OnBytes/Tie/Pv/Lookup/Ends/H.lean and what stands beneath it; Honest/K3/Tab/SisterG.lean.

Limits. Nothing says how long anything takes. At rows of which `InnerH.Is` fails nothing is said.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Tie.Pv.Lookup.Ends.H
import Johnson.Desc.ProofFile.Honest.K3.Tab.SisterG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabH
open OnBytes.Model OnBytes.Ends OnBytes.Ends.H
open ProofFile.Honest.K3.TabG (Row mul0 mul0_eq)

/-- **The rows that the arm HD0 reads.** -/
structure InnerH (R : Type) where
  /-- of a position: the normalized activations by channel -/
  nr : ℕ → Row R
  /-- of an entry of the vocabulary: the head's weights by channel -/
  wh : ℕ → Row R
  /-- the checked token's logit by position -/
  lw : Row R

variable {R : Type} [Field R]

/-- **The theorems' hypothesis: the rows' values are the library's own.** -/
structure InnerH.Is (P : PubH) (cell : NameH → R) (I : InnerH R) : Prop where
  nr : ∀ t k, (I.nr t).get k = nrm P cell k t
  wh : ∀ v k, (I.wh v).get k = wH P cell k v
  lw : ∀ t, I.lw.get t = lg P cell (P.win.getD t 0) t

/-- The library's own values, as rows with empty arrays. -/
def innerOfH (P : PubH) (cell : NameH → R) : InnerH R :=
  { nr := fun t => ⟨#[], fun k => nrm P cell k t⟩
    wh := fun v => ⟨#[], fun k => wH P cell k v⟩
    lw := ⟨#[], fun t => lg P cell (P.win.getD t 0) t⟩ }

/-- That hypothesis holds of them. -/
theorem innerOfH_is (P : PubH) (cell : NameH → R) : (innerOfH P cell).Is P cell :=
  ⟨fun _ _ => Row.get_nil _ _, fun _ _ => Row.get_nil _ _, fun _ => Row.get_nil _ _⟩

variable (P : PubH) (cell : NameH → R) (I : InnerH R)

/-- `lg`, its factors off two rows. -/
def lgBy (v t : ℕ) : R :=
  let a := I.nr t
  let b := I.wh v
  (List.range P.h.d).foldl (fun s k => s + a.get k * b.get k) 0

/-- **`gamH`, the arm HD0 off rows.** -/
def gamHBy [DecidableEq R] (sn : String) (x t : ℕ) : R :=
  if sn == "HD0" then iw P * mul0 (real P x t) fun _ => I.lw.get t - lgBy P I x t
  else gamH P cell sn x t

/-- **`kvOf`, with the entry and the segment of a column read off a function that is handed in.**
The library's text but for `col q j` in the place of `colH P.L q j`. -/
def kvOfBy (col : ℕ → ℕ → Option (String × ℕ)) (f : String → ℕ → ℕ → R) (q i : ℕ) : R :=
  match col q (i / P.h.T) with
  | some (sn, x) => f sn x (i % P.h.T)
  | none => (tauN P.L.fs q (t0N P.L.fs q) : R)

/-- `kvH` over the two. -/
def kvHBy [DecidableEq R] (col : ℕ → ℕ → Option (String × ℕ)) (q i : ℕ) : R :=
  kvOfBy P col (fun sn x t => affH P cell sn x t + gamHBy P cell I sn x t) q i

/-- At the library's `colH` it is `kvOf`. -/
theorem kvOfBy_of (f : String → ℕ → ℕ → R) (q i : ℕ) :
    kvOfBy P (colH P.L) f q i = kvOf P f q i := rfl

variable {P cell I}

/-- Conditional on `InnerH.Is`: `lgBy` is `lg`. -/
theorem lgBy_of (h : I.Is P cell) (v t : ℕ) : lgBy P I v t = lg P cell v t := by
  simp only [lgBy, lg, h.nr, h.wh]

/-- Conditional on `InnerH.Is`: `gamHBy` is `gamH`. -/
theorem gamHBy_of [DecidableEq R] (h : I.Is P cell) (sn : String) (x t : ℕ) :
    gamHBy P cell I sn x t = gamH P cell sn x t := by
  unfold gamHBy
  by_cases h1 : (sn == "HD0") = true
  · have e : sn = "HD0" := by simpa using h1
    have n1 : ¬ (sn == "NF") = true := by subst e; decide
    simp only [if_pos h1, if_neg n1, gamH, mul0_eq, h.lw, lgBy_of h]
  · simp only [if_neg h1]

/-- **Conditional on `InnerH.Is`: `kvHBy` at the library's `colH` is `kvH`.** -/
theorem kvHBy_of [DecidableEq R] (h : I.Is P cell) (q i : ℕ) :
    kvHBy P cell I (colH P.L) q i = kvH P cell q i := by
  have e : (fun sn x t => affH P cell sn x t + gamHBy P cell I sn x t) = segH P cell := by
    funext sn x t
    rw [gamHBy_of h]
    rfl
  unfold kvHBy
  rw [e]
  rfl

end ProofFile.Honest.K3.TabH

#print axioms ProofFile.Honest.K3.TabH.innerOfH_is
#print axioms ProofFile.Honest.K3.TabH.kvOfBy_of
#print axioms ProofFile.Honest.K3.TabH.lgBy_of
#print axioms ProofFile.Honest.K3.TabH.gamHBy_of
#print axioms ProofFile.Honest.K3.TabH.kvHBy_of
