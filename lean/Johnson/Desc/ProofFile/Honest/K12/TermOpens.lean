-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TermOpens.lean: the groups of columns in the term of a proximity
test, written as one list of openings. The term is `stagesAll`
(Johnson/Desc/K12/Honest/Stages.lean). Its result (`BOut`, Johnson/Prover/Link/BodyAll.lean) has
three lists: the rounds `rs`; for each round the written column of the tree that it sends, `tr`; and
the groups of columns `gs`. An opening is a triple, one for each group: the number of the round at
whose positions the group is read, the tree's depth, and the tree's origin (`From`): either its
number in a list T₀, meant for the trees that were there before the test, or the number of the
test's own round that sends it. `stagesAll` hands the new tree of each switch (the step from one
stage, `Fmt.M1.Stage`, to the next) to the next stage as a written column; here that column is named
by the round that sends it. `gs_stages` holds for every list of stages and at all values of its
other parameters. An inductive type, two definitions and one theorem.

  `gs_stages`: under the two hypotheses below, the term's list `gs` is the list of `opensFrom`, in
    order, with each opening (round, depth, origin) replaced by its group: `groupAt`
    (Johnson/Prover/Link/BodyAll.lean) at the depth, at the positions sampled in that round (the
    field `poss` of D at the round's number; D: the sampled challenges, `Fmt.Drawn`, by round) and
    at the origin's column
  `From`: an inductive type: a tree's origin: `old k`: number k in the list T₀; `sent r`: sent in
    round r
  `opensFrom`: the openings of the stages from a stage on: (round, depth, origin): public: of the
    stages' numbers and the trees' depths alone. A definition. Its arguments: the later stages; the
    stage; o, the number of the stage's first round; fr, the depth and the origin of each tree that
    holds the stage's rows
  `colBy T₀ TR`: a definition: an origin's written column: at `old k` the column of entry k of the
    list T₀ (of `Tree`, Stages.lean: a depth and a written column); at `sent r` it is `TR r`

By what. Induction on the list of the later stages, unfolding `stagesAll`, `aGroups` and `groupsAt`
(Stages.lean). `length_aFold` (Johnson/Desc/K12/Honest/Causal.lean: how many rounds a fold has)
finds the new tree's column in the term's list `tr`: it is the entry at the switch's first round.

Hypotheses of `gs_stages`. (1) The list `trees` that the term is handed is fr with each origin
replaced by its column: `trees = fr.map fun x => (x.1, colBy T₀ TR x.2)`. (2) TR agrees with the
term's own list `tr`: at every i with 0 < i, below the length of `tr`, entry i of `tr` is
`TR (o + i)`. Nothing is asked at i = 0.

Limits. Nothing on what a description's rounds declare to open. T₀, TR and fr are free parameters:
it is not stated that the trees of T₀ were sent before the test, nor that the depths in fr are
public. Where T₀ has no entry k, `colBy` gives at `old k` the column that is empty at every
position; no statement of this file excludes that case. `gs_stages` is an equation of two lists; it
holds also at values that no run reaches. Nothing on a decision, on completeness, on soundness or on
what is hidden.
-/
import Johnson.Desc.K12.Honest.Causal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- A tree's origin. `old k`: number k in a list of trees (T₀ in `colBy`). `sent r`: the tree that
round r sends. -/
inductive From where
  | old (k : ℕ)
  | sent (r : ℕ)
  deriving DecidableEq, Repr

/-- The openings of the stages from a stage on, as triples (round, depth, origin). The arguments:
the later stages; the stage; o: the number of the stage's first round; fr: the trees that hold the
stage's rows: depth and origin. At the last stage the trees of fr are read at the positions of round
o + 1. At any other stage, with n for `(sgOf cur).h + (sgOf cur).g`, they are read at the positions
of round o + 2 + n; the next stage begins at round o + n + 3, and one tree holds its rows, of depth
`(sgOf next).C.a`, sent in round o + 1 + n. -/
def opensFrom : List Fmt.M1.Stage → Fmt.M1.Stage → ℕ → List (ℕ × From) → List (ℕ × ℕ × From)
  | [], _, o, fr => fr.map fun x => (o + 1, x.1, x.2)
  | next :: rest, cur, o, fr =>
    fr.map (fun x => (o + 2 + ((sgOf cur).h + (sgOf cur).g), x.1, x.2)) ++
      opensFrom rest next (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        [((sgOf next).C.a, .sent (o + 1 + ((sgOf cur).h + (sgOf cur).g)))]

/-- An origin's written column. T₀: a list of trees, meant for those before the test; where it has
no entry k, the column at `old k` is empty at every position. TR: the written column of the tree
that a round sends, by the round's number. -/
def colBy (T₀ : List Tree) (TR : ℕ → ℕ → List UInt64) : From → ℕ → List UInt64
  | .old k => (T₀.getD k (0, fun _ => [])).2
  | .sent r => TR r

/-- **The term's groups are the openings' groups.** Hypotheses: `trees` is fr with each origin
replaced by its column; TR is any family that has, at each round of the stages after the first, the
written column that the term lists there in `tr`. -/
theorem gs_stages (p : P12) (K : BCoins) (T₀ : List Tree) (TR : ℕ → ℕ → List UInt64)
    (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (P : PS) (trees : List Tree) (fr : List (ℕ × From)),
    trees = fr.map (fun x => (x.1, colBy T₀ TR x.2)) →
    (∀ i, 0 < i → i < (stagesAll p K rest j cur l o t P trees D).tr.length →
      (stagesAll p K rest j cur l o t P trees D).tr.getD i (fun _ => []) = TR (o + i)) →
    (stagesAll p K rest j cur l o t P trees D).gs =
      (opensFrom rest cur o fr).map fun x => groupAt x.2.1 (D x.1).poss (colBy T₀ TR x.2.2)
  | [], j, cur, l, o, t, P, trees, fr, ht, _ => by
    subst ht
    show groupsAt _ _ = _
    unfold groupsAt opensFrom
    rw [List.map_map, List.map_map]
    rfl
  | next :: rest, j, cur, l, o, t, P, trees, fr, ht, hTR => by
    subst ht
    have hl := length_aFold K j cur o P (rowOf t) D
    simp only [stagesAll] at hTR ⊢
    -- The new tree's column is the one that `tr` lists at the switch's first round.
    have hcol : aCol rest.isEmpty next (aNext K rest.isEmpty j cur next o P D) =
        TR (o + 1 + ((sgOf cur).h + (sgOf cur).g)) := by
      have k := hTR (1 + ((sgOf cur).h + (sgOf cur).g)) (by omega) (by
        simp only [List.length_append, List.length_map, hl, List.length_cons]
        omega)
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [List.length_map, hl]),
        List.length_map, hl, Nat.sub_self] at k
      rw [show o + 1 + ((sgOf cur).h + (sgOf cur).g) = o + (1 + ((sgOf cur).h + (sgOf cur).g)) by
        omega, ← k]
      rfl
    have ih := gs_stages p K T₀ TR D rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (aRec3 p rest.isEmpty j cur next l o (fr.map fun x => (x.1, colBy T₀ TR x.2)) D
        (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
        (aSwitch cur o D (aAns p j cur next o D (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
          (aNext K rest.isEmpty j cur next o P D))))
      (aNext K rest.isEmpty j cur next o P D)
      [((sgOf next).C.a, aCol rest.isEmpty next (aNext K rest.isEmpty j cur next o P D))]
      [((sgOf next).C.a, .sent (o + 1 + ((sgOf cur).h + (sgOf cur).g)))]
      (by simp only [List.map_cons, List.map_nil, colBy, hcol])
      (fun i h0 hi => by
        have k := hTR (((sgOf cur).h + (sgOf cur).g) + 3 + i) (by omega) (by
          simp only [List.length_append, List.length_map, hl, List.length_cons, List.length_nil]
          omega)
        rw [List.getD_append_right _ _ _ _ (by
          simp only [List.length_append, List.length_map, hl, List.length_cons, List.length_nil]
          omega)] at k
        simp only [List.length_append, List.length_map, hl, List.length_cons,
          List.length_nil] at k
        rw [show (sgOf cur).h + (sgOf cur).g + 3 + i -
          (1 + ((sgOf cur).h + (sgOf cur).g) + (0 + 1 + 1)) = i by omega] at k
        rw [k]
        congr 1
        omega)
    rw [ih, opensFrom, List.map_append, List.map_map]
    unfold aGroups groupsAt
    rw [List.map_map]
    rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.gs_stages
#print axioms ProofFile.Honest.K12.From
#print axioms ProofFile.Honest.K12.opensFrom
#print axioms ProofFile.Honest.K12.colBy
