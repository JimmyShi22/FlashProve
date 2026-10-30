-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/LabelsLaw.lean: labelsOk = true gives what that test checks, in plain facts:
the openings that the first switch of the proximity test (the kind K12) declares bear, in turn and
uncut, the numbers of the trees of the group in the record's book.

labelsOk (Johnson/Desc/K12/Law/FirstCut.lean) is the second half of the guard on the group's trees
in the block's batching (Johnson/Desc/K12/JoinGuarded.lean). Statements and proofs; no definition of
Johnson/Desc/K12/Law/FirstCut.lean is turned.
Main names:
  `tree_of_ts`: every place in D.ts is the place of a tree of the book D.book: a member's tree or
    the mask's.
  `labels_of_ok`: under labelsOk p t = true, at the record t behind the batching: the plain data D
    can be made; its declared openings are those of the first switch's two declared rounds; they are
    as many as the trees' places D.ts; and for each i the i-th declared opening's label is the
    number of the tree that stands in the book at the i-th of these places.
Why the test is there. The key of a tree is its number less the chain's first tree's number, cut off
at 0. Where the first tree's number is above the numbers of all the group's trees, all keys are 0
and gpOk's clause opens.key tells no two trees apart. The labels are not cut, so they tell apart any
two trees whose numbers differ.
Limits: No soundness is claimed, and nothing is said on hiding.
A yes gives these facts; that the test says yes wherever they hold is not shown. That the numbers of
the group's trees differ is not shown here. In what order the places D.ts stand is not restated here
(Made.ts, Johnson/Desc/K12/Law/FirstOkLaw.lean: Fmt.listOf of the members' places and the mask's).
No theorem of the law spends labels_of_ok: the reading goes by the order of the dealt columns.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.FirstCutLaw

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- Every place in D.ts is the place of a tree of the book. -/
theorem tree_of_ts (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (D : Plain)
    (hm : Made p t a L D) (τ : ℕ) (hτ : τ ∈ D.ts) : ∃ T, D.book.trees[τ]? = some T := by
  rw [hm.ts] at hτ
  have h1 := (Fmt.listOf_mem _ _).1 hτ
  rcases List.mem_append.1 h1 with h2 | h2
  · obtain ⟨m, hmem, rfl⟩ := List.mem_map.1 h2
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    obtain ⟨T, hT, _⟩ := (hm.mem i).2.tree
    exact ⟨T, hT⟩
  · obtain rfl := List.mem_singleton.1 h2
    obtain ⟨T, hT, _⟩ := hm.fresh.tree
    exact ⟨T, hT⟩

/-- What a yes of labelsOk gives. -/
theorem labels_of_ok (p : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (hs : p.nums.stages = a :: rest)
    (hp : t.pass = .claim row L) (h : labelsOk p t = true) :
    ∃ D, gpOf p t a L = some D ∧ D.opens = opensOf p a.k ∧ D.opens.length = D.ts.length ∧
      ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (τ : ℕ), D.opens[i]? = some o → D.ts[i]? = some τ →
        ∃ T, D.book.trees[τ]? = some T ∧ o.1.tree = T.number := by
  unfold labelsOk labelsL at h
  rw [hs, hp] at h
  dsimp only at h
  cases hD : gpOf p t a L with
  | none =>
    rw [hD] at h
    cases h
  | some D =>
    rw [hD] at h
    have e : D.opens.map (·.1.tree) = D.ts.map (numAt D.book) := by
      simpa [ok] using h
    have hm := made_of p t a L D hD
    refine ⟨D, rfl, hm.opens, ?_, fun i o τ ho hτ => ?_⟩
    · have := congrArg List.length e
      rwa [List.length_map, List.length_map] at this
    · obtain ⟨T, hT⟩ := tree_of_ts p t a L D hm τ (List.mem_of_getElem? hτ)
      have e' := congrArg (·[i]?) e
      simp only [List.getElem?_map, ho, hτ, Option.map_some, Option.some.injEq] at e'
      refine ⟨T, hT, ?_⟩
      rw [e']
      unfold numAt
      rw [hT]
      rfl

end H2K.First
