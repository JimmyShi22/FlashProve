-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/WrittenOfG.lean: the written rounds of a proximity test's place (the kind K12)
hang on its declared rounds only through what a reader takes of them; and so a place whose declared
rounds are a stretch of a chain has the written rounds of any place of which readers take that
stretch.

Why. CondAtFull.lean has one named premise: a made place's written rounds (`writtenOf`, PubOk.lean)
are a closed place's. What is known of a description in the goals' scope is its declared rounds as
readers take them (`Fmt.DeclaredRound.round`, Fmt/Parsed.lean), written out as closed lists. This file
leads from the one to the other; it names no description.
Main names:
  `ownOfR`, `round_keeps`: a declared round as a reader takes it keeps its entry and the numbers of
    the chain's own trees that it opens.
  `layR`, `layW_eq_layR`, `layW_congr_round`: so two lists of declared rounds of which readers take
    the same have the same written rounds.
  `mapM_append_some`, `mapM_stretch`: what readers take of a stretch of a chain is that stretch of
    what they take of the chain.
  `layOpens_length`, `roundsOfNums_length`: two places with the same stages and bits of work declare
    as many rounds.
  `writtenOf_at_stretch`: the theorem.
Limits: on the makers' texts alone. Where the stretch begins, and that a place's declared rounds are
a stretch of a chain, are premises. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.WrittenReads
import Fmt.Parsed

set_option autoImplicit false
namespace H2K.Pub
open H2U (TestNums roundsOfNums)

/-- The own number of a tree that a round opens, as a reader takes the round. -/
def ownOfR : Fmt.Shape × Fmt.Src → Option Nat
  | (_, .own n) => some n
  | _ => none

/-- The readers' sources keep the own numbers. -/
theorem ownOfR_of_mapM (e : List (List ByteArray × ByteArray)) :
    ∀ (l : List (Fmt.Shape × Fmt.TreeSource)) (os : List (Fmt.Shape × Fmt.Src)),
    (l.mapM fun (o : Fmt.Shape × Fmt.TreeSource) => (o.2.src e).map fun s => (o.1, s)) = some os →
    os.filterMap ownOfR = l.filterMap ownOf
  | [], os, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | (sh, d) :: l, os, h => by
    rw [List.mapM_cons] at h
    cases hd : d.src e with
    | none =>
      simp [hd] at h
    | some s =>
      cases hl :
          (l.mapM fun (o : Fmt.Shape × Fmt.TreeSource) => (o.2.src e).map fun s => (o.1, s)) with
      | none => simp [hd, hl] at h
      | some os' =>
        simp [hd, hl] at h
        subst h
        have ih := ownOfR_of_mapM e l os' hl
        cases d with
        | own n =>
          cases hd
          simp [ownOfR, ownOf, ih]
        | taken c p =>
          have hs : ∃ r st, s = .given r st := by
            unfold Fmt.TreeSource.src at hd
            cases h1 : e[c]? with
            | none => simp [h1] at hd
            | some x =>
              cases h2 : x.1[p]? with
              | none => simp [h1, h2] at hd
              | some r =>
                simp [h1, h2] at hd
                exact ⟨r, x.2, hd.symm⟩
          obtain ⟨r, st, rfl⟩ := hs
          simp [ownOfR, ownOf, ih]

/-- A declared round as a reader takes it keeps its entry and its own numbers. -/
theorem round_keeps {e : List (List ByteArray × ByteArray)} {r : Fmt.DeclaredRound} {x : Fmt.Round}
    (h : r.round e = some x) :
    x.entry = r.entry ∧ x.opens.filterMap ownOfR = r.opens.filterMap ownOf := by
  unfold Fmt.DeclaredRound.round at h
  cases hk : Fmt.kindOf r.entry.name with
  | none => simp [hk] at h
  | some k =>
    cases hl : (r.opens.mapM fun (o : Fmt.Shape × Fmt.TreeSource) =>
        (o.2.src e).map fun s => (o.1, s)) with
    | none => simp [hk, hl] at h
    | some os =>
      simp [hk, hl] at h
      subst h
      exact ⟨rfl, ownOfR_of_mapM e _ os hl⟩

/-- `layW` on rounds as a reader takes them. -/
def layR : List Fmt.Round → List Fmt.Shape → Option (List WR)
  | [], [] => some []
  | [], _ :: _ => none
  | r :: rs, sh =>
    match Fmt.kindOf r.entry.name with
    | none => none
    | some k =>
      if r.entry.roots == 0 then
        (layR rs sh).map (⟨r.entry, k, r.entry.cut, none, r.opens.filterMap ownOfR⟩ :: ·)
      else if r.entry.roots == 1 then
        match sh with
        | s :: t => (layR rs t).map
            (⟨r.entry, k, r.entry.cut, some s, r.opens.filterMap ownOfR⟩ :: ·)
        | [] => none
      else none

/-- **The written rounds hang on the declared rounds only through what a reader takes of them.** -/
theorem layW_eq_layR (e : List (List ByteArray × ByteArray)) :
    ∀ (ds : List Fmt.DeclaredRound) (xs : List Fmt.Round), ds.mapM (·.round e) = some xs →
    ∀ sh : List Fmt.Shape, layW ds sh = layR xs sh
  | [], xs, h, sh => by
    rw [List.mapM_nil] at h
    cases h
    cases sh <;> rfl
  | r :: ds, xs, h, sh => by
    rw [List.mapM_cons] at h
    cases hr : r.round e with
    | none => simp [hr] at h
    | some x =>
      cases hl : ds.mapM (·.round e) with
      | none => simp [hr, hl] at h
      | some xs' =>
        simp [hr, hl] at h
        subst h
        obtain ⟨e1, e2⟩ := round_keeps hr
        have ih := layW_eq_layR e ds xs' hl
        rw [layW, layR, e1, e2]
        simp only [ih]
        rfl

/-- Two lists of declared rounds of which readers take the same have the same written rounds. -/
theorem layW_congr_round {e e' : List (List ByteArray × ByteArray)} {ds ds' : List Fmt.DeclaredRound}
    {xs : List Fmt.Round} (h : ds.mapM (·.round e) = some xs) (h' : ds'.mapM (·.round e') = some xs)
    (sh : List Fmt.Shape) : layW ds sh = layW ds' sh :=
  (layW_eq_layR e ds xs h sh).trans (layW_eq_layR e' ds' xs h' sh).symm

/-! ## A stretch of a chain -/

/-- `mapM` into `Option` over an append. -/
theorem mapM_append_some {α β : Type} (f : α → Option β) :
    ∀ (a b : List α) (xs : List β), (a ++ b).mapM f = some xs →
    a.mapM f = some (xs.take a.length) ∧ b.mapM f = some (xs.drop a.length)
  | [], b, xs, h => by
    rw [List.nil_append] at h
    exact ⟨by rw [List.mapM_nil]; rfl, h⟩
  | x :: a, b, xs, h => by
    rw [List.cons_append, List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hl : (a ++ b).mapM f with
      | none => simp [hx, hl] at h
      | some ys =>
        simp [hx, hl] at h
        subst h
        obtain ⟨i1, i2⟩ := mapM_append_some f a b ys hl
        refine ⟨?_, ?_⟩
        · rw [List.mapM_cons, hx, i1]
          rfl
        · rw [i2]
          rfl

/-- What readers take of a stretch of a chain is that stretch of what they take of the chain. -/
theorem mapM_stretch {α β : Type} (f : α → Option β) (pre ds post : List α) (xs : List β)
    (h : (pre ++ (ds ++ post)).mapM f = some xs) :
    ds.mapM f = some ((xs.drop pre.length).take ds.length) :=
  (mapM_append_some f ds post _ (mapM_append_some f pre (ds ++ post) xs h).2).1

/-- `layOpens` keeps the number of rounds. -/
theorem layOpens_length (own : Bool) : ∀ (R : List Fmt.Round) (seen : Bool)
    (X : List (List (Fmt.Shape × Fmt.TreeSource))) (ds : List Fmt.DeclaredRound),
    H2U.layOpens own seen R X = some ds → ds.length = R.length
  | [], _, [], ds, h => by
    simp only [H2U.layOpens] at h
    cases h
    rfl
  | [], _, _ :: _, ds, h => by
    simp only [H2U.layOpens] at h
    cases h
  | r :: rs, seen, X, ds, h => by
    by_cases hr : r.opens.isEmpty = true
    · simp only [H2U.layOpens, hr, if_true] at h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [List.length_cons, List.length_cons, layOpens_length own rs _ X t ht]
    · cases X with
      | nil =>
        simp only [H2U.layOpens, hr] at h
        cases h
      | cons x X' =>
        simp only [H2U.layOpens, hr] at h
        by_cases hx : x.isEmpty = true
        · simp only [hx, if_true] at h
          simp at h
        · simp only [hx] at h
          simp only [Bool.false_eq_true, if_false] at h
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
          rw [List.length_cons, List.length_cons, layOpens_length own rs _ X' t ht]

/-- Two places with the same stages and bits of work declare as many rounds. -/
theorem roundsOfNums_length {N N' : TestNums} {ds ds' : List Fmt.DeclaredRound}
    (h : roundsOfNums N = some ds) (h' : roundsOfNums N' = some ds') (h2 : N.work = N'.work)
    (h3 : N.stages = N'.stages) : ds.length = ds'.length := by
  unfold roundsOfNums at h h'
  rw [← h3, ← h2] at h'
  cases hs : N.stages with
  | nil =>
    rw [hs] at h
    cases h
  | cons s t =>
    cases t with
    | nil =>
      rw [hs] at h
      cases h
    | cons next rest =>
      rw [hs] at h h'
      rw [layOpens_length _ _ _ _ _ h, layOpens_length _ _ _ _ _ h']
      rfl

/-- **At a stretch of a chain.** D: a chain's declared rounds; ds: the rounds that the place N
declares, a stretch of D behind `pre`; xs: what readers take of D. N0: a place with the same stages,
bits of work and own mask, and the same sum of the first tree's number and the first free own
number, of whose declared rounds readers take just that stretch of xs. Then the two places have the
same written rounds. -/
theorem writtenOf_at_stretch {N N0 : TestNums} {pre ds post ds0 : List Fmt.DeclaredRound}
    {e e0 : List (List ByteArray × ByteArray)} {xs : List Fmt.Round}
    (hx : (pre ++ (ds ++ post)).mapM (·.round e) = some xs) (hN : roundsOfNums N = some ds)
    (h0 : roundsOfNums N0 = some ds0)
    (hc : ds0.mapM (·.round e0) = some ((xs.drop pre.length).take ds0.length))
    (h2 : N.work = N0.work) (h3 : N.stages = N0.stages) (h4 : N.ownMask = N0.ownMask)
    (hT : N.firstTree + N.free = N0.firstTree + N0.free) : writtenOf N = writtenOf N0 := by
  have hl := roundsOfNums_length hN h0 h2 h3
  have hd := mapM_stretch (·.round e) pre ds post xs hx
  rw [hl] at hd
  have hs : N.sent = N0.sent := by
    unfold TestNums.sent
    rw [h3, h4]
  have hsh : (N.sent.zipIdx.map fun t => (N.own t.1.1 t.1.2 (N.free + t.2)).1) =
      N0.sent.zipIdx.map fun t => (N0.own t.1.1 t.1.2 (N0.free + t.2)).1 := by
    rw [hs]
    refine List.map_congr_left fun t _ => ?_
    show (⟨t.1.1, t.1.2, false, N.firstTree + (N.free + t.2)⟩ : Fmt.Shape) =
      ⟨t.1.1, t.1.2, false, N0.firstTree + (N0.free + t.2)⟩
    have : N.firstTree + (N.free + t.2) = N0.firstTree + (N0.free + t.2) := by omega
    rw [this]
  unfold writtenOf
  rw [hN, h0, hsh]
  exact layW_congr_round hd hc _

end H2K.Pub

#print axioms H2K.Pub.mapM_stretch
#print axioms H2K.Pub.roundsOfNums_length
#print axioms H2K.Pub.writtenOf_at_stretch
#print axioms H2K.Pub.round_keeps
#print axioms H2K.Pub.layW_eq_layR
#print axioms H2K.Pub.layW_congr_round
