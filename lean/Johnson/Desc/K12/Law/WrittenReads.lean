-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/WrittenReads.lean: what the written rounds of a proximity test's place (the
kind K12) read of the place's numbers.

`writtenOf` (PubOk.lean) makes the place's declared rounds (`H2U.roundsOfNums`) into written rounds.
It reads six of the seven numbers whole. Of the seventh, the trees of the test's group, which the
first round "CS" opens, a written round keeps only the numbers of the chain's own trees; shapes, and
trees taken from another chain, are dropped; and the maker refuses an empty list.
Main names:
  `Alike x y`: two lists of trees are both empty or neither, and have the same own numbers.
    `AlikeAll`: member by member.
  `layW_cons_alike`, `layOpens_alike`: the two makers on lists that are alike.
  `writtenOf_reads`: two records of numbers that agree in six fields and are alike in the seventh
    have the same written rounds.
  `writtenOf_of_rounds`: so have two records with the same declared rounds, the same stages, the
    same own mask and the same sum of the first tree's number and the first free own number.
Limits: on the makers' texts alone; no Mathlib beneath. No field is shown idle. Nothing on
soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.PubOk

set_option autoImplicit false
namespace H2K.Pub
open H2U (TestNums roundsOfNums layOpens)

/-- Two lists of trees are read alike: both empty or neither, and the same own numbers. -/
def Alike (x y : List (Fmt.Shape × Fmt.TreeSource)) : Prop :=
  x.isEmpty = y.isEmpty ∧ x.filterMap ownOf = y.filterMap ownOf

theorem bind_map_layW {α : Type} (o : Option (List Fmt.DeclaredRound))
    (g : List Fmt.DeclaredRound → Option α) (d : Fmt.DeclaredRound) :
    (o.map (d :: ·)).bind g = o.bind fun ds => g (d :: ds) := by
  cases o <;> rfl

/-- What `layW` makes of a round and the rest hangs on the round's entry and own numbers alone. -/
theorem layW_cons_alike (e : Fmt.Entry) (s : List Fmt.Stored)
    (x y : List (Fmt.Shape × Fmt.TreeSource)) (hxy : x.filterMap ownOf = y.filterMap ownOf)
    (o o' : Option (List Fmt.DeclaredRound))
    (ih : ∀ sh, o.bind (layW · sh) = o'.bind (layW · sh)) (sh : List Fmt.Shape) :
    (o.bind fun ds => layW (⟨e, s, x⟩ :: ds) sh) = o'.bind fun ds => layW (⟨e, s, y⟩ :: ds) sh := by
  have key : ∀ (z : List (Fmt.Shape × Fmt.TreeSource)) (u : Option (List Fmt.DeclaredRound)),
      (u.bind fun ds => layW (⟨e, s, z⟩ :: ds) sh) =
        match Fmt.kindOf e.name with
        | none => none
        | some k =>
          if e.roots == 0 then
            (u.bind (layW · sh)).map (⟨e, k, e.cut, none, z.filterMap ownOf⟩ :: ·)
          else if e.roots == 1 then
            match sh with
            | s0 :: t => (u.bind (layW · t)).map (⟨e, k, e.cut, some s0, z.filterMap ownOf⟩ :: ·)
            | [] => none
          else none := by
    intro z u
    cases u with
    | none =>
      simp only [Option.bind_none, Option.map_none]
      split
      · rfl
      · split
        · rfl
        · split
          · split <;> rfl
          · rfl
    | some ds =>
      simp only [Option.bind_some]
      rw [layW]
      rfl
  rw [key x o, key y o', hxy, ih sh]
  split
  · rfl
  · split
    · rfl
    · split
      · split
        · rw [ih]
        · rfl
      · rfl

theorem isEmpty_app {α : Type} (a b : List α) : (a ++ b).isEmpty = (a.isEmpty && b.isEmpty) := by
  cases a <;> rfl

theorem alike_refl (x : List (Fmt.Shape × Fmt.TreeSource)) : Alike x x := ⟨rfl, rfl⟩

/-- Two lists of such lists, member by member. -/
inductive AlikeAll : List (List (Fmt.Shape × Fmt.TreeSource)) →
    List (List (Fmt.Shape × Fmt.TreeSource)) → Prop
  | nil : AlikeAll [] []
  | cons {x y : List (Fmt.Shape × Fmt.TreeSource)} {X Y : List (List (Fmt.Shape × Fmt.TreeSource))} :
    Alike x y → AlikeAll X Y → AlikeAll (x :: X) (y :: Y)

theorem alikeAll_refl : ∀ X : List (List (Fmt.Shape × Fmt.TreeSource)), AlikeAll X X
  | [] => .nil
  | x :: X => .cons (alike_refl x) (alikeAll_refl X)

/-- The written rounds hang on the lists of trees only through what `Alike` keeps. -/
theorem layOpens_alike (own : Bool) : ∀ (R : List Fmt.Round) (seen : Bool)
    (X Y : List (List (Fmt.Shape × Fmt.TreeSource))), AlikeAll X Y → ∀ sh : List Fmt.Shape,
    (layOpens own seen R X).bind (layW · sh) = (layOpens own seen R Y).bind (layW · sh)
  | [], _, _, _, h, _ => by
    cases h with
    | nil => rfl
    | cons _ _ => rfl
  | r :: rs, seen, X, Y, h, sh => by
    by_cases hr : r.opens.isEmpty = true
    · simp only [layOpens, hr, if_true]
      rw [bind_map_layW, bind_map_layW]
      exact layW_cons_alike _ [] [] [] rfl _ _ (layOpens_alike own rs _ X Y h) sh
    · cases h with
      | nil => simp only [layOpens, hr]
      | @cons x y X' Y' hx ht =>
        simp only [layOpens, hr, hx.1]
        by_cases hy : y.isEmpty = true
        · simp only [hy, if_true]
          rfl
        · simp only [hy]
          simp only [Bool.false_eq_true, if_false]
          rw [bind_map_layW, bind_map_layW]
          exact layW_cons_alike _ [] x y hx.2 _ _ (layOpens_alike own rs _ X' Y' ht) sh

/-- **What the written rounds read of a place's numbers**: six fields whole; of the seventh, the
trees of the test's group, only whether it is empty and the numbers of its own trees. -/
theorem writtenOf_reads {N N' : TestNums} (h1 : N.rows = N'.rows) (h2 : N.work = N'.work)
    (h3 : N.stages = N'.stages) (h4 : N.ownMask = N'.ownMask) (h5 : N.free = N'.free)
    (h6 : N.firstTree = N'.firstTree) (h7 : Alike N.first N'.first) :
    writtenOf N = writtenOf N' := by
  obtain ⟨rows, work, stages, ownMask, first, free, firstTree⟩ := N
  obtain ⟨rows', work', stages', ownMask', first', free', firstTree'⟩ := N'
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6
  unfold writtenOf roundsOfNums
  cases stages with
  | nil => rfl
  | cons s t =>
    cases t with
    | nil => rfl
    | cons next rest =>
      refine layOpens_alike _ _ _ _ _ (.cons ⟨?_, ?_⟩ (alikeAll_refl _)) _
      · rw [isEmpty_app, isEmpty_app, h7.1]
        rfl
      · rw [List.filterMap_append, List.filterMap_append, h7.2]
        rfl

/-- **From the declared rounds.** Beyond the declared rounds the written rounds read only the shapes
of the trees that the test sends: the stages, whether the first fold sends its own mask, and the sum
of the first tree's number and the first free own number. -/
theorem writtenOf_of_rounds {N N' : TestNums} (hR : roundsOfNums N = roundsOfNums N')
    (h3 : N.stages = N'.stages) (h4 : N.ownMask = N'.ownMask)
    (hT : N.firstTree + N.free = N'.firstTree + N'.free) : writtenOf N = writtenOf N' := by
  have hs : N.sent = N'.sent := by
    unfold TestNums.sent
    rw [h3, h4]
  have hsh : (N.sent.zipIdx.map fun t => (N.own t.1.1 t.1.2 (N.free + t.2)).1) =
      N'.sent.zipIdx.map fun t => (N'.own t.1.1 t.1.2 (N'.free + t.2)).1 := by
    rw [hs]
    refine List.map_congr_left fun t _ => ?_
    show (⟨t.1.1, t.1.2, false, N.firstTree + (N.free + t.2)⟩ : Fmt.Shape) =
      ⟨t.1.1, t.1.2, false, N'.firstTree + (N'.free + t.2)⟩
    have : N.firstTree + (N.free + t.2) = N'.firstTree + (N'.free + t.2) := by omega
    rw [this]
  unfold writtenOf
  rw [hR, hsh]

end H2K.Pub

#print axioms H2K.Pub.writtenOf_of_rounds
#print axioms H2K.Pub.layOpens_alike
#print axioms H2K.Pub.writtenOf_reads
