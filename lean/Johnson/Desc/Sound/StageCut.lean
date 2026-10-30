-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StageCut.lean: a stage over two stretches of written rounds behind each other
(`stageIOR`, OnBytes/Maker/Stage.lean) is the stage over the first, then the stage over the second
at the oracles that the first leaves: where all trees are at hand and all are left at every border
(`Frame`, Johnson/Desc/Sound/ChainRule.lean). Statements and proofs. No protocol occurs here.

Main names.
  `stg F b ds`: the stage's data: the first own tree's number b, the written rounds' data ds.
  `ListedAt F b ds`: each tree that ds sends stands in `F.all` under its number, and the first entry
    of that number has its depth. `OpensBelow b ds`: no round of ds opens a tree that is sent behind
    ds.
  `depth_fst`, `depth_snd`, `sWants_join`: depths and wants. `sCol_fst`, `sCol_snd`: a column; the
    second stretch reads the first one's trees through the oracles left.
  `sView_rounds_join`, `sView_opened_join`, `sTests_join`, `sLeft_join`: the view, the tests in
    front of the run, the trees left.
  `stage_cut`: **the law**: as reductions: the same verdict, state and oracles left, for three runs
    of which the one on the joined view is the first, then the second.

Limits: a law on the library's stage, at parameters: `ListedAt` and `OpensBelow` are premises, shown
of no file's data here. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Cuts
import Johnson.Desc.Sound.ChainRule
import OnBytes.Maker.RowWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel
open _root_.Run.PQ (CK SgX)
open _root_.Iop (IOR)

/-- A stage's data at a frame: all trees at hand, all left. -/
abbrev stg (F : Frame) (b : ℕ) (ds : List RDT) : StageD := ⟨F.a, b, F.all, ds, F.key, F.all⟩

/-- Each tree that ds sends is listed under its number, at its depth. -/
def ListedAt (F : Frame) (b : ℕ) (ds : List RDT) : Prop :=
  ∀ n sh, treeShT ds n = some sh → (F.all.find? (·.no == b + n)).map (·.a) = some sh.a

/-- No round of ds opens a tree that is sent behind ds. -/
def OpensBelow (b : ℕ) (ds : List RDT) : Prop := ∀ d ∈ ds, ∀ j ∈ d.opens, j < b + nTrees ds

theorem treeShT_some_of_lt : ∀ (ds : List RDT) (n : ℕ), n < nTrees ds → ∃ sh, treeShT ds n = some sh
  | [], n, h => by simp [nTrees] at h
  | d :: ds, n, h => by
    rw [treeShT_cons]
    rw [nTrees_cons] at h
    by_cases h1 : n < d.trees.length
    · exact ⟨d.trees[n], by rw [if_pos h1]; exact List.getElem?_eq_getElem h1⟩
    · rw [if_neg h1]
      exact treeShT_some_of_lt ds _ (by omega)

variable (C : CK) (F : Frame) (b : ℕ) (ds es : List RDT)

theorem depth_eq (j : ℕ) (xs : List RDT) : (stg F b xs).depth j =
    if j < b then (F.all.find? (·.no == j)).map (·.a) else (treeShT xs (j - b)).map (·.a) := rfl

theorem depth_fst (j : ℕ) (h : j < b + nTrees ds) :
    (stg F b (ds ++ es)).depth j = (stg F b ds).depth j := by
  rw [depth_eq, depth_eq]
  by_cases h1 : j < b
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, treeShT_append, if_pos (by omega)]

theorem depth_snd (hL : ListedAt F b ds) (j : ℕ) :
    (stg F b (ds ++ es)).depth j = (stg F (b + nTrees ds) es).depth j := by
  rw [depth_eq, depth_eq]
  by_cases h1 : j < b
  · rw [if_pos h1, if_pos (by omega)]
  · by_cases h2 : j < b + nTrees ds
    · rw [if_neg h1, if_pos h2, treeShT_append, if_pos (by omega)]
      obtain ⟨sh, hsh⟩ := treeShT_some_of_lt ds (j - b) (by omega)
      have t := hL (j - b) sh hsh
      have e : b + (j - b) = j := by omega
      rw [e] at t
      rw [hsh, t]
      rfl
    · rw [if_neg h1, if_neg h2, treeShT_append, if_neg (by omega), Nat.sub_sub]

variable {ds es}

/-- The wants of a joined transcript. -/
theorem sWants_join (hL : ListedAt F b ds) (hO : OpensBelow b ds) (π : Iop.Tr (uLT C ds))
    (σ : Iop.Tr (uLT C es)) :
    sWants C (stg F b (ds ++ es)) (rhoT C (ds ++ es) (joinR C ds es π σ)) =
      sWants C (stg F b ds) (rhoT C ds π) ++ sWants C (stg F (b + nTrees ds) es) (rhoT C es σ) := by
  show wantsOf F.a (stg F b (ds ++ es)).depth (ds ++ es)
      (drawnT C (ds ++ es) (rhoT C (ds ++ es) (joinR C ds es π σ))) =
    wantsOf F.a (stg F b ds).depth ds (drawnT C ds (rhoT C ds π)) ++
      wantsOf F.a (stg F (b + nTrees ds) es).depth es (drawnT C es (rhoT C es σ))
  rw [drawnT_join, wantsOf_append _ _ _ _ _ _ (drawnT_length C ds _),
    wantsOf_congr F.a (stg F b (ds ++ es)).depth (stg F b ds).depth ds _
      (fun d hd j hj => depth_fst F b ds es j (hO d hd j hj)),
    wantsOf_congr F.a (stg F b (ds ++ es)).depth (stg F (b + nTrees ds) es).depth es _
      (fun _ _ j _ => depth_snd F b ds es hL j)]

/-- What a stage leaves at the entry that `posL` finds for (j, x) is its column of tree j at x. -/
theorem sLeft_at (xs : List RDT) (c : ℕ) (y : F.E.Str) (τ : Iop.Tr (uLT C xs)) (j x : ℕ)
    (p : PosL F.all) (hp : posL F.all j x = some p) :
    sLeft C (stg F c xs) y τ p = (sCol C (stg F c xs) y τ (.tree j x)).getD [] := by
  obtain ⟨h1, h2⟩ := posL_spec _ _ _ _ hp
  show (sCol C (stg F c xs) y τ (.tree (F.all.get p.1).no p.2.val)).getD [] = _
  rw [h1, h2]

theorem sCol_eq (xs : List RDT) (c : ℕ) (y : F.E.Str) (τ : Iop.Tr (uLT C xs)) (j x : ℕ) :
    sCol C (stg F c xs) y τ (.tree j x) =
      if j < c then (posL F.all j x).map y.2 else colAtST C xs τ (j - c) x := rfl

/-- A column that the first stretch's draws ask for. -/
theorem sCol_fst (y : F.E.Str) (π : Iop.Tr (uLT C ds)) (σ : Iop.Tr (uLT C es)) (j x : ℕ)
    (h : j < b + nTrees ds) :
    sCol C (stg F b (ds ++ es)) y (joinR C ds es π σ) (.tree j x) =
      sCol C (stg F b ds) y π (.tree j x) := by
  rw [sCol_eq, sCol_eq]
  by_cases h1 : j < b
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, colAtST_join, if_pos (by omega)]

/-- The second stretch's stage, at the oracles that the first leaves, has the joined stage's column,
up to the value where there is none. -/
theorem sCol_snd_getD (y : F.E.Str) (π : Iop.Tr (uLT C ds)) (σ : Iop.Tr (uLT C es)) (j x : ℕ)
    (hp : j < b + nTrees ds → ∃ p, posL F.all j x = some p) :
    (sCol C (stg F (b + nTrees ds) es) (y.1, sLeft C (stg F b ds) y π) σ (.tree j x)).getD [] =
      (sCol C (stg F b (ds ++ es)) y (joinR C ds es π σ) (.tree j x)).getD [] := by
  by_cases h2 : j < b + nTrees ds
  · obtain ⟨p, hp⟩ := hp h2
    rw [sCol_fst C F b y π σ j x h2, sCol_eq, if_pos h2, hp]
    exact sLeft_at C F ds b y π j x p hp
  · rw [sCol_eq, sCol_eq, if_neg h2, if_neg (by omega), colAtST_join, if_neg (by omega),
      Nat.sub_sub]

/-- A column that the second stretch's draws ask for. -/
theorem sCol_snd (hL : ListedAt F b ds) (y : F.E.Str) (π : Iop.Tr (uLT C ds))
    (σ : Iop.Tr (uLT C es)) (j x d : ℕ) (hd : (stg F b (ds ++ es)).depth j = some d)
    (hx : x < 2 ^ d) :
    sCol C (stg F b (ds ++ es)) y (joinR C ds es π σ) (.tree j x) =
      sCol C (stg F (b + nTrees ds) es) (y.1, sLeft C (stg F b ds) y π) σ (.tree j x) := by
  by_cases h2 : j < b + nTrees ds
  · have hd2 : (F.all.find? (·.no == j)).map (·.a) = some d := by
      have t := depth_snd F b ds es hL j
      rw [hd, depth_eq, if_pos h2] at t
      exact t.symm
    obtain ⟨p, hp⟩ := posL_of_find F.all j x d hd2 hx
    have hs : ∃ c, sCol C (stg F b ds) y π (.tree j x) = some c := by
      rw [sCol_eq]
      by_cases h1 : j < b
      · rw [if_pos h1, hp]
        exact ⟨_, rfl⟩
      · rw [if_neg h1]
        have t := depth_fst F b ds es j h2
        rw [hd, depth_eq, if_neg h1] at t
        exact colAtST_isSome C ds π (j - b) x d t.symm hx
    obtain ⟨c, hc⟩ := hs
    rw [sCol_fst C F b y π σ j x h2, hc, sCol_eq, if_pos h2, hp]
    show some c = some (sLeft C (stg F b ds) y π p)
    rw [sLeft_at C F ds b y π j x p hp, hc]
    rfl
  · rw [sCol_eq, sCol_eq, if_neg h2, if_neg (by omega), colAtST_join, if_neg (by omega),
      Nat.sub_sub]

/-- The view's rounds. -/
theorem sView_rounds_join (y y' : F.E.Str) (π : Iop.Tr (uLT C ds)) (σ : Iop.Tr (uLT C es)) :
    (sView C (stg F b (ds ++ es)) y (joinR C ds es π σ)).rounds =
      (sView C (stg F b ds) y π).rounds ++ (sView C (stg F (b + nTrees ds) es) y' σ).rounds :=
  rvT_join C ds es π σ

/-- The view's opened columns. -/
theorem sView_opened_join (hL : ListedAt F b ds) (hO : OpensBelow b ds) (y : F.E.Str)
    (π : Iop.Tr (uLT C ds)) (σ : Iop.Tr (uLT C es)) :
    (sView C (stg F b (ds ++ es)) y (joinR C ds es π σ)).opened =
      (sView C (stg F b ds) y π).opened ++
        (sView C (stg F (b + nTrees ds) es) (y.1, sLeft C (stg F b ds) y π) σ).opened := by
  unfold sView
  simp only
  rw [sWants_join C F b hL hO π σ, List.filterMap_append]
  congr 1
  · refine List.filterMap_congr fun w hw => ?_
    cases w with
    | table item x => rfl
    | tree j x =>
      obtain ⟨⟨d, hd, hj⟩, _⟩ := mem_wantsOf_tree _ _ j x _ _ hw
      rw [sCol_fst C F b y π σ j x (hO d hd j hj)]
  · refine List.filterMap_congr fun w hw => ?_
    cases w with
    | table item x => rfl
    | tree j x =>
      obtain ⟨_, d, hd, hx⟩ := mem_wantsOf_tree _ _ j x _ _ hw
      rw [sCol_snd C F b hL y π σ j x d ((depth_snd F b ds es hL j).trans hd) hx]

theorem and6 (a b c d e f : Bool) :
    ((a && b) && (c && d) && (e && f)) = ((a && c && e) && (b && d && f)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

/-- The tests in front of the run. -/
theorem sTests_join (hL : ListedAt F b ds) (hO : OpensBelow b ds) (y : F.E.Str)
    (π : Iop.Tr (uLT C ds)) (σ : Iop.Tr (uLT C es)) :
    sTests C (stg F b (ds ++ es)) y (joinR C ds es π σ) =
      (sTests C (stg F b ds) y π &&
        sTests C (stg F (b + nTrees ds) es) (y.1, sLeft C (stg F b ds) y π) σ) := by
  unfold sTests
  rw [sWants_join C F b hL hO π σ]
  show (passT C (ds ++ es) (rhoT C (ds ++ es) (joinR C ds es π σ)) &&
      fullOf (ds ++ es) (drawnT C (ds ++ es) (rhoT C (ds ++ es) (joinR C ds es π σ))) &&
      (sWants C (stg F b ds) (rhoT C ds π) ++
        sWants C (stg F (b + nTrees ds) es) (rhoT C es σ)).all _) = _
  rw [passT_join, drawnT_join, fullOf_append _ _ _ _ (drawnT_length C ds _), List.all_append, and6]
  rfl

/-- The trees left. -/
theorem sLeft_join (y : F.E.Str) (π : Iop.Tr (uLT C ds)) (σ : Iop.Tr (uLT C es)) :
    sLeft C (stg F b (ds ++ es)) y (joinR C ds es π σ) =
      sLeft C (stg F (b + nTrees ds) es) (y.1, sLeft C (stg F b ds) y π) σ := by
  funext p
  exact (sCol_snd_getD C F b y π σ (F.all.get p.1).no p.2.val fun _ =>
    posL_isSome F.all _ _ (F.all.get p.1) (List.get_mem _ _) rfl p.2.isLt).symm

/-- **A stage over two stretches is the stage over the first, then the stage over the second.** -/
theorem stage_cut {S : Type} (hL : ListedAt F b ds) (hO : OpensBelow b ds)
    (r₁ r₂ r : S → Fmt.View → Option S) (s : S) (y : F.E.Str) (π : Iop.Tr (uLT C ds))
    (σ : Iop.Tr (uLT C es))
    (hr : r s (sView C (stg F b (ds ++ es)) y (joinR C ds es π σ)) =
      (r₁ s (sView C (stg F b ds) y π)).bind fun s' =>
        r₂ s' (sView C (stg F (b + nTrees ds) es) (y.1, sLeft C (stg F b ds) y π) σ)) :
    (stageIOR C (stg F b (ds ++ es)) r).red.out (s, y) (joinR C ds es π σ) =
      ((stageIOR C (stg F b ds) r₁).red.out (s, y) π).bind fun a =>
        (stageIOR C (stg F (b + nTrees ds) es) r₂).red.out a σ := by
  show ((if sTests C (stg F b (ds ++ es)) y (joinR C ds es π σ) then
        r s (sView C (stg F b (ds ++ es)) y (joinR C ds es π σ)) else none).map fun s' =>
      (s', ((y.1, sLeft C (stg F b (ds ++ es)) y (joinR C ds es π σ)) : F.E.Str))) =
    (((if sTests C (stg F b ds) y π then r₁ s (sView C (stg F b ds) y π) else none).map fun s' =>
      (s', ((y.1, sLeft C (stg F b ds) y π) : F.E.Str))).bind fun a =>
        (if sTests C (stg F (b + nTrees ds) es) a.2 σ then
          r₂ a.1 (sView C (stg F (b + nTrees ds) es) a.2 σ) else none).map fun s' =>
        (s', ((a.2.1, sLeft C (stg F (b + nTrees ds) es) a.2 σ) : F.E.Str)))
  rw [sTests_join C F b hL hO y π σ, sLeft_join C F b y π σ, hr]
  cases h1 : sTests C (stg F b ds) y π with
  | false => simp
  | true =>
    cases h3 : r₁ s (sView C (stg F b ds) y π) with
    | none => simp
    | some s' =>
      cases h2 : sTests C (stg F (b + nTrees ds) es) (y.1, sLeft C (stg F b ds) y π) σ <;> simp [h2]

end VerifiableInference.Desc.Sound
