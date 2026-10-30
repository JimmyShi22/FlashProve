-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TreesMade.lean: which written rounds of a proximity test send a tree: the first
round of each code switch; the first fold's first round where that fold sends its own mask; no other
round of a fold or a switch.

In a game a word is fixed before a draw by the round in whose message it stands. The library's chain
reads stage j's words off the first message of switch j - 1. That the tree which stage j's declared
opening names is that message's is asked, by whoever spends the law in a game, as `Chain.Trees`
(OnBytes/Slice/ManyShows.lean) with "the chain's own tree number free + n is the stretch's n-th".
Here Chain.Trees is a theorem of the block's own test on the plan. Definitions, statements and
proofs.
Main names:
  `WShape pre rest a l`: the written rounds l of the stages a :: rest, cut as the chain cuts them:
    at a stage but the last: dE, k times dT, dS, dC; dE sends pre (a tree or none), dT and dC none,
    dS one; 1 ≤ k and h ≤ k; and so on, with none for pre; at the last stage two rounds, of whose
    trees nothing is said (Chain.Trees asks nothing of a base case).
  `lay_some`, `shape_step`, `stage_k`, `shape_later`: the walk, over MadeRounds.lean and
    TieOkMade.lean; `stage_k`: what sizesOk's walk holds of a stage but the last.
  `drop_rep`, `none_isSome`, `chain_step`: tools; `chain_step`: chainFrom unfolded once at a stage
    with WShape.
  `shape_made`: at a place whose numbers give rounds, with sizesOk's clauses on the stages: WShape
    of the written rounds behind "BAT", with the own mask's shape as told for pre.
  `trees_of_shape`: WShape none gives Chain.Trees of the place's chain (`chainFrom`, ChainOf.lean),
    at any letters. `treesOwn_of_shape`: WShape (some _) gives the like with "the first fold's first
    round sends a tree". Both go after `trees_of_walk` (Johnson/Desc/K12/Coin/Bools.lean),
    which goes from a test with code to Chain.Trees by the same unfolding of
    chainFrom.
  `TreesOwnP`: the text of `TreesOwn` (Johnson/Desc/K12/Coin/OwnTrees.lean),
    typed here by hand: that constant is not beneath this file.
Limits: nothing is said of a view, a record or a transcript. No soundness is claimed, and nothing is
said on hiding.
-/
import Johnson.Desc.K12.Law.TieOkMade
import Johnson.Desc.K12.Law.ChainOf
import OnBytes.Slice.ManyShows

set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (rEps rTwo rSeed rCs rLambda rBase laterRounds wMid)
open H2K.First
open H2K.Pub (WR writtenOf layW chainFrom Letters sgOf stepEndX stepMidX)

/-- Which written rounds send a tree, cut as the chain cuts them. -/
def WShape : Option Fmt.Shape → List Fmt.M1.Stage → Fmt.M1.Stage → List WR → Prop
  | _, [], _, l => ∃ dL dB, l = [dL, dB]
  | pre, b :: rest, a, l => ∃ dE dT dS dC l',
      l = (dE :: List.replicate a.k dT) ++ (dS :: dC :: l') ∧ dE.tree = pre ∧ dT.tree = none ∧
      dS.tree.isSome = true ∧ dC.tree = none ∧ 1 ≤ a.k ∧ a.h ≤ a.k ∧ WShape none rest b l'

/-- A stage is laid only where a list of trees is left to it. -/
theorem lay_some (own : Bool) (work tree W : Nat) (nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ls : List (List Op)) (R' : List Fmt.DeclaredRound)
    (h' : H2U.layOpens own true (laterRounds work tree W nxt rest) ls = some R') :
    ∃ x t, ls = x :: t := by
  cases rest with
  | nil =>
    obtain ⟨x, rfl, _, _⟩ := lay_base own work tree W nxt ls R' h'
    exact ⟨x, [], rfl⟩
  | cons n2 rest =>
    obtain ⟨x, t, _, rfl, _, _, _⟩ := lay_stage own true work tree W nxt n2 rest ls R' h'
    exact ⟨x, t, rfl⟩

/-- One stage but the last. -/
theorem shape_step (p : P12) (own seen : Bool) (work tree W : Nat) (cur nxt : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (R : List Fmt.DeclaredRound) (x : List Op) (m : Nat)
    (pre : List Fmt.Shape)
    (hpre : ((own && !seen) = true ∧ ∃ s0, pre = [s0]) ∨ ((own && !seen) = false ∧ pre = []))
    (h : H2U.layOpens own seen (laterRounds work tree W cur (nxt :: rest))
      (x :: ((told p.nums).drop m).map ([·])) = some R)
    (w : List WR) (hw : layW R (pre ++ ((told p.nums).drop m).map (·.1)) = some w)
    (hk1 : 1 ≤ cur.k) (hk : cur.h ≤ cur.k)
    (IH : ∀ R' x' w', H2U.layOpens own true (laterRounds work (tree + 1) (wMid nxt) nxt rest)
        (x' :: ((told p.nums).drop (m + 1)).map ([·])) = some R' →
      layW R' (((told p.nums).drop (m + 1)).map (·.1)) = some w' → WShape none rest nxt w') :
    WShape pre.head? (nxt :: rest) cur w := by
  obtain ⟨x1, t, R', hx, _, h', rfl⟩ := lay_stage own seen work tree W cur nxt rest _ R h
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨x', t', hx'⟩ := lay_some own work _ _ nxt rest _ R' h'
  obtain ⟨a, W', hd⟩ := told_cons _ _ _ _ hx'
  rw [hd, List.map_cons] at h'
  rw [hd, List.map_cons, layW_stage own seen work tree W cur nxt x R' pre _ _ hpre] at hw
  obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.1 hw
  exact ⟨_, _, _, _, w', rfl, rfl, rfl, rfl, rfl, hk1, hk, IH R' _ w' h' hw'⟩

/-- What sizesOk's walk holds of a stage but the last. -/
theorem stage_k (answers : Nat) (b : Option Fmt.M1.Stage) (cur nxt : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (h : stagesOk answers b (cur :: nxt :: rest) = true) :
    1 ≤ cur.k ∧ cur.h ≤ cur.k ∧ stagesOk answers (some cur) (nxt :: rest) = true := by
  unfold stagesOk at h
  simp only [Bool.and_eq_true] at h
  have h1 := h.1.1
  unfold stageOk at h1
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, Bool.and_eq_true,
    decide_eq_true_eq] at h1
  exact ⟨h1.2.1, h1.1.2, h.2⟩

/-- The walk from a stage behind the first "FOLD epsilon" on. -/
theorem shape_later (p : P12) (own : Bool) (work answers : Nat) : ∀ (rest : List Fmt.M1.Stage)
    (cur : Fmt.M1.Stage) (b : Option Fmt.M1.Stage) (tree W : Nat) (R : List Fmt.DeclaredRound)
    (x : List Op) (m : Nat) (w : List WR),
    stagesOk answers b (cur :: rest) = true →
    H2U.layOpens own true (laterRounds work tree W cur rest)
      (x :: ((told p.nums).drop m).map ([·])) = some R →
    layW R (((told p.nums).drop m).map (·.1)) = some w → WShape none rest cur w
  | [], cur, b, tree, W, R, x, m, w, _, h, hw => by
    obtain ⟨x', hx, _, rfl⟩ := lay_base own work tree W cur _ R h
    have hn : (told p.nums).drop m = [] := by
      have := (List.cons.inj hx).2
      simpa using this
    rw [hn, List.map_nil, layW_base] at hw
    exact ⟨_, _, (Option.some.inj hw).symm⟩
  | nxt :: rest, cur, b, tree, W, R, x, m, w, hS, h, hw => by
    obtain ⟨k1, k2, hS'⟩ := stage_k answers b cur nxt rest hS
    exact shape_step p own true work tree W cur nxt rest R x m [] (Or.inr ⟨by simp, rfl⟩) h w
      (by simpa using hw) k1 k2 (fun R' x' w' hR' hw' =>
        shape_later p own work answers rest nxt _ _ _ R' x' (m + 1) w' hS' hR' hw')

/-- **The written rounds behind "BAT": which of them send a tree.** -/
theorem shape_made (p : P12) (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds)
    (answers : Nat) (hS : stagesOk answers none p.nums.stages = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest) (w0 : WR) (w : List WR)
    (hw : writtenOf p.nums = some (w0 :: w)) :
    WShape ((ownTold p.nums).map (·.1)).head? rest a w := by
  obtain ⟨s, next, rest', R, hs', hR, rfl⟩ := rounds_top p.nums rds hr
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hs')
  rw [hs] at hS
  obtain ⟨k1, k2, hS'⟩ := stage_k answers none a next rest' hS
  unfold writtenOf at hw
  rw [hr, Option.bind_some, told_shapes, layW_quiet _ _ _ .elems kBat rfl] at hw
  obtain ⟨w1, hw1, e⟩ := Option.map_eq_some_iff.1 hw
  obtain rfl := (List.cons.inj e).2
  cases ho : p.nums.ownMask
  · rw [ho] at hR
    have := shape_step p false false p.nums.work 0 0 a next rest' R _ 0 [] (Or.inr ⟨rfl, rfl⟩)
      (by simpa using hR) w1 (by simpa using hw1) k1 k2 (fun R' x' w' hR' hw' =>
        shape_later p false p.nums.work answers rest' next _ _ _ R' x' 1 w' hS' hR' hw')
    simpa [ownTold, ho] using this
  · rw [ho] at hR
    cases ht : told p.nums with
    | nil =>
      exfalso
      obtain ⟨_, t, R', hx, _, h', _⟩ := lay_stage _ _ _ _ _ _ _ _ _ R hR
      obtain ⟨_, _, hx'⟩ := lay_some _ _ _ _ _ _ _ R' h'
      rw [← (List.cons.inj hx).2, ht] at hx'
      simp at hx'
    | cons y ys =>
      have := shape_step p true false p.nums.work 0 0 a next rest' R _ 1 [y.1]
        (Or.inl ⟨rfl, y.1, rfl⟩) (by simpa using hR) w1 (by rw [ht] at hw1 ⊢; simpa using hw1)
        k1 k2 (fun R' x' w' hR' hw' =>
          shape_later p true p.nums.work answers rest' next _ _ _ R' x' 2 w' hS' hR' hw')
      simpa [ownTold, ho, ht] using this

theorem drop_rep {α : Type} (x : α) (k : Nat) (l : List α) :
    (List.replicate k x ++ l).drop k = l := List.drop_left' (by simp)

/-- The frame's cut of one stage of a chain, off WShape. -/
theorem chain_step (X : Letters) (pre : Option Fmt.Shape) (b : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage) (l : List WR)
    (c : OnBytes.Slice.Chain (sgOf a)) (hW : WShape pre (b :: rest) a l)
    (hc : chainFrom X (b :: rest) a l = some c) :
    ∃ (dE dT dS dC : WR) (l' : List WR) (hf : OnBytes.Slice.CsFit (sgOf a) (sgOf b))
      (next : OnBytes.Slice.Chain (sgOf b)),
      dE.tree = pre ∧ dT.tree = none ∧ dS.tree.isSome = true ∧ dC.tree = none ∧
      WShape none rest b l' ∧ chainFrom X rest b l' = some next ∧
      (c = stepEndX X a b hf dE dT dS dC next ∨ c = stepMidX X a b hf dE dT dS dC next) := by
  obtain ⟨dE, dT, dS, dC, l', rfl, e1, e2, e3, e4, k1, k2, hW'⟩ := hW
  obtain ⟨n, hn⟩ : ∃ n, a.k = n + 1 := ⟨a.k - 1, by omega⟩
  have hkk : H2K.Pub.kk a = n + 1 := by unfold H2K.Pub.kk; omega
  rw [hn, List.replicate_succ] at hc
  unfold chainFrom at hc
  simp only [List.cons_append] at hc
  split at hc
  · rename_i hcond
    split at hc
    · rename_i dS' dC' l'' hd
      have hd' : (dT :: (List.replicate n dT ++ dS :: dC :: l')).drop (H2K.Pub.kk a) =
          dS :: dC :: l' := by
        rw [hkk, ← List.cons_append, ← List.replicate_succ]
        exact drop_rep dT (n + 1) _
      rw [hd'] at hd
      obtain ⟨rfl, h2⟩ := List.cons.inj hd
      obtain ⟨rfl, rfl⟩ := List.cons.inj h2
      obtain ⟨next, hnx, rfl⟩ := Option.map_eq_some_iff.1 hc
      refine ⟨dE, dT, dS, dC, l', H2K.Pub.csFit_of_B hcond.1, next, e1, e2, e3, e4, hW', hnx, ?_⟩
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · cases hc
  · cases hc

theorem none_isSome {α : Type} {x : Option α} (h : x = none) : x.isSome = false := by
  rw [h]
  rfl

/-- **Chain.Trees of the place's chain**, off WShape. -/
theorem trees_of_shape (X : Letters) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage)
    (l : List WR) (c : OnBytes.Slice.Chain (sgOf a)), WShape none rest a l →
    chainFrom X rest a l = some c → c.Trees
  | [], a, l, c, _, hc => by
    unfold chainFrom at hc
    split at hc
    · cases hc
      trivial
    · cases hc
  | b :: rest, a, l, c, hW, hc => by
    obtain ⟨dE, dT, dS, dC, l', hf, next, e1, e2, e3, e4, hW', hnx, hcc⟩ :=
      chain_step X none b rest a l c hW hc
    have ih := trees_of_shape X rest b l' next hW' hnx
    rcases hcc with rfl | rfl
    · exact ⟨none_isSome e1, none_isSome e2, e3, none_isSome e4, ih⟩
    · exact ⟨none_isSome e1, none_isSome e2, e3, none_isSome e4, ih⟩

/-- The first fold's first round sends a tree; else as Chain.Trees. (The text of
TreesOwn, typed by hand.) -/
def TreesOwnP : {s : OnBytes.Slice.Sg} → OnBytes.Slice.Chain s → Prop
  | _, .last _ _ _ _ _ _ _ => False
  | _, .step _ _ _ _ _ dE dT dS dC _ _ _ _ _ next =>
    dE.tree.isSome = true ∧ dT.tree.isSome = false ∧ dS.tree.isSome = true ∧
      dC.tree.isSome = false ∧ next.Trees

/-- **The like where the first fold sends its own mask.** -/
theorem treesOwn_of_shape (X : Letters) (s0 : Fmt.Shape) (b : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage) (l : List WR)
    (c : OnBytes.Slice.Chain (sgOf a)) (hW : WShape (some s0) (b :: rest) a l)
    (hc : chainFrom X (b :: rest) a l = some c) : TreesOwnP c := by
  obtain ⟨dE, dT, dS, dC, l', hf, next, e1, e2, e3, e4, hW', hnx, hcc⟩ :=
    chain_step X (some s0) b rest a l c hW hc
  have ih := trees_of_shape X rest b l' next hW' hnx
  have e1' : dE.tree.isSome = true := by rw [e1]; rfl
  rcases hcc with rfl | rfl
  · exact ⟨e1', none_isSome e2, e3, none_isSome e4, ih⟩
  · exact ⟨e1', none_isSome e2, e3, none_isSome e4, ih⟩

end H2K.Made

#print axioms H2K.Made.shape_made
#print axioms H2K.Made.trees_of_shape
#print axioms H2K.Made.treesOwn_of_shape
