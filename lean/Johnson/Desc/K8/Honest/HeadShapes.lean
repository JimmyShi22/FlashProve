-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/HeadShapes.lean: THE SMALLNESS TEST AT THE OUTPUT HEAD: THE LIST OF TABLES
THAT THE QUIET STEP MAKES AND CLOSES THERE HAS THE PLACE's SHAPES. In two halves, and joined. Lemmas
on the verifier's own text; no prover, no message, no coin in them; none of the library's goals.

The kind's text holds the closed list against `tabs p` (Johnson/Desc/First/K8/Hear.lean): the shapes
(matrix, rows to an entry, first entry) that the place's families of tables make at the place's rows
and columns. The library has a closed public term for the head's tables: `Closed.headShapes h mats`
(OnBytes/Tie/Pv/Tail/ShapesHead.lean).

  `asks_head`   the families: `Asks.head h` (Johnson/Desc/First/K8/Asks.lean) is `Closed.headAsks h`
  `layFamily_parts`, `tabs_asks`   one family's tables, and all families', laid by the kind's text,
                   are the library's `partShapes`, `asksShapes`, at the same rows and columns
  **`tabs_headShapes`**   THE PLACE's SHAPES ARE THE PUBLIC TERM: at a place whose families are
                   `Asks.head h` and whose columns and rows are those of mats: tabs p =
                   (Closed.headShapes h mats).map ofTab
  **`tables_shapes`**   WHAT THE TEXT MAKES: every success of `ReadsQuiet.tables h L hp cov x`
                   (Johnson/Desc/K8/ReadsQuiet.lean) lays tables of the shapes `Closed.headShapes h
                   hp.tl.mats`: no premise but the success
  **`head_tabs`**   JOINED, IN THE FORM IN WHICH THE LAW OF THE DRAW ASKS IT: behind a yes of the
                   quiet step at the head (`ReadsQuiet.head P`), at a place with the three facts:
                   the list that the state bears has the shapes `tabs p`
  `head_tabs_lists`   the same at the two equations of lists in which the law of the draw has the
                   place's columns and rows (`getD_mats`)
  **`head_tabs_under`**   AND OF A MEMBER AS A CHAIN HAS IT: any block a yes of which is the same
                   yes of the quiet step joined behind another block
Limits. The three facts on the place's numbers (its families are the head's; its columns and rows
are those of the plan's matrices) are premises: how a place's numbers are made of the public
parameters is the seat's. ALL LAWS BUT THE FIRST HALF's HANG ON A YES THAT IS EVALUATED NOWHERE
HERE. That a description's member is under the joined step is a premise (`Block.Under`): it is shown
of no member here. Nothing on the tables' weights.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.First.K8.LawShapes
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.K8.ReadsQuietAt
import Johnson.Desc.Sound.HearsOnce
import OnBytes.Tie.Pv.Tail.ShapesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail Cb.Pv.Tail
open OnBytes.Tie.Pv.Tail.Closed (partShapes asksShapes headAsks headShapes foldAsks shapesOf)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par tabs layFamily ofTab)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables ReadsQuiet.head ReadsQuiet.PH
  ReadsQuiet.head_ok ReadsQuiet.closed_ok ReadsQuiet.bind_ok ReadsQuiet.named_ok)

/-- **The families.** -/
theorem asks_head (h : Head.Shape) : Asks.head h = headAsks h := by
  simp [Asks.head, headAsks, List.replicate, Nat.add_assoc]

/-- One family's parts, laid one behind the other. -/
theorem layParts_parts (p : Par) (mats : Array TMat)
    (hk : ∀ M, p.ks.getD M 0 = (mats.getD M {}).k) (hm : ∀ M, p.ms.getD M 0 = (mats.getD M {}).m)
    (M0 Lf : Nat) :
    ∀ (qs : List Nat) (acc : List (Nat × Nat × Nat)) (e : Nat),
      qs.foldl (fun (x : List (Nat × Nat × Nat) × Nat) q => (x.1 ++ [(M0 + q, Lf, x.2)],
          x.2 + p.ks.getD (M0 + q) 0 * (p.ms.getD (M0 + q) 0 / Lf))) (acc, e) =
        (acc ++ (partShapes mats M0 Lf qs e).1.map ofTab, (partShapes mats M0 Lf qs e).2)
  | [], acc, e => by simp [partShapes]
  | q :: qs, acc, e => by
    rw [List.foldl_cons, layParts_parts p mats hk hm M0 Lf qs, hk, hm]
    simp [partShapes, ofTab, List.append_assoc]

/-- One family's tables. -/
theorem layFamily_parts (p : Par) (mats : Array TMat)
    (hk : ∀ M, p.ks.getD M 0 = (mats.getD M {}).k) (hm : ∀ M, p.ms.getD M 0 = (mats.getD M {}).m)
    (a : Nat × Nat × Nat) (e : Nat) :
    layFamily p a e = ((partShapes mats a.1 a.2.2 (List.range a.2.1) e).1.map ofTab,
      (partShapes mats a.1 a.2.2 (List.range a.2.1) e).2) := by
  unfold layFamily
  rw [layParts_parts p mats hk hm]
  rfl

/-- All families' tables. -/
theorem tabs_asks (p : Par) (mats : Array TMat)
    (hk : ∀ M, p.ks.getD M 0 = (mats.getD M {}).k) (hm : ∀ M, p.ms.getD M 0 = (mats.getD M {}).m) :
    ∀ (asks : List (Nat × Nat × Nat)) (acc : List (Nat × Nat × Nat)) (e : Nat),
      (asks.foldl (fun (x : List (Nat × Nat × Nat) × Nat) a =>
          let y := layFamily p a x.2; (x.1 ++ y.1, y.2)) (acc, e)).1 =
        acc ++ (asksShapes mats asks e).map ofTab
  | [], acc, e => by simp [asksShapes]
  | a :: asks, acc, e => by
    rw [List.foldl_cons]
    dsimp only
    rw [layFamily_parts p mats hk hm a e, tabs_asks p mats hk hm asks]
    simp [asksShapes, List.append_assoc]

/-- **The place's shapes are the library's public term.** -/
theorem tabs_headShapes (p : Par) (h : Head.Shape) (mats : Array TMat)
    (ha : p.asks = Asks.head h) (hk : ∀ M, p.ks.getD M 0 = (mats.getD M {}).k)
    (hm : ∀ M, p.ms.getD M 0 = (mats.getD M {}).m) :
    tabs p = (headShapes h mats).map ofTab := by
  unfold tabs headShapes
  rw [ha, asks_head, tabs_asks p mats hk hm]
  rfl

/-- **Every success of the text's tables lays the term's shapes.** -/
theorem tables_shapes {h : Head.Shape} {L : Head.HL} {hp : Head.HPlanH2} {cov : Head.Covered}
    {x : Head.Heard} {t : Head.Tables} (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    shapesOf t.funs = headShapes h hp.tl.mats := by
  unfold ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨t', ht, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  simp only [pure, Except.pure, Except.ok.injEq] at e
  subst e
  exact (foldAsks _ _ _ _ (ReadsQuiet.named_ok ht)).1

/-- **Behind a yes of the quiet step at the head the closed list has the place's shapes.** -/
theorem head_tabs (P : ReadsQuiet.PH) (p : Par) (ha : p.asks = Asks.head P.h)
    (hk : ∀ M, p.ks.getD M 0 = (P.hp.tl.mats.getD M {}).k)
    (hm : ∀ M, p.ms.getD M 0 = (P.hp.tl.mats.getD M {}).m) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (ReadsQuiet.head P).decide s rs gs = .ok s') :
    ∀ tl, s'.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p := by
  obtain ⟨a, cov, x, t, tl', _, ho, _, _, ht, hc, rfl⟩ := ReadsQuiet.head_ok h
  obtain ⟨_, rfl, _, _⟩ := ReadsQuiet.closed_ok hc
  intro tl htl
  have e : (some { P.hp.tl with funClosed := true, funs := t.funs } : Option HTailF2) =
      some tl := by
    rw [← htl]
    simp [S.tl?, ho]
  obtain rfl := Option.some.inj e
  rw [tabs_headShapes p P.h P.hp.tl.mats ha hk hm, ← tables_shapes ht]
  unfold shapesOf
  rw [List.map_map]
  rfl

/-- A list of the matrices' numbers, read at a number M, against the array read there. f: a field
that is 0 at the matrix without numbers. -/
theorem getD_mats (mats : Array TMat) (f : TMat → Nat) (h0 : f {} = 0) (M : Nat) :
    (mats.toList.map f).getD M 0 = f (mats.getD M {}) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases mats[M]? with
  | none => exact h0.symm
  | some _ => rfl

/-- **The same at the two equations of lists** in which the law of the draw has the place's columns
and rows. -/
theorem head_tabs_lists (P : ReadsQuiet.PH) (p : Par) (ha : p.asks = Asks.head P.h)
    (hk : P.hp.tl.mats.toList.map (·.k) = p.ks) (hm : P.hp.tl.mats.toList.map (·.m) = p.ms)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (ReadsQuiet.head P).decide s rs gs = .ok s') :
    ∀ tl, s'.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p :=
  head_tabs P p ha (fun M => by rw [← hk]; exact getD_mats _ (·.k) rfl M)
    (fun M => by rw [← hm]; exact getD_mats _ (·.m) rfl M) h

/-- **And of a member as a chain has it**: any block c a yes of which is the same yes of the quiet
step joined behind a block own (`Block.Under`, Johnson/Desc/Sound/HearsOnce.lean; `behind`,
Johnson/Desc/K8/ReadsQuietAt.lean). -/
theorem head_tabs_under {Cl : Type} (P : ReadsQuiet.PH) (p : Par) (ha : p.asks = Asks.head P.h)
    (hk : P.hp.tl.mats.toList.map (·.k) = p.ks) (hm : P.hp.tl.mats.toList.map (·.m) = p.ms)
    (own : Block S Unit) (c : Block S Cl)
    (u : c.Under (VerifiableInference.Desc.K8.ReadsQuiet.behind own (ReadsQuiet.head P)))
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : c.decide s rs gs = .ok s') :
    ∀ tl, s'.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p := by
  have H : (own.decide s (rs.take own.rounds.length) (gs.take own.openings)).bind (fun t =>
      (ReadsQuiet.head P).decide t (rs.drop own.rounds.length) (gs.drop own.openings)) = .ok s' :=
    u s rs gs s' h
  obtain ⟨t, _, H⟩ := ReadsQuiet.bind_ok H
  exact head_tabs_lists P p ha hk hm H

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.getD_mats
#print axioms VerifiableInference.Desc.First.K8.Honest.head_tabs_lists
#print axioms VerifiableInference.Desc.First.K8.Honest.head_tabs_under
#print axioms VerifiableInference.Desc.First.K8.Honest.asks_head
#print axioms VerifiableInference.Desc.First.K8.Honest.layParts_parts
#print axioms VerifiableInference.Desc.First.K8.Honest.layFamily_parts
#print axioms VerifiableInference.Desc.First.K8.Honest.tabs_asks
#print axioms VerifiableInference.Desc.First.K8.Honest.tabs_headShapes
#print axioms VerifiableInference.Desc.First.K8.Honest.tables_shapes
#print axioms VerifiableInference.Desc.First.K8.Honest.head_tabs
