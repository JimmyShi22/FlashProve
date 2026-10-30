-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawShapes.lean: THE SMALLNESS TEST: AT A LAYERS' LINK THE SHAPES OF THE TABLES
THAT THE PLACE'S NUMBERS MAKE ARE THE LIBRARY'S OWN PUBLIC TERM.

The kind's text holds the closed list of tables against `tabs p` (Johnson/Desc/First/K8/Hear.lean):
the shapes that the place's families of tables (`Par.asks`) make at the place's rows and columns.
For a layers' link the families are `Asks.layers y rd g` (Johnson/Desc/First/K8/Asks.lean). The
library has a public term for the same thing: `Closed.layShapes P g`
(OnBytes/Tie/Pv/Tail/ShapesLay.lean), made by the verifier on bytes' own `Layer.tableAsks` and
`Layer.layTables` (OnBytes/Model/LayerForms.lean). Here the two are tied, so that they are no twins:
  `asks_layers`: the families: `Asks.layers y rd g` is `Layer.tableAsks y rd g`, family by family:
    first matrix, number of parts, rows to an entry.
  `goFam`, `layParts_eq`, `layFamily_eq`: one family's tables, laid part by part: the library's
    `layParts` and the text's `layFamily` are one plain recursion.
  `tabs_of_layTables`: where the library's `layTables` returns, the text's fold over the same
    families, at the same rows and columns, lays the same shapes.
  `tabs_layShapes`: **at a place whose families are `Asks.layers P.y P.rd g` and whose rows and
    columns are those of the group's matrices: `tabs p`, as tables, is `Closed.layShapes P g`**,
    where `layTables` returns.
Definitions, statements and proofs.
Limits. THE LAYERS' LINKS ALONE: for the attention links and the head the library has no such term.
One premise: `layTables` returns (it refuses an empty family; `layShapes` is then the empty list,
while `tabs p` lays on). Nothing on the weights. Nothing on soundness.

-/
import Johnson.Desc.First.K8.Hear
import Johnson.Desc.First.K8.Asks
import OnBytes.Tie.Pv.Tail.ShapesLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail Cb.Pv.Tail

/-- A family of the library's, as the place's numbers hold it. -/
def triOf (a : Layer.TableAsk) : Nat × Nat × Nat := (a.M0, a.parts, a.L)

/-- **The families.** -/
theorem asks_layers (y : Layer.Lay) (rd : Layer.Reads) (g : Nat) :
    (Layer.tableAsks y rd g).map triOf = Asks.layers y rd g := by
  unfold Layer.tableAsks Asks.layers Layer.matIx triOf
  by_cases hg : g = 0 <;> cases hp : y.h.p4 <;>
    simp [hg, List.map_append, List.map_map, Function.comp_def, List.map_const',
      List.replicate_succ, Nat.add_assoc]

/-- One family's tables, by a plain recursion: n parts from matrix M and entry e on; w M: how many
entries the table of matrix M has. -/
def goFam (w : Nat → Nat) : Nat → Nat → Nat → List (Nat × Nat) × Nat
  | 0, _, e => ([], e)
  | n + 1, M, e => ((M, e) :: (goFam w n (M + 1) (e + w M)).1, (goFam w n (M + 1) (e + w M)).2)

/-- The library's laying of a family's last n parts. -/
theorem layParts_eq (mats : Array (Nat × Nat)) (a : Layer.TableAsk) :
    ∀ (n e : Nat), n ≤ a.parts →
      Layer.layParts mats a n e =
        goFam (fun M => (mats.getD M (0, 0)).2 * ((mats.getD M (0, 0)).1 / a.L)) n
          (a.M0 + (a.parts - n)) e
  | 0, _, _ => rfl
  | n + 1, e, h => by
    have e1 : a.M0 + (a.parts - (n + 1)) + 1 = a.M0 + (a.parts - n) := by omega
    simp only [Layer.layParts, goFam]
    rw [layParts_eq mats a n _ (by omega), e1]

/-- The text's laying of a family. -/
theorem fold_from (w : Nat → Nat) (L M : Nat) :
    ∀ (n s : Nat) (pre : List (Nat × Nat × Nat)) (e : Nat),
      (List.range' s n).foldl
          (fun (x : List (Nat × Nat × Nat) × Nat) q => (x.1 ++ [(M + q, L, x.2)], x.2 + w (M + q)))
          (pre, e) =
        (pre ++ (goFam w n (M + s) e).1.map (fun y => (y.1, L, y.2)), (goFam w n (M + s) e).2)
  | 0, _, _, _ => by simp [goFam]
  | n + 1, s, pre, e => by
    rw [List.range'_succ, List.foldl_cons, fold_from w L M n (s + 1) _ _]
    show (pre ++ [(M + s, L, e)] ++ _, _) = _
    simp only [goFam, List.map_cons, List.append_assoc, List.singleton_append]
    rfl

theorem fold_eq (w : Nat → Nat) (L n M : Nat) (pre : List (Nat × Nat × Nat)) (e : Nat) :
    (List.range n).foldl
        (fun (x : List (Nat × Nat × Nat) × Nat) q => (x.1 ++ [(M + q, L, x.2)], x.2 + w (M + q)))
        (pre, e) =
      (pre ++ (goFam w n M e).1.map (fun y => (y.1, L, y.2)), (goFam w n M e).2) := by
  rw [List.range_eq_range']
  exact fold_from w L M n 0 pre e

theorem layFamily_eq (p : Par) (a : Nat × Nat × Nat) (e : Nat) :
    layFamily p a e =
      ((goFam (fun M => p.ks.getD M 0 * (p.ms.getD M 0 / a.2.2)) a.2.1 a.1 e).1.map
          (fun y => (y.1, a.2.2, y.2)),
        (goFam (fun M => p.ks.getD M 0 * (p.ms.getD M 0 / a.2.2)) a.2.1 a.1 e).2) := by
  unfold layFamily
  rw [fold_eq (fun M => p.ks.getD M 0 * (p.ms.getD M 0 / a.2.2)) a.2.2 a.2.1 a.1 [] e]
  rfl

/-- A table, as the place's numbers hold it. -/
def ofTab (t : Tab) : Nat × Nat × Nat := (t.mat, t.len, t.start)

/-- **Where the library's laying returns, the text's fold lays the same shapes.** -/
theorem tabs_of_layTables (p : Par) (mats : Array (Nat × Nat))
    (hk : ∀ M, p.ks.getD M 0 = (mats.getD M (0, 0)).2)
    (hm : ∀ M, p.ms.getD M 0 = (mats.getD M (0, 0)).1) :
    ∀ (as : List Layer.TableAsk) (pre : List (Nat × Nat × Nat)) (e : Nat)
      (x : List Layer.TableAt × List (Layer.TableAsk × List (Nat × Nat)) × Nat),
      Layer.layTables mats as e = some x →
      (as.map triOf).foldl (fun x a => let y := layFamily p a x.2; (x.1 ++ y.1, y.2)) (pre, e) =
        (pre ++ (Closed.laidShapes x.2.1).map ofTab, x.2.2)
  | [], pre, e, x, h => by
    simp only [Layer.layTables, Option.some.injEq] at h
    subst h
    simp [Closed.laidShapes]
  | a :: rest, pre, e, x, h => by
    simp only [Layer.layTables] at h
    split at h
    · exact absurd h (by simp)
    · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
      have hw : (fun M => p.ks.getD M 0 * (p.ms.getD M 0 / a.L)) =
          fun M => (mats.getD M (0, 0)).2 * ((mats.getD M (0, 0)).1 / a.L) := by
        funext M
        rw [hk, hm]
      have hP := layParts_eq mats a a.parts e (Nat.le_refl _)
      rw [Nat.sub_self, Nat.add_zero] at hP
      rw [hP] at hr
      simp only [List.map_cons, List.foldl_cons]
      rw [layFamily_eq p (triOf a) e]
      simp only [triOf]
      rw [hw, tabs_of_layTables p mats hk hm rest _ _ r hr, hP]
      simp [Closed.laidShapes, ofTab, List.map_map, Function.comp_def, List.append_assoc]

/-- **At a layers' link the place's shapes are the library's public term.** -/
theorem tabs_layShapes (p : Par) (P : Layer.Pub) (g : Nat)
    (ha : p.asks = Asks.layers P.y P.rd g)
    (hk : ∀ M, p.ks.getD M 0 = (((P.tails.getD g {}).mats.map fun M => (M.m, M.k)).getD M (0, 0)).2)
    (hm : ∀ M, p.ms.getD M 0 = (((P.tails.getD g {}).mats.map fun M => (M.m, M.k)).getD M (0, 0)).1)
    (hr : (Layer.layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
      (Layer.tableAsks P.y P.rd g) 0).isSome = true) :
    tabs p = (Closed.layShapes P g).map ofTab := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hr
  unfold tabs Closed.layShapes
  rw [ha, ← asks_layers, hx, tabs_of_layTables p _ hk hm _ [] 0 x hx]
  rfl

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.asks_layers
#print axioms VerifiableInference.Desc.First.K8.layParts_eq
#print axioms VerifiableInference.Desc.First.K8.layFamily_eq
#print axioms VerifiableInference.Desc.First.K8.tabs_of_layTables
#print axioms VerifiableInference.Desc.First.K8.tabs_layShapes
