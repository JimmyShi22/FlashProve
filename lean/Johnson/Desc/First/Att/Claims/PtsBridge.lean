-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PtsBridge.lean: kind K5: the functions on the place's numbers
(Johnson/Desc/First/Att/Geo.lean, Points.lean, over Geo) against the pure functions of OnBytes/Model
(over Shape), at geoOf S: the units; the pieces with their weights; the inner point; the last call
that holds a list; the unit of a list that one call serves. Tools for
Johnson/Desc/First/Att/Claims/PtsAgree.lean.

Main names: `units_old`, `keyBits_old`, `inner_old`, `pieces_old`, `lastHolding_old`, `single_unit`.
Used of OnBytes: plain records, pure functions and lemmas on them alone; no routine in a context and
no theorem on a run: the records Shape, ACall, Piece, PW, Seg, Table; the pure functions
Attention.unitsOf, pieces, PW.le, inner, Shape.segB, segBits, lastHolding, unitOf, eqAt.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Claim58
import OnBytes.Model.AttentionDivide

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf callOf tabOf keysOf w1Of UnitG)

/-- The units of the calls of one kind of table. -/
theorem units_old (S : Shape) (t : Table) (ks : List Attention.Seg) :
    (geoOf S).units (tabOf t) (ks.map keysOf) =
      (unitsOf S t ks).map fun u => (u.1, callOf u.2.1, keysOf u.2.2) := by
  unfold P.Geo.units unitsOf
  rw [calls_zip, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun x _ => ?_
  show (if (tabOf x.1.kind == tabOf t) = true then _ else _) = _
  rw [tab_eq]
  split
  · rw [List.filter_map, List.map_map, List.map_map]
    have e : ((fun k => (callOf x.1).holds k) ∘ keysOf) = fun s => x.1.holds s :=
      funext fun s => holds_callOf x.1 s
    rw [e]
    rfl
  · rfl

theorem keyBits_old (S : Shape) (s : Attention.Seg) : (geoOf S).keyBits (keysOf s) = S.segB s := by
  cases s <;> rfl

theorem inner_old (S : Shape) (q : ℕ) (c : ACall) (s : Attention.Seg) (key : Array E) :
    P.inner ((geoOf S).unitAt q (callOf c) (keysOf s)) key = Attention.inner S key s := by
  unfold P.inner Attention.inner P.Geo.unitAt
  dsimp only
  rw [keyBits_old]

theorem filterMap_ite {α β : Type} (p : α → Bool) (f : α → β) : ∀ l : List α,
    (l.filterMap fun a => if p a = true then some (f a) else none) = (l.filter p).map f
  | [] => rfl
  | a :: l => by
    rw [List.filterMap_cons, List.filter_cons]
    by_cases h : p a = true
    · simp only [h, if_true, List.map_cons, filterMap_ite p f l]
    · simp only [h, filterMap_ite p f l]
      rfl

/-- The pieces of a unit with their weights. -/
theorem pieces_old (S : Shape) (q : ℕ) (c : ACall) (s : Attention.Seg) (key : Array E) :
    P.piecesOf ((geoOf S).unitAt q (callOf c) (keysOf s)) key = w1Of (pieces c key s) := by
  unfold P.piecesOf pieces w1Of P.Geo.unitAt callOf
  dsimp only
  rw [filterMap_ite (fun pc : Attention.Piece => pc.seg == s), List.map_toArray, List.filter_map, List.map_map]
  congr 1
  rw [List.map_mergeSort (r := PW.le) (f := fun x : PW => ({ lam := x.lam, a := x.a, wp := x.wp } : P.W1))
    (s := fun x y : P.W1 => decide (x.lam < y.lam) || x.lam == y.lam && decide (x.a ≤ y.a))
    (fun _ _ _ _ => rfl), List.map_map]
  have e : ((fun pc : P.Pc => pc.keys == keysOf s) ∘ fun pc : Attention.Piece =>
      ({ keys := keysOf pc.seg, lam := pc.lam, a := pc.a, b := pc.b, off := pc.off } : P.Pc)) =
      fun pc : Attention.Piece => pc.seg == s := funext fun pc => keys_eq pc.seg s
  rw [e]
  rfl

theorem lastHolding_old (S : Shape) (s : Attention.Seg) :
    (geoOf S).lastHolding (keysOf s) = lastHolding S s := by
  unfold P.Geo.lastHolding lastHolding
  rw [calls_zip, List.filter_map, List.getLast?_map, Option.map_map]
  have e : ((fun x : P.CallG × ℕ => x.1.holds (keysOf s)) ∘ fun x : ACall × ℕ => (callOf x.1, x.2)) =
      fun x : ACall × ℕ => x.1.holds s := funext fun x => holds_callOf x.1 s
  rw [e]
  rfl

/-- The unit of a list that one call serves. -/
theorem single_unit (S : Shape) (zk : Array (Array E)) (s : Attention.Seg) (u : UnitG)
    (r : ℕ × Array PW × Array E) (hu : (geoOf S).single (keysOf s) = some u)
    (hr : unitOf S zk s = some r) :
    r.1 = u.call ∧ P.piecesOf u (zk.getD u.call #[]) = w1Of r.2.1 ∧
      P.inner u (zk.getD u.call #[]) = r.2.2 := by
  unfold P.Geo.single at hu
  unfold unitOf at hr
  rw [lastHolding_old] at hu
  cases hq : lastHolding S s with
  | none => rw [hq] at hr; cases hr
  | some q =>
    rw [hq] at hu hr
    dsimp only at hr
    have ec : (geoOf S).calls[q]? = (S.calls[q]?).map callOf := by
      show (S.calls.map callOf)[q]? = _
      rw [Array.getElem?_map]
    simp only [Option.bind_eq_bind, Option.bind_some, ec] at hu
    cases hc : S.calls[q]? with
    | none => rw [hc] at hr; cases hr
    | some c =>
      rw [hc] at hu hr
      simp only [Option.map_some, Option.bind_some, Option.pure_def, Option.some.injEq] at hu hr
      subst hu hr
      exact ⟨rfl, pieces_old S q c s _, inner_old S q c s _⟩

end K5Law
