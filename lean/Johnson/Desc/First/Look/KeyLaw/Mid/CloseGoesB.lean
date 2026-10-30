-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/CloseGoesB.lean: the sumcheck on k variables of degree 2 and a
further variable of degree 2, seen as a sumcheck on k + 1 variables of degree 2 whose last equality
weight stands at 0.

It imports CloseGoesC.lean; `Lev.rowF`, `Lev.finC`, `Lev.nmV`, `Lev.nmC`, `Lev.lk` are those of
Cb/Pv/KeyLookup/LevRunA.lean.
Main names:
  `portIdx_inl`, `portIdx_inr` `Cf.portIdx` at a variable that is not the last.
  `hidM_rowF` `hidM` at k + 1 variables of degree 2 is `Lev.rowF k`, if on both sides the place of a
    name is a function e of its number `Cf.portIdx`.
  `finM_finC` `finM` at k + 1 variables of degree 2, the last weight at 0, is `Lev.finC k`.
  `ofFn_snoc0` the list of the k + 1 weights.
Limits: statements on plain functions over the field.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.CloseGoesC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid.Clo
open Lk6.PortSim Lk6.Clo

open OnBytes OnBytes.Slice Flat Cb Cb.LdLkp Finset Lk6.PortSim

theorem portIdx_inl {E : Type} [Field E] (f : PFmt E) : ∀ (l : List (PFmt E)), l ≠ [] →
    ∀ t : Fin f.n, Cf.portIdx (f :: l) (.inl t) = t.val
  | [], h, _ => absurd rfl h
  | _ :: _, _, _ => rfl

theorem portIdx_inr {E : Type} [Field E] (f : PFmt E) : ∀ (l : List (PFmt E)), l ≠ [] →
    ∀ i : PIdx l, Cf.portIdx (f :: l) (.inr i) = f.n + Cf.portIdx l i
  | [], h, _ => absurd rfl h
  | _ :: _, _, _ => rfl

theorem lk_ne (k : ℕ) : Lev.lk GE k ≠ [] := by simp [Lev.lk]

theorem hidM_rowF {J : Type} [DecidableEq J] (j : J) : ∀ (k : ℕ) (e : ℕ → J) (c : ℕ → GE),
    hidM (k + 1) (fun _ => 2) (fun i => e (Cf.portIdx (pfMix GE (k + 1) fun _ => 2) i)) c j =
      Lev.rowF k (fun r t => e (Cf.portIdx (Lev.lk GE k) (Lev.nmV GE k r t)))
        (e (Cf.portIdx (Lev.lk GE k) (Lev.nmC GE k))) c j
  | 0, e, c => by
    show (∑ t : Fin 2, Lev.one (e (1 + t.val)) (c 0 ^ (t.val + 1)) j) + Lev.one (e 0) 1 j =
      Lev.one (e (1 + 0)) (c 0) j + Lev.one (e (1 + 1)) (c 0 ^ 2) j + Lev.one (e 0) 1 j
    rw [Fin.sum_univ_two]
    show Lev.one (e (1 + 0)) (c 0 ^ (0 + 1)) j + Lev.one (e (1 + 1)) (c 0 ^ (1 + 1)) j + _ = _
    rw [zero_add, pow_one]
  | k + 1, e, c => by
    have ih := hidM_rowF j k (fun n => e (2 + n)) fun i => c (i + 1)
    show (∑ t : Fin 2, Lev.one (e t.val) (c 0 ^ (t.val + 1)) j) +
      hidM (k + 1) (fun _ => 2)
        (fun i => e (2 + Cf.portIdx (pfMix GE (k + 1) fun _ => 2) i)) (fun i => c (i + 1)) j =
      Lev.one (e (Cf.portIdx (pfCube GE 2 :: Lev.lk GE k) (.inl 0))) (c 0) j +
        Lev.one (e (Cf.portIdx (pfCube GE 2 :: Lev.lk GE k) (.inl 1))) (c 0 ^ 2) j +
        Lev.rowF k (fun r t => e (Cf.portIdx (pfCube GE 2 :: Lev.lk GE k)
            (.inr (Lev.nmV GE k r t))))
          (e (Cf.portIdx (pfCube GE 2 :: Lev.lk GE k) (.inr (Lev.nmC GE k))))
          (fun i => c (i + 1)) j
    rw [ih, Fin.sum_univ_two, portIdx_inl _ _ (lk_ne k), portIdx_inl _ _ (lk_ne k),
      portIdx_inr _ _ (lk_ne k)]
    have e1 : (fun r t => e (Cf.portIdx (pfCube GE 2 :: Lev.lk GE k) (.inr (Lev.nmV GE k r t)))) =
        fun r t => e (2 + Cf.portIdx (Lev.lk GE k) (Lev.nmV GE k r t)) :=
      funext fun r => funext fun t => by rw [portIdx_inr _ _ (lk_ne k)]
    rw [e1]
    show Lev.one (e 0) (c 0 ^ (0 + 1)) j + Lev.one (e 1) (c 0 ^ (1 + 1)) j + _ = _
    rw [zero_add, pow_one]
    rfl

theorem finM_finC : ∀ (k : ℕ) (L : List GE), L.length = k → ∀ (σ : GE) (f : List (RV GE)),
    finM (k + 1) (fun _ => 2) (fun i => (L ++ [0]).getD i.val 0) σ f =
      Lev.finC k (fun i => L.getD i.val 0) σ f
  | 0, [], _, σ, f => by
    show σ - 0 * (∑ t : Fin 2, Lev.snt f 0 t) +
        ∑ t : Fin 2, Lev.snt f 0 t * Lev.chC f 0 ^ (t.val + 1) =
      σ + Lev.snt f 0 0 * Lev.chC f 0 + Lev.snt f 0 1 * Lev.chC f 0 ^ 2
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    show σ - 0 * _ +
      (Lev.snt f 0 0 * Lev.chC f 0 ^ (0 + 1) + Lev.snt f 0 1 * Lev.chC f 0 ^ (1 + 1)) = _
    ring
  | 0, _ :: _, h, _, _ => absurd h (by simp)
  | _ + 1, [], h, _, _ => absurd h (by simp)
  | k + 1, a :: L, h, σ, f => by
    have ih := finM_finC k L (by simpa using h)
      (σ - a * (Lev.snt f 0 0 + Lev.snt f 0 1) + Lev.snt f 0 0 * Lev.chC f 0 +
        Lev.snt f 0 1 * Lev.chC f 0 ^ 2) f.tail
    show finM (k + 1) (fun _ => 2) (fun i => (L ++ [0]).getD i.val 0)
      (σ - a * (∑ t : Fin 2, Lev.snt f 0 t) +
        ∑ t : Fin 2, Lev.snt f 0 t * Lev.chC f 0 ^ (t.val + 1))
      f.tail = Lev.finC k (fun i => L.getD i.val 0)
      (σ - a * (Lev.snt f 0 0 + Lev.snt f 0 1) + Lev.snt f 0 0 * Lev.chC f 0 +
        Lev.snt f 0 1 * Lev.chC f 0 ^ 2) f.tail
    rw [← ih, Fin.sum_univ_two, Fin.sum_univ_two]
    refine congrArg (fun s => finM (k + 1) (fun _ => 2) (fun i => (L ++ [0]).getD i.val 0) s f.tail)
      ?_
    show σ - a * (Lev.snt f 0 0 + Lev.snt f 0 1) +
      (Lev.snt f 0 0 * Lev.chC f 0 ^ (0 + 1) + Lev.snt f 0 1 * Lev.chC f 0 ^ (1 + 1)) = _
    ring

theorem ofFn_snoc0 (k : ℕ) (L : List GE) (h : L.length = k) :
    (List.ofFn fun i : Fin (k + 1) => PscF.Weight.equality ((L ++ [0]).getD i.val 0) (2 + 1)) =
      L.map (fun a => PscF.Weight.equality a 3) ++ [PscF.Weight.atZero 3] := by
  have e : (List.ofFn fun i : Fin (k + 1) =>
        PscF.Weight.equality ((L ++ [0]).getD i.val 0) (2 + 1)) =
      (List.ofFn fun i : Fin (k + 1) => (L ++ [0]).getD i.val 0).map
        fun a => PscF.Weight.equality a 3 := by
    rw [List.map_ofFn]
    rfl
  rw [e, ofFn_getD _ _ (by rw [List.length_append, h]; rfl), List.map_append]
  rfl

end Lk6.Mid.Clo

#print axioms Lk6.Mid.Clo.hidM_rowF
#print axioms Lk6.Mid.Clo.finM_finC
#print axioms Lk6.Mid.Clo.ofFn_snoc0
