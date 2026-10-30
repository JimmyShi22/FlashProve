-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/CubeKitD.lean: CONDITIONAL. Four definitions, and statements with their
proofs.

What is here. Tools for the laws on a sum over a cube: a round's polynomial at X; the tables as
multilinear maps; the challenges as a point; `mle`.

  `roundQ`, `round_eq`, `roundAt`, `round_value`   a round's three sums; its polynomial at X
  `roundAt_next`, `roundAt_sum`, `sumBy_round`   that polynomial at a challenge; summed
  `sumOver_ones`, `toList_rev`   sums with the weights 1 and 1; an array's list, written from the
     numbers n - 1, .., 0
  `prK`, `setAll`, `bind_rep`, `rep`   the tables behind some rounds against the first tables
  `pointFold_at`, `setAll_at`   the challenges by variable
  `valuesAt_getD`, `mle_sum`   a map's value behind the rounds is entry 0 of its bound table; `mle`
     as a sum under the equality table
  Beside these, smaller steps: `roundQ_at`, `valueP_three`, `mem_next`, `bindK_zero`, `bindK_one`,
  `sum_range_two`, `setAll_snoc`, `set_getD_eq`, `set_getD_ne`, `pointFold_size`, `pointFold_keep`,
  `dotK_zero`, `zipFold`.

Limits. `round_eq`, `round_value`, `sumBy_round`, `roundAt_next`, `roundAt_sum` and `mem_next` ask
that the rest of the order begins with the round's variable (c.order.drop rs.length = v :: os); the
last three are under `Inv` besides; `rep` is under `FitsP` and rs.length ≤ c.n; `bind_rep` under
hypotheses on the order of the variables and on the tables' sizes. ON WORDS, not on readings:
`round_eq`, `toList_rev`, `set_getD_eq`, `set_getD_ne`, `pointFold_size`, `pointFold_keep`,
`pointFold_at`, `valuesAt_getD`. `sumBy`, of which `sumBy_round` speaks, is a definition among the
honest file's tests (Johnson/Desc/K4/Honest/Cube.lean): no verifier's text.

Kin. `sum_range_two` IS IN THE LIBRARY in another spelling, over a field: `sum_range_two`
(Johnson/HonestTrace/LookCube.lean): n * 2 for 2 * N, the arguments in the other order.
`set_getD_eq` and `set_getD_ne` are, at the program's elements and the default 0, the library's
`getD_set_self` and `getD_set_ne` (Johnson/Desc/K8/Honest/EqReturnsProofs.lean: any type, any
default), which it states more than once again. This file builds on none of these.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.CubeKitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading eqTab)
open OnBytes.Road (getD_map_lt getD_ge)
open OnBytes.Desc.First.K4.Honest.CubeTest (sumBy)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## 1 A round's polynomial -/

/-- The three sums of `Cube.round`, v the round's variable. -/
def roundQ (c : Cube) (rs : List E) (v : ℕ) : E × E × E :=
  fold3 (fun i => (weightsOf (((c.bound rs).1.erase v).map (sidesOf c))).getD i zeroE)
    (fun i => lineAt c.pairs (c.bound rs).2 (lowAt (2 ^ placeOf (c.bound rs).1 v) i)
      (2 ^ placeOf (c.bound rs).1 v))
    (2 ^ ((c.bound rs).1.erase v).length)

theorem round_eq {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) :
    c.round rs = [(roundQ c rs v).1, (roundQ c rs v).2.1, (roundQ c rs v).2.2] := by
  unfold Cube.round
  rw [h]
  rfl

/-- The round's polynomial at X: the summand on the tables with the round's variable set to X,
summed over the variables of the later rounds. -/
def roundAt (c : Cube) (rs : List E) (v : ℕ) (X : K) : K :=
  sumOver (((c.bound rs).1.erase v).reverse.map (sidesK ρ c)) fun i =>
    sumT ρ c.pairs (fun a => bindK (2 ^ placeOf (c.bound rs).1 v) X (rdM ρ (c.bound rs).2 a)) i

theorem roundQ_at (c : Cube) (rs : List E) (v : ℕ) (X : K) :
    ρ.val (roundQ c rs v).1 + ρ.val (roundQ c rs v).2.1 * X + ρ.val (roundQ c rs v).2.2 * X ^ 2 =
      roundAt ρ c rs v X := by
  have hw := weights_sum ρ (((c.bound rs).1.erase v).map (sidesOf c)) fun i =>
    sumT ρ c.pairs (fun a => bindK (2 ^ placeOf (c.bound rs).1 v) X (rdM ρ (c.bound rs).2 a)) i
  rw [List.length_map, List.map_map, ← List.map_reverse] at hw
  unfold roundQ roundAt
  rw [fold3_read]
  simp only [lineAt_rd]
  exact hw

theorem valueP_three (a b d r : E) :
    ρ.val (valueP [a, b, d] r) = ρ.val a + ρ.val b * ρ.val r + ρ.val d * ρ.val r ^ 2 := by
  simp only [valueP, List.foldr_cons, List.foldr_nil, ρ.add, ρ.mul, ρ.zero]
  ring

theorem round_value {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) (r : E) :
    ρ.val (valueP (c.round rs) r) = roundAt ρ c rs v (ρ.val r) := by
  rw [round_eq h, valueP_three, roundQ_at]

theorem mem_next {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) (I : Inv c rs) : v ∈ (c.bound rs).1 :=
  (I.mem v).mpr (by rw [h]; simp)

theorem roundAt_next {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) (I : Inv c rs) (r : E) :
    roundAt ρ c rs v (ρ.val r) = partK ρ c (rs ++ [r]) := by
  have hv := mem_next h I
  obtain ⟨L, hL⟩ : ∃ L, (c.bound rs).1.length = L + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (List.length_pos_of_mem hv)).symm⟩
  have hs : ∀ a, a < (c.bound rs).2.size → ((c.bound rs).2.getD a #[]).size = 2 ^ (L + 1) := by
    intro a ha
    rw [I.size a ha, hL]
  unfold roundAt partK
  rw [bound_snoc h r]
  show _ = sumOver (((c.bound rs).1.erase v).reverse.map (sidesK ρ c)) fun i =>
    ρ.val (termsAt c.pairs ((c.bound rs).2.map (bindAt (placeOf (c.bound rs).1 v) r)) i)
  refine sumOver_congr _ _ _ fun i hi => ?_
  rw [List.length_map, List.length_reverse, List.length_erase_of_mem hv, hL,
    Nat.add_sub_cancel] at hi
  have hb := fun a => rdM_bind ρ (c.bound rs).2 (placeOf (c.bound rs).1 v) r L hs a i hi
  rw [termsAt_rd]
  simp only [sumT, hb]

theorem bindK_zero (s : ℕ) (f : ℕ → K) : bindK s 0 f = fun i => f (lowAt s i) := by
  funext i
  simp [bindK]

theorem bindK_one (s : ℕ) (f : ℕ → K) : bindK s 1 f = fun i => f (lowAt s i + s) := by
  funext i
  simp [bindK]

theorem roundAt_sum {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) (I : Inv c rs) :
    (sidesK ρ c v).1 * roundAt ρ c rs v 0 + (sidesK ρ c v).2 * roundAt ρ c rs v 1 =
      partK ρ c rs := by
  obtain ⟨hi, lo, e, h1, h2⟩ := split_sorted _ I.sorted v (mem_next h I)
  have q : (hi ++ v :: lo).reverse.map (sidesK ρ c) =
      lo.reverse.map (sidesK ρ c) ++ sidesK ρ c v :: hi.reverse.map (sidesK ρ c) := by simp
  have q' : (hi ++ lo).reverse.map (sidesK ρ c) =
      lo.reverse.map (sidesK ρ c) ++ hi.reverse.map (sidesK ρ c) := by simp
  unfold roundAt partK
  rw [e, placeOf_split hi lo v h1 h2, erase_split hi lo v h1, q, q', sumOver_peel]
  simp only [bindK_zero, bindK_one, termsAt_rd, List.length_map, List.length_reverse]
  rfl

theorem sumBy_round {c : Cube} {rs : List E} {v : ℕ} {os : List ℕ}
    (h : c.order.drop rs.length = v :: os) :
    ρ.val (sumBy c.points[rs.length]? (c.round rs)) =
      (sidesK ρ c v).1 * roundAt ρ c rs v 0 + (sidesK ρ c v).2 * roundAt ρ c rs v 1 := by
  have h0 : ρ.val (valueP (c.round rs) zeroE) = roundAt ρ c rs v 0 := by
    rw [round_value ρ h, ρ.zero]
  have h1 : ρ.val (valueP (c.round rs) oneE) = roundAt ρ c rs v 1 := by
    rw [round_value ρ h, ρ.one]
  have hv : c.order[rs.length]? = some v := by
    have := congrArg (fun l => l[0]?) h
    simpa using this
  cases hw : c.way with
  | plain =>
    have hp : c.points[rs.length]? = none := by simp [Cube.points, hw]
    rw [hp]
    show ρ.val (addE (valueP (c.round rs) zeroE) (valueP (c.round rs) oneE)) = _
    rw [ρ.add, h0, h1]
    simp [sidesK, sidesOf, hw, ρ.one]
  | point rho =>
    have hp : c.points[rs.length]? = some (rho.getD (c.n - 1 - v) zeroE) := by
      simp [Cube.points, hw, hv]
    rw [hp]
    show ρ.val (addE (mulE (subE oneE (rho.getD (c.n - 1 - v) zeroE)) (valueP (c.round rs) zeroE))
      (mulE (rho.getD (c.n - 1 - v) zeroE) (valueP (c.round rs) oneE))) = _
    rw [ρ.add, ρ.mul, ρ.mul, h0, h1]
    simp [sidesK, sidesOf, hw]

/-! ## 2 Two lists -/

theorem sum_range_two (F : ℕ → K) : ∀ N : ℕ,
    ∑ i ∈ Finset.range (2 * N), F i = ∑ i ∈ Finset.range N, (F (2 * i) + F (2 * i + 1))
  | 0 => by simp
  | N + 1 => by
    have e : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, sum_range_two F N, Finset.sum_range_succ]
    ring

/-- With the weights 1 and 1 throughout the sum is the bare sum. -/
theorem sumOver_ones : ∀ (q : List (K × K)) (F : ℕ → K), (∀ w ∈ q, w = (1, 1)) →
    sumOver q F = ∑ i ∈ Finset.range (2 ^ q.length), F i
  | [], F, _ => by simp [sumOver]
  | w :: q, F, h => by
    have hw : w = (1, 1) := h w (by simp)
    have hq : ∀ u ∈ q, u = (1, 1) := fun u hu => h u (by simp [hu])
    rw [List.length_cons, pow_succ', sum_range_two, Finset.sum_add_distrib, sumOver,
      sumOver_ones q _ hq, sumOver_ones q _ hq, hw]
    simp

/-- An array's list, written from the numbers n - 1, .., 0. -/
theorem toList_rev (a : Array E) (n : ℕ) (h : a.size = n) :
    (List.range n).reverse.map (fun v => a.getD (n - 1 - v) zeroE) = a.toList := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    have e : n - 1 - (n - 1 - i) = i := by omega
    simp [e, Array.getD, h, hi]

/-! ## 3 The tables behind some rounds -/

/-- A coordinate's two weights. -/
def prK (X : ℕ → K) (v : ℕ) : K × K := (1 - X v, X v)

/-- X with the listed variables set to the readings of the listed elements. Where a variable is
listed twice the first listing holds. -/
def setAll (zs : List (ℕ × E)) (X : ℕ → K) : ℕ → K :=
  zs.foldr (fun x Y => Function.update Y x.1 (ρ.val x.2)) X

theorem bind_rep (ms : Array Tab) (hi lo : List ℕ) (v : ℕ) (h1 : ∀ u ∈ hi, v < u)
    (h2 : ∀ u ∈ lo, u < v)
    (hs : ∀ a, a < ms.size → (ms.getD a #[]).size = 2 ^ (hi ++ v :: lo).length) (r : E)
    (X : ℕ → K) (m : ℕ) :
    sumOver (((hi ++ v :: lo).erase v).reverse.map (prK X))
        (rdM ρ (ms.map (bindAt (placeOf (hi ++ v :: lo) v) r)) m) =
      sumOver ((hi ++ v :: lo).reverse.map (prK (Function.update X v (ρ.val r)))) (rdM ρ ms m) := by
  have hlo : lo.reverse.map (prK (Function.update X v (ρ.val r))) = lo.reverse.map (prK X) :=
    List.map_congr_left fun u hu => by
      have hne : u ≠ v := Nat.ne_of_lt (h2 u (List.mem_reverse.mp hu))
      simp [prK, Function.update_of_ne hne]
  have hhi : hi.reverse.map (prK (Function.update X v (ρ.val r))) = hi.reverse.map (prK X) :=
    List.map_congr_left fun u hu => by
      have hne : u ≠ v := Nat.ne_of_gt (h1 u (List.mem_reverse.mp hu))
      simp [prK, Function.update_of_ne hne]
  have q : (hi ++ v :: lo).reverse.map (prK (Function.update X v (ρ.val r))) =
      lo.reverse.map (prK X) ++ (1 - ρ.val r, ρ.val r) :: hi.reverse.map (prK X) := by
    rw [← hlo, ← hhi]
    simp [prK]
  have q' : (hi ++ lo).reverse.map (prK X) =
      lo.reverse.map (prK X) ++ hi.reverse.map (prK X) := by simp
  have hlen : (hi ++ v :: lo).length = (hi ++ lo).length + 1 := by
    simp only [List.length_append, List.length_cons]
    omega
  rw [hlen] at hs
  have hsb := sumOver_bind (lo.reverse.map (prK X)) (hi.reverse.map (prK X)) (ρ.val r) (rdM ρ ms m)
  rw [List.length_map, List.length_reverse] at hsb
  rw [placeOf_split hi lo v h1 h2, erase_split hi lo v h1, q, q', ← hsb]
  refine sumOver_congr _ _ _ fun i hi' => ?_
  rw [← q', List.length_map, List.length_reverse] at hi'
  exact rdM_bind ρ ms lo.length r _ hs m i hi'

theorem setAll_snoc (zs : List (ℕ × E)) (v : ℕ) (r : E) (X : ℕ → K) :
    setAll ρ (zs ++ [(v, r)]) X = setAll ρ zs (Function.update X v (ρ.val r)) := by
  unfold setAll
  rw [List.foldr_append]
  rfl

/-- **The tables behind the rounds of rs, as multilinear maps in the variables that are left, are
the first tables with the rounds' variables at the challenges.** CONDITIONAL: on F and
rs.length ≤ c.n. -/
theorem rep {c : Cube} (F : FitsP c) (m : ℕ) : ∀ rs : List E, rs.length ≤ c.n → ∀ X : ℕ → K,
    sumOver ((c.bound rs).1.reverse.map (prK X)) (rdM ρ (c.bound rs).2 m) =
      sumOver ((List.range c.n).map (prK (setAll ρ (c.order.zip rs) X))) (rdM ρ c.maps m) := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil =>
    intro _ X
    rw [bound_nil, List.zip_nil_right, List.reverse_reverse]
    rfl
  | append_singleton rs r ih =>
    intro hr X
    rw [List.length_append, List.length_singleton] at hr
    obtain ⟨v, os, h⟩ := next_var F rs (by omega)
    have I := inv F rs (by omega)
    obtain ⟨hi, lo, e, h1, h2⟩ := split_sorted _ I.sorted v (mem_next h I)
    have hs := I.size
    rw [zips h r, setAll_snoc, ← ih (by omega), bound_snoc h r]
    show sumOver (((c.bound rs).1.erase v).reverse.map (prK X))
      (rdM ρ ((c.bound rs).2.map (bindAt (placeOf (c.bound rs).1 v) r)) m) = _
    rw [e] at hs ⊢
    exact bind_rep ρ _ hi lo v h1 h2 hs r X m

/-! ## 4 The challenges by variable -/

theorem setAll_at : ∀ (zs : List (ℕ × E)) (X : ℕ → K), (zs.map Prod.fst).Nodup →
    ∀ x ∈ zs, setAll ρ zs X x.1 = ρ.val x.2
  | [], _, _, x, hx => by simp at hx
  | y :: zs, X, hn, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hn
    show Function.update (setAll ρ zs X) y.1 (ρ.val y.2) x.1 = ρ.val x.2
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [Function.update_self]
    · have hne : x.1 ≠ y.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hx')
      rw [Function.update_of_ne hne]
      exact setAll_at zs X hn.2 x hx'

theorem set_getD_eq (a : Array E) (q : ℕ) (r : E) (h : q < a.size) :
    (a.set! q r).getD q zeroE = r := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem set_getD_ne (a : Array E) (q p : ℕ) (r : E) (h : q ≠ p) :
    (a.set! q r).getD p zeroE = a.getD p zeroE := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem pointFold_size (n : ℕ) : ∀ (zs : List (ℕ × E)) (a : Array E),
    (zs.foldl (fun a x => a.set! (n - 1 - x.1) x.2) a).size = a.size
  | [], _ => rfl
  | y :: zs, a => by
    rw [List.foldl_cons, pointFold_size n zs]
    simp

theorem pointFold_keep (n p : ℕ) : ∀ (zs : List (ℕ × E)) (a : Array E),
    (∀ x ∈ zs, n - 1 - x.1 ≠ p) →
    (zs.foldl (fun a x => a.set! (n - 1 - x.1) x.2) a).getD p zeroE = a.getD p zeroE
  | [], _, _ => rfl
  | y :: zs, a, h => by
    rw [List.foldl_cons, pointFold_keep n p zs _ fun x hx => h x (by simp [hx]),
      set_getD_ne _ _ _ _ (h y (by simp))]

/-- Where the listed variables differ and lie below n, each one's element lies at its place. -/
theorem pointFold_at (n : ℕ) : ∀ (zs : List (ℕ × E)) (a : Array E), (zs.map Prod.fst).Nodup →
    (∀ x ∈ zs, x.1 < n) → a.size = n →
    ∀ x ∈ zs, (zs.foldl (fun a x => a.set! (n - 1 - x.1) x.2) a).getD (n - 1 - x.1) zeroE = x.2
  | [], _, _, _, _, x, hx => by simp at hx
  | y :: zs, a, hn, hb, ha, x, hx => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hx1 := hb x (by simp)
      rw [pointFold_keep n _ zs _ fun z hz => by
        have hz1 := hb z (by simp [hz])
        have hne : z.1 ≠ x.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hz)
        omega]
      exact set_getD_eq a _ _ (by omega)
    · exact pointFold_at n zs _ hn.2 (fun z hz => hb z (by simp [hz])) (by simp [ha]) x hx'

/-! ## 5 The values and `mle` -/

theorem valuesAt_getD (c : Cube) (rs : List E) (m : ℕ) :
    (c.valuesAt rs).getD m zeroE = ((c.bound rs).2.getD m #[]).getD 0 zeroE := by
  unfold Cube.valuesAt
  by_cases h : m < (c.bound rs).2.size
  · rw [getD_map_lt _ _ h zeroE #[]]
  · have h' : (c.bound rs).2.size ≤ m := Nat.le_of_not_lt h
    rw [getD_ge _ (by rw [Array.size_map]; exact h') zeroE, getD_ge _ h' #[],
      getD_ge #[] (Nat.zero_le 0) zeroE]

theorem dotK_zero : ∀ t : List K, dotK t (fun _ => 0) = 0
  | [] => rfl
  | a :: t => by
    rw [dotK, dotK_zero t]
    simp

theorem zipFold : ∀ (a b : List E) (s : E),
    ρ.val ((a.zip b).foldl (fun s y => addE s (mulE y.1 y.2)) s) =
      ρ.val s + dotK (a.map ρ.val) fun i => ρ.val (b.getD i zeroE)
  | [], _, _ => by simp [dotK]
  | x :: a, [], s => by
    have e : (fun i => ρ.val (([] : List E).getD i zeroE)) = fun _ => (0 : K) := by
      funext i
      simp [ρ.zero]
    rw [e, dotK_zero]
    simp
  | x :: a, y :: b, s => by
    rw [List.zip_cons_cons, List.foldl_cons, zipFold a b, ρ.add, ρ.mul]
    simp only [List.map_cons, dotK, List.getD_cons_zero, List.getD_cons_succ]
    ring

/-- `mle` as a sum under the library's equality table. -/
theorem mle_sum (t : Tab) (z : Array E) :
    ρ.val (mle t z) =
      ∑ i ∈ Finset.range (2 ^ z.size), ρ.val ((eqTab z).getD i zeroE) * rdT ρ t i := by
  unfold mle
  rw [← Array.foldl_toList, Array.toList_zip, zipFold, ρ.zero, zero_add, dotK_sum,
    List.length_map, Array.length_toList, OnBytes.Road.eqTab_size]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : t.toList.getD i zeroE = t.getD i zeroE := by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [getD_mapA, e]
  rfl

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.roundQ
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.round_eq
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.roundAt
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.roundQ_at
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.valueP_three
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.round_value
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.mem_next
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.roundAt_next
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bindK_zero
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bindK_one
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.roundAt_sum
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sumBy_round
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sum_range_two
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sumOver_ones
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.toList_rev
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.prK
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.setAll
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bind_rep
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.setAll_snoc
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.rep
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.setAll_at
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.set_getD_eq
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.set_getD_ne
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.pointFold_size
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.pointFold_keep
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.pointFold_at
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.valuesAt_getD
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.dotK_zero
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.zipFold
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.mle_sum
