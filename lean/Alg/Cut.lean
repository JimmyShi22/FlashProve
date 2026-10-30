-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Alg/Cut.lean: a point that is drawn in one message, cut into its elements: the bad tuples of a polynomial identity, element by element.

A round may draw a point of n elements at once. The count of its bad tuples (Alg/Poly.lean, DegLE.count_zero_le: at most (∑ d j) |K|^(n - 1))
says nothing on a single element. This file gives, for the zeros of a function that is not identically 0 and has degree at most d j in
its variable number j, a set of at most d j bad values for each element, which hangs on the earlier elements alone, such that every
zero has a bad element. The sets are said by meaning: the function is still alive behind the earlier elements, and dead behind them
with this value. No coefficient is picked.

Main names:
  Alive g j x      : g is not identically 0 on the points that agree with x in the first j coordinates.
  cutBad g j x     : the bad values of the element number j.
  cutBad_congr     : they hang on the earlier elements alone.
  cutBad_count     : they are at most d j (by DegLE.count_update_le).
  cut_covers       : a zero of a function that is not identically 0 has a bad element.
  cut_count        : back: the tuples with a bad element are at most (∑ d j) |K|^(n - 1) (by count_pi_exists_le).
  cutBadF, cutBadF_congr, cutBadF_count, cut_covers_family : MANY FUNCTIONS ON ONE POINT, in a fixed order: the bad values are those of
                     the first function that is alive behind the earlier elements: at most d j, the largest degree, NOT the sum over the
                     family; if some function is not identically 0 and all vanish at the point, the point has a bad element.
  ptOf, alongL, along_list, cutBadL, cutBadFL, their counts, cut_covers_list, cut_coversL, cut_covers_family_list : the same along a list, as a view
                     shows the drawn elements: if no member is bad behind the members before it, the function (some function of the
                     family) is not 0 at the point.
  cut_bites        : the sets are not always empty: at the function «the one coordinate», 0 is bad.
  cut_step, cut_back, cut_step_family, cut_back_family : WHAT A ROUND THAT DRAWS A POINT OWES, with the relation in front (In) and behind
                     (Out) as letters: ALIVE (In fails: g is not identically 0) and DIES (Out holds: g is 0 at the point): then a
                     false front with a true behind has a bad element. zero_not_alive, const_not_dies: the function 0 and a constant
                     other than 0 buy nothing.
  finOf, cutFin, cutFinF, cutFin_card_le, cutFinF_card_le, cut_back_list, cut_back_family_list : THE SAME AS FINITE SETS, behind a list of
                     elements, for a meaning that names the bad values of each drawn element by a Finset: the size at EVERY list (empty
                     behind n elements or more), and the backward step along the list of what the round drew.
  no_cut, no_cut_at, no_cut_at_two : WITHOUT SUCH A FORM THERE IS NO CUT: the square on s + 1 values, which is within s |K| as soon as
                     (s + 1)^2 ≤ s |K|, is covered at NO split k₁ + k₂ = s by at most k₁ bad first elements and at most k₂ bad second
                     elements; at s = 2: nine pairs, in every finite type with five values or more.

DegLE d g (Alg/Poly.lean) is the degree IN EACH SINGLE VARIABLE, the others fixed: not the total degree.
A TWIN: Blocks/StageBoth.lean has Vanishes and cnt_vanishes_le: «not Alive g j x» is «Vanishes g x T» at T the variables from j on, and
cutBad_count is cnt_vanishes_le in these words; its doomed_rider is the cut where each element is drawn in a round of its own. This file
does not import it, because it stands above files of blocks and this file stands under lean/Alg. New here: a point drawn in ONE
message, cut along a list; the family's form on such a point; that without a form there is no cut.
WHAT no_cut SHOWS, AND NO MORE: from the count of the bad tuples alone one cannot have sets for each element whose sizes add up to the
count's own numerator. (Larger sets one can have: at two elements, of about the square root of the count.) A bridge that carries a set of
tuples as it is, with no set for an element, is another road; it is not taken here and nothing here speaks against it.
Limits: on functions and counts alone; the file mentions no protocol. That the bad tuples of a given round lie in the zeros of such a
function is a fact about that round, not said here.
-/
import Alg.Poly

set_option autoImplicit false

namespace Alg

open Finset

section Cut

variable {K : Type*} [CommRing K] {n : ℕ}

/-- g is not identically 0 on the points that agree with x in the first j coordinates. -/
def Alive (g : (Fin n → K) → K) (j : ℕ) (x : Fin n → K) : Prop :=
  ∃ w : Fin n → K, (∀ i : Fin n, i.1 < j → w i = x i) ∧ g w ≠ 0

/-- The bad values of the element number j: alive in front of it, dead behind it. -/
def cutBad (g : (Fin n → K) → K) (j : Fin n) (x : Fin n → K) : Set K :=
  {t | Alive g j.1 x ∧ ¬ Alive g (j.1 + 1) (Function.update x j t)}

theorem alive_congr (g : (Fin n → K) → K) (j : ℕ) (x x' : Fin n → K) (h : ∀ i : Fin n, i.1 < j → x i = x' i) :
    Alive g j x ↔ Alive g j x' :=
  ⟨fun ⟨w, hw, hg⟩ => ⟨w, fun i hi => (hw i hi).trans (h i hi), hg⟩,
    fun ⟨w, hw, hg⟩ => ⟨w, fun i hi => (hw i hi).trans (h i hi).symm, hg⟩⟩

theorem alive_zero (g : (Fin n → K) → K) (x : Fin n → K) : Alive g 0 x ↔ ∃ w, g w ≠ 0 :=
  ⟨fun ⟨w, _, hg⟩ => ⟨w, hg⟩, fun ⟨w, hg⟩ => ⟨w, fun _ hi => absurd hi (Nat.not_lt_zero _), hg⟩⟩

theorem alive_full (g : (Fin n → K) → K) (x : Fin n → K) : Alive g n x ↔ g x ≠ 0 :=
  ⟨fun ⟨w, hw, hg⟩ => by
      have e : w = x := funext fun i => hw i i.2
      rwa [e] at hg,
    fun hg => ⟨x, fun _ _ => rfl, hg⟩⟩

omit [CommRing K] in
/-- Two points that agree in front of j agree, with one value at j, up to j. -/
theorem update_agree (j : Fin n) (x x' : Fin n → K) (t : K) (h : ∀ i : Fin n, i.1 < j.1 → x i = x' i) (i : Fin n)
    (hi : i.1 < j.1 + 1) : Function.update x j t i = Function.update x' j t i := by
  rw [Function.update_apply, Function.update_apply]
  split_ifs with e
  · rfl
  · have hne : i.1 ≠ j.1 := fun hv => e (Fin.ext hv)
    exact h i (by omega)

/-- Fixed before the element: the bad values hang on the earlier elements alone. -/
theorem cutBad_congr (g : (Fin n → K) → K) (j : Fin n) (x x' : Fin n → K) (h : ∀ i : Fin n, i.1 < j.1 → x i = x' i) :
    cutBad g j x = cutBad g j x' := by
  ext t
  show (Alive g j.1 x ∧ ¬ Alive g (j.1 + 1) (Function.update x j t)) ↔
    (Alive g j.1 x' ∧ ¬ Alive g (j.1 + 1) (Function.update x' j t))
  rw [alive_congr g j.1 x x' h, alive_congr g (j.1 + 1) _ _ (update_agree j x x' t h)]

/-- **At most d j values are bad.** -/
theorem cutBad_count [IsDomain K] [Finite K] {d : Fin n → ℕ} {g : (Fin n → K) → K} (hg : DegLE d g) (j : Fin n)
    (x : Fin n → K) : Nat.card {t : K // t ∈ cutBad g j x} ≤ d j := by
  by_cases ha : Alive g j.1 x
  · obtain ⟨w, hw, hne⟩ := ha
    refine le_trans (count_mono fun t ht => ?_) (hg.count_update_le w hne j)
    by_contra hcon
    exact ht.2 ⟨Function.update w j t, update_agree j w x t hw, hcon⟩
  · rw [count_eq_zero fun t ht => ha ht.1]
    exact Nat.zero_le _

/-- **The cut**: a zero of a function that is not identically 0 has a bad element. -/
theorem cut_covers (g : (Fin n → K) → K) (hw : ∃ w, g w ≠ 0) (x : Fin n → K) (hx : g x = 0) :
    ∃ j : Fin n, x j ∈ cutBad g j x := by
  by_contra hno
  have key : ∀ k, k ≤ n → Alive g k x := by
    intro k
    induction k with
    | zero => exact fun _ => (alive_zero g x).2 hw
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      by_contra h3
      refine hno ⟨⟨k, by omega⟩, h1, ?_⟩
      rw [Function.update_eq_self]
      exact h3
  exact (alive_full g x).1 (key n (Nat.le_refl n)) hx

/-- Back: the tuples with a bad element are at most (∑ d j) |K|^(n - 1). -/
theorem cut_count [IsDomain K] [Fintype K] {d : Fin n → ℕ} {g : (Fin n → K) → K} (hg : DegLE d g) :
    Nat.card {x : Fin n → K // ∃ j, x j ∈ cutBad g j x} ≤ (∑ j, d j) * Fintype.card K ^ (n - 1) := by
  have h := count_pi_exists_le (fun (j : Fin n) (x : Fin n → K) => x j ∈ cutBad g j x) d fun j f => by
    refine le_trans (count_mono fun a ha => ?_) (cutBad_count hg j f)
    have ha' : Function.update f j a j ∈ cutBad g j (Function.update f j a) := ha
    rw [Function.update_apply, if_pos rfl, cutBad_congr g j (Function.update f j a) f fun i hi => by
      rw [Function.update_apply, if_neg fun e => by
        rw [e] at hi
        exact Nat.lt_irrefl _ hi]] at ha'
    exact ha'
  rwa [Fintype.card_fin] at h

/-- The sets are not always empty. -/
theorem cut_bites [Nontrivial K] (x : Fin 1 → K) : (0 : K) ∈ cutBad (fun z : Fin 1 → K => z 0) 0 x := by
  refine ⟨⟨fun _ => 1, fun _ hi => absurd hi (Nat.not_lt_zero _), one_ne_zero⟩, ?_⟩
  rintro ⟨w, hw, hne⟩
  apply hne
  have h0 := hw 0 (Nat.lt_succ_self _)
  rw [Function.update_apply, if_pos rfl] at h0
  exact h0

end Cut

/-! ## Many functions on one point: the first that is alive -/

section Family

variable {K : Type*} [CommRing K] {n : ℕ} {M : Type*} [LinearOrder M]

/-- The bad values of the element number j for a family in a fixed order: those of the first member that is alive behind the earlier
elements; none if no member is. -/
def cutBadF (G : M → (Fin n → K) → K) (j : Fin n) (x : Fin n → K) : Set K :=
  {t | ∃ m, IsFirst (fun m => Alive (G m) j.1 x) m ∧ t ∈ cutBad (G m) j x}

theorem cutBadF_congr (G : M → (Fin n → K) → K) (j : Fin n) (x x' : Fin n → K)
    (h : ∀ i : Fin n, i.1 < j.1 → x i = x' i) : cutBadF G j x = cutBadF G j x' := by
  have e : (fun m => Alive (G m) j.1 x) = fun m => Alive (G m) j.1 x' :=
    funext fun m => propext (alive_congr (G m) j.1 x x' h)
  have c : ∀ m, cutBad (G m) j x = cutBad (G m) j x' := fun m => cutBad_congr (G m) j x x' h
  unfold cutBadF
  rw [e]
  simp only [c]

/-- **At most d j values are bad: the largest degree, not the sum over the family.** -/
theorem cutBadF_count [IsDomain K] [Finite K] {d : Fin n → ℕ} {G : M → (Fin n → K) → K} (hG : ∀ m, DegLE d (G m))
    (j : Fin n) (x : Fin n → K) : Nat.card {t : K // t ∈ cutBadF G j x} ≤ d j :=
  count_first_le (fun m => Alive (G m) j.1 x) (fun m t => t ∈ cutBad (G m) j x) (d j)
    fun m _ => cutBad_count (hG m) j x

/-- **The cut for a family**: if some member is not identically 0 and all members vanish at x, then x has a bad element. -/
theorem cut_covers_family [Finite M] (G : M → (Fin n → K) → K) (hw : ∃ m w, G m w ≠ 0) (x : Fin n → K)
    (hx : ∀ m, G m x = 0) : ∃ j : Fin n, x j ∈ cutBadF G j x := by
  by_contra hno
  have key : ∀ k, k ≤ n → ∃ m, Alive (G m) k x := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨m, hm⟩ := hw
      exact ⟨m, (alive_zero (G m) x).2 hm⟩
    | succ k ih =>
      intro hk
      obtain ⟨m, hm⟩ := exists_isFirst (ih (by omega))
      by_contra h3
      refine hno ⟨⟨k, by omega⟩, m, hm, hm.1, ?_⟩
      rw [Function.update_eq_self]
      exact fun ha => h3 ⟨m, ha⟩
  obtain ⟨m, hm⟩ := key n (Nat.le_refl n)
  exact (alive_full (G m) x).1 hm (hx m)

end Family

/-! ## The same along a list, as a view shows the drawn elements -/

section Along

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The point of a list of elements; 0 behind its end. -/
def ptOf (es : List K) : Fin n → K := fun i => es.getD i.1 0

/-- Bad values by number and point, read behind a list of elements: those of the next element. -/
def alongL (Bad : Fin n → (Fin n → K) → Set K) (xs : List K) : Set K :=
  {t | ∃ h : xs.length < n, t ∈ Bad ⟨xs.length, h⟩ (ptOf xs)}

/-- A bad element of the point of a list is bad behind the members before it. es: what was drawn, n members, read by f. -/
theorem along_list {α : Type*} (f : α → K) (Bad : Fin n → (Fin n → K) → Set K)
    (hc : ∀ j x x', (∀ i : Fin n, i.1 < j.1 → x i = x' i) → Bad j x = Bad j x') (es : List α) (hn : es.length = n)
    (j : Fin n) (hj : ptOf (es.map f) j ∈ Bad j (ptOf (es.map f))) :
    ∃ xs x ys, es = xs ++ x :: ys ∧ f x ∈ alongL Bad (xs.map f) := by
  have hjl : j.1 < es.length := by
    rw [hn]
    exact j.2
  have hsplit : es = es.take j.1 ++ es[j.1] :: es.drop (j.1 + 1) := by
    rw [← List.drop_eq_getElem_cons hjl, List.take_append_drop]
  have hlen : ((es.take j.1).map f).length = j.1 := by
    rw [List.length_map, List.length_take]
    omega
  have hlt : ((es.take j.1).map f).length < n := by
    rw [hlen]
    exact j.2
  refine ⟨_, _, _, hsplit, hlt, ?_⟩
  have e1 : (⟨((es.take j.1).map f).length, hlt⟩ : Fin n) = j := Fin.ext hlen
  have e2 : ∀ i : Fin n, i.1 < j.1 → ptOf ((es.take j.1).map f) i = ptOf (es.map f) i := by
    intro i hi
    show ((es.take j.1).map f).getD i.1 0 = (es.map f).getD i.1 0
    rw [List.map_take, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  have e3 : ptOf (es.map f) j = f es[j.1] := by
    show (es.map f).getD j.1 0 = f es[j.1]
    simp [List.getD_eq_getElem?_getD, hjl]
  rw [e1, hc j _ _ e2, ← e3]
  exact hj

/-- The bad values of the next element behind the elements xs: one function; a family. -/
def cutBadL (g : (Fin n → K) → K) (xs : List K) : Set K := alongL (cutBad g) xs

def cutBadFL {M : Type*} [LinearOrder M] (G : M → (Fin n → K) → K) (xs : List K) : Set K := alongL (cutBadF G) xs

theorem cutBadL_count [IsDomain K] [Finite K] {d : Fin n → ℕ} {g : (Fin n → K) → K} (hg : DegLE d g) (xs : List K)
    (h : xs.length < n) : Nat.card {t : K // t ∈ cutBadL g xs} ≤ d ⟨xs.length, h⟩ :=
  le_trans (count_mono fun _ ht => ht.2) (cutBad_count hg ⟨xs.length, h⟩ (ptOf xs))

theorem cutBadFL_count [IsDomain K] [Finite K] {M : Type*} [LinearOrder M] {d : Fin n → ℕ} {G : M → (Fin n → K) → K}
    (hG : ∀ m, DegLE d (G m)) (xs : List K) (h : xs.length < n) :
    Nat.card {t : K // t ∈ cutBadFL G xs} ≤ d ⟨xs.length, h⟩ :=
  le_trans (count_mono fun _ ht => ht.2) (cutBadF_count hG ⟨xs.length, h⟩ (ptOf xs))

/-- Behind n elements nothing is bad. -/
theorem alongL_empty (Bad : Fin n → (Fin n → K) → Set K) (xs : List K) (h : n ≤ xs.length) (t : K) : t ∉ alongL Bad xs :=
  fun ht => absurd ht.1 (Nat.not_lt.2 h)

/-- **The cut along a list.** If no member is bad behind the members before it, a function that is not identically 0 is not 0 at the
point. -/
theorem cut_covers_list {α : Type*} (f : α → K) (g : (Fin n → K) → K) (hw : ∃ w, g w ≠ 0) (es : List α) (hn : es.length = n)
    (hclean : ∀ xs x ys, es = xs ++ x :: ys → f x ∉ cutBadL g (xs.map f)) : g (ptOf (es.map f)) ≠ 0 := by
  intro hx
  obtain ⟨j, hj⟩ := cut_covers g hw (ptOf (es.map f)) hx
  obtain ⟨xs, x, ys, h1, h2⟩ := along_list f (cutBad g) (cutBad_congr g) es hn j hj
  exact hclean xs x ys h1 h2

/-- The cut along a list of elements themselves, as a «there is»: a zero has a member that is bad behind the members before it. -/
theorem cut_coversL (g : (Fin n → K) → K) (hw : ∃ w, g w ≠ 0) (l : List K) (hl : l.length = n) (hx : g (ptOf l) = 0) :
    ∃ xs x ys, l = xs ++ x :: ys ∧ x ∈ cutBadL g xs := by
  obtain ⟨j, hj⟩ := cut_covers g hw (ptOf l) hx
  have e : l.map id = l := List.map_id l
  obtain ⟨xs, x, ys, h1, h2⟩ := along_list id (cutBad g) (cutBad_congr g) l hl j (by rw [e]; exact hj)
  rw [List.map_id] at h2
  exact ⟨xs, x, ys, h1, h2⟩

/-- **The cut along a list, for a family.** If no member of the list is bad behind the members before it, and some function of the
family is not identically 0, then some function of the family is not 0 at the point. -/
theorem cut_covers_family_list {α M : Type*} [LinearOrder M] [Finite M] (f : α → K) (G : M → (Fin n → K) → K)
    (hw : ∃ m w, G m w ≠ 0) (es : List α) (hn : es.length = n)
    (hclean : ∀ xs x ys, es = xs ++ x :: ys → f x ∉ cutBadFL G (xs.map f)) : ∃ m, G m (ptOf (es.map f)) ≠ 0 := by
  by_contra hx
  obtain ⟨j, hj⟩ := cut_covers_family G hw (ptOf (es.map f)) fun m => by
    by_contra hm
    exact hx ⟨m, hm⟩
  obtain ⟨xs, x, ys, h1, h2⟩ := along_list f (cutBadF G) (cutBadF_congr G) es hn j hj
  exact hclean xs x ys h1 h2

end Along

/-! ## What a round that draws a point owes, and what it then gets -/

section Step

variable {K : Type*} [CommRing K] {n : ℕ}

/-- **The backward step of a round that draws a point.** In: the relation in front of the round. Out: the relation behind it, at the
drawn point x. g is named before the point is drawn. ALIVE: if the relation in front fails, g is not identically 0. DIES: if the relation
behind holds, g is 0 at the point. Then a false front with a true behind has a bad element. -/
theorem cut_step (g : (Fin n → K) → K) (x : Fin n → K) {In Out : Prop} (hAlive : ¬ In → ∃ w, g w ≠ 0)
    (hDies : Out → g x = 0) : Out → ¬ In → ∃ j : Fin n, x j ∈ cutBad g j x :=
  fun ho hi => cut_covers g (hAlive hi) x (hDies ho)

/-- The same, read backward: off the bad values the relation behind gives the relation in front. -/
theorem cut_back (g : (Fin n → K) → K) (x : Fin n → K) {In Out : Prop} (hAlive : ¬ In → ∃ w, g w ≠ 0)
    (hDies : Out → g x = 0) (hclean : ∀ j : Fin n, x j ∉ cutBad g j x) : Out → In := by
  intro ho
  by_contra hi
  obtain ⟨j, hj⟩ := cut_step g x hAlive hDies ho hi
  exact hclean j hj

/-- The step for a family: ALIVE: some member is not identically 0. DIES: all members are 0 at the point. -/
theorem cut_step_family {M : Type*} [LinearOrder M] [Finite M] (G : M → (Fin n → K) → K) (x : Fin n → K) {In Out : Prop}
    (hAlive : ¬ In → ∃ m w, G m w ≠ 0) (hDies : Out → ∀ m, G m x = 0) :
    Out → ¬ In → ∃ j : Fin n, x j ∈ cutBadF G j x :=
  fun ho hi => cut_covers_family G (hAlive hi) x (hDies ho)

theorem cut_back_family {M : Type*} [LinearOrder M] [Finite M] (G : M → (Fin n → K) → K) (x : Fin n → K) {In Out : Prop}
    (hAlive : ¬ In → ∃ m w, G m w ≠ 0) (hDies : Out → ∀ m, G m x = 0) (hclean : ∀ j : Fin n, x j ∉ cutBadF G j x) :
    Out → In := by
  intro ho
  by_contra hi
  obtain ⟨j, hj⟩ := cut_step_family G x hAlive hDies ho hi
  exact hclean j hj

/-- The function 0 buys nothing: it fails ALIVE wherever the relation in front can fail. -/
theorem zero_not_alive {In : Prop} (hi : ¬ In) : ¬ (¬ In → ∃ w : Fin n → K, (fun _ : Fin n → K => (0 : K)) w ≠ 0) := by
  intro H
  obtain ⟨_, hw⟩ := H hi
  exact hw rfl

/-- A constant other than 0 buys nothing: it fails DIES wherever the relation behind can hold. -/
theorem const_not_dies {Out : Prop} (c : K) (hc : c ≠ 0) (x : Fin n → K) (ho : Out) :
    ¬ (Out → (fun _ : Fin n → K => c) x = 0) :=
  fun H => hc (H ho)

end Step

/-! ## As finite sets, for a meaning that names the bad values of each drawn element by a Finset -/

section Fin

variable {K : Type*} [CommRing K] [Fintype K] {n : ℕ}

open Classical in
/-- Bad values behind a list of elements, as a finite set. -/
noncomputable def finOf (Bad : List K → Set K) (xs : List K) : Finset K := univ.filter fun t => t ∈ Bad xs

omit [CommRing K] in
theorem mem_finOf (Bad : List K → Set K) (xs : List K) (t : K) : t ∈ finOf Bad xs ↔ t ∈ Bad xs := by
  classical
  simp [finOf]

omit [CommRing K] in
theorem finOf_card (Bad : List K → Set K) (xs : List K) : (finOf Bad xs).card = Nat.card {t : K // t ∈ Bad xs} := by
  classical
  rw [finOf, count_eq_card_filter]

/-- The bad values of the next element behind the elements xs, as a finite set: one function; a family. -/
noncomputable def cutFin (g : (Fin n → K) → K) (xs : List K) : Finset K := finOf (cutBadL g) xs

noncomputable def cutFinF {M : Type*} [LinearOrder M] (G : M → (Fin n → K) → K) (xs : List K) : Finset K :=
  finOf (cutBadFL G) xs

/-- **The size, at every list**: D: a bound on the degrees by the element's number. Behind n elements or more the set is empty. -/
theorem cutFin_card_le [IsDomain K] {d : Fin n → ℕ} {g : (Fin n → K) → K} (hg : DegLE d g) (D : ℕ → ℕ)
    (hD : ∀ j : Fin n, d j ≤ D j.1) (xs : List K) : (cutFin g xs).card ≤ D xs.length := by
  rw [cutFin, finOf_card]
  by_cases h : xs.length < n
  · exact le_trans (cutBadL_count hg xs h) (hD ⟨xs.length, h⟩)
  · have e : Nat.card {t : K // t ∈ cutBadL g xs} = 0 :=
      count_eq_zero fun t ht => alongL_empty (cutBad g) xs (Nat.not_lt.1 h) t ht
    rw [e]
    exact Nat.zero_le _

theorem cutFinF_card_le [IsDomain K] {M : Type*} [LinearOrder M] {d : Fin n → ℕ} {G : M → (Fin n → K) → K}
    (hG : ∀ m, DegLE d (G m)) (D : ℕ → ℕ) (hD : ∀ j : Fin n, d j ≤ D j.1) (xs : List K) :
    (cutFinF G xs).card ≤ D xs.length := by
  rw [cutFinF, finOf_card]
  by_cases h : xs.length < n
  · exact le_trans (cutBadFL_count hG xs h) (hD ⟨xs.length, h⟩)
  · have e : Nat.card {t : K // t ∈ cutBadFL G xs} = 0 :=
      count_eq_zero fun t ht => alongL_empty (cutBadF G) xs (Nat.not_lt.1 h) t ht
    rw [e]
    exact Nat.zero_le _

/-- **The backward step of a round that draws a point, along the list of what it drew.** es: the drawn elements as they are shown, n of
them, read by f. ALIVE and DIES as in cut_step, DIES at the point of the list. If no member lies in the finite set behind the members
before it, the relation behind gives the relation in front. -/
theorem cut_back_list {α : Type*} (f : α → K) (g : (Fin n → K) → K) (es : List α) (hn : es.length = n) {In Out : Prop}
    (hAlive : ¬ In → ∃ w, g w ≠ 0) (hDies : Out → g (ptOf (es.map f)) = 0)
    (hclean : ∀ xs x ys, es = xs ++ x :: ys → f x ∉ cutFin g (xs.map f)) : Out → In := by
  intro ho
  by_contra hi
  exact cut_covers_list f g (hAlive hi) es hn
    (fun xs x ys h1 h2 => hclean xs x ys h1 ((mem_finOf _ _ _).2 h2)) (hDies ho)

theorem cut_back_family_list {α M : Type*} [LinearOrder M] [Finite M] (f : α → K) (G : M → (Fin n → K) → K) (es : List α)
    (hn : es.length = n) {In Out : Prop} (hAlive : ¬ In → ∃ m w, G m w ≠ 0)
    (hDies : Out → ∀ m, G m (ptOf (es.map f)) = 0)
    (hclean : ∀ xs x ys, es = xs ++ x :: ys → f x ∉ cutFinF G (xs.map f)) : Out → In := by
  intro ho
  by_contra hi
  obtain ⟨m, hm⟩ := cut_covers_family_list f G (hAlive hi) es hn
    (fun xs x ys h1 h2 => hclean xs x ys h1 ((mem_finOf _ _ _).2 h2))
  exact hm (hDies ho m)

end Fin

/-! ## Without a form there is no cut -/

/-- At any two budgets: a rectangle with k₁ + 1 values or more on the first side and k₂ + 1 or more on the second is covered by no family
of at most k₁ bad first elements and, for each first element, at most k₂ bad second elements. -/
theorem no_cut {α : Type*} (k₁ k₂ : ℕ) (A B : Finset α) (hA : k₁ + 1 ≤ A.card) (hB : k₂ + 1 ≤ B.card) (B₁ : Finset α)
    (B₂ : α → Finset α) (h₁ : B₁.card ≤ k₁) (h₂ : ∀ a, (B₂ a).card ≤ k₂) : ¬ ∀ a ∈ A, ∀ b ∈ B, a ∈ B₁ ∨ b ∈ B₂ a := by
  intro H
  have h1 : ∃ a ∈ A, a ∉ B₁ := by
    by_contra hc
    have h3 := Finset.card_le_card (show A ⊆ B₁ from fun a ha => by
      by_contra hn
      exact hc ⟨a, ha, hn⟩)
    omega
  obtain ⟨a, ha, hna⟩ := h1
  have h3 := Finset.card_le_card (show B ⊆ B₂ a from fun b hb => (H a ha b hb).resolve_left hna)
  have h4 := h₂ a
  omega

/-- **A set of pairs within the count of a point of two elements, s |K|, that has no cut at ANY split of the sum s over the two
elements**: the square on s + 1 values, as soon as (s + 1)^2 ≤ s |K|. -/
theorem no_cut_at {K : Type*} [Fintype K] [DecidableEq K] (s : ℕ) (A : Finset K) (hA : A.card = s + 1)
    (hK : (s + 1) * (s + 1) ≤ s * Fintype.card K) :
    ∃ T : Finset (K × K), T.card ≤ s * Fintype.card K ^ (2 - 1) ∧
      ∀ k₁ k₂ : ℕ, k₁ + k₂ = s → ∀ (B₁ : Finset K) (B₂ : K → Finset K), B₁.card ≤ k₁ → (∀ a, (B₂ a).card ≤ k₂) →
        ¬ ∀ p ∈ T, p.1 ∈ B₁ ∨ p.2 ∈ B₂ p.1 := by
  refine ⟨A ×ˢ A, ?_, ?_⟩
  · rw [Finset.card_product, hA]
    simp only [Nat.add_one_sub_one, pow_one]
    exact hK
  · intro k₁ k₂ hs B₁ B₂ h₁ h₂ H
    exact no_cut k₁ k₂ A A (by omega) (by omega) B₁ B₂ h₁ h₂
      fun a ha b hb => H (a, b) (Finset.mem_product.2 ⟨ha, hb⟩)

/-- At the sum 2, the count of a point of two elements of degree 1 each: nine pairs, in every finite type with five values or more: no
cut at 2 | 0, at 1 | 1 or at 0 | 2. -/
theorem no_cut_at_two {K : Type*} [Fintype K] [DecidableEq K] (A : Finset K) (hA : A.card = 3) (hK : 5 ≤ Fintype.card K) :
    ∃ T : Finset (K × K), T.card ≤ 2 * Fintype.card K ^ (2 - 1) ∧
      ∀ k₁ k₂ : ℕ, k₁ + k₂ = 2 → ∀ (B₁ : Finset K) (B₂ : K → Finset K), B₁.card ≤ k₁ → (∀ a, (B₂ a).card ≤ k₂) →
        ¬ ∀ p ∈ T, p.1 ∈ B₁ ∨ p.2 ∈ B₂ p.1 :=
  no_cut_at 2 A hA (by omega)

end Alg

#print axioms Alg.cutBad_congr
#print axioms Alg.cutBad_count
#print axioms Alg.cut_covers
#print axioms Alg.cut_count
#print axioms Alg.cutBadF_congr
#print axioms Alg.cutBadF_count
#print axioms Alg.cut_covers_family
#print axioms Alg.cutBadL_count
#print axioms Alg.cutBadFL_count
#print axioms Alg.cut_covers_list
#print axioms Alg.cut_coversL
#print axioms Alg.cut_covers_family_list
#print axioms Alg.cut_bites
#print axioms Alg.cut_step
#print axioms Alg.cut_back
#print axioms Alg.cut_step_family
#print axioms Alg.cut_back_family
#print axioms Alg.cutFin_card_le
#print axioms Alg.cutFinF_card_le
#print axioms Alg.cut_back_list
#print axioms Alg.cut_back_family_list
#print axioms Alg.zero_not_alive
#print axioms Alg.const_not_dies
#print axioms Alg.no_cut_at
#print axioms Alg.no_cut_at_two
