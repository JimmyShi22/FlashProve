-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TermsLaw.lean: what the functions of
Johnson/Desc/K5/Honest/Terms.lean compute of a summand, READ IN A FIELD. Definitions of
propositions, and statements with their proofs. rho: any reading (OnBytes/Model/HideLaws.lean). No
word is asked to be below the prime: everything is stated through rho.

EVERY STATEMENT ON A ROUND POLYNOMIAL's VALUE IS CONDITIONAL: on one or both of the two duties that
Terms.lean leaves to its caller, which are typed here as propositions. Whoever lays a summand pays
them for that summand.
  `Affine rho n v f`     read, f is of degree at most 1 in coordinate v of n
  `IsExt rho n f`        read, f is the multilinear extension (`Blocks.ext`) of some table
  `isExt_affine`         the second gives the first, at every coordinate
  `Summand.termAt`, `coefAt`, `facAt`   term number t at a point; its coefficient; the value of its
                         factor number j. Beyond the lists: the coefficient 0 and no factor; 0
  `Summand.Uniform`      the number of terms, of each term's factors, and each factor's hidden map
                         do not depend on the point
  `Summand.Tame rho S ds dY`   both duties, and: what lies beyond the first ds[i] coefficients of
                         round i's polynomial, and beyond the first dY + 1 of the polynomial in Y,
                         reads 0
  `Summand.val rho S past`     the partial sum: the sum of the summand over the cube behind `past`
  `Summand.formula`      the summand's formula at a point, on any values in the hidden maps' place
Main statements:
  `read_at`, `at_formula`, `read_total`, `val_nil`, `val_full`: unconditional
  `round_value`          the core: the round polynomial's value at r, where coefficients and factors
                         lie on their lines at r, on the cube behind
  `round_sum`            under Uniform: its values at 0 and at 1 add up to `val past`
  `round_at`             under Uniform and Affine at that variable: its value at r is
                         `val (past ++ [r])`
  `inY_at`, `inY_zero`   unconditional: the polynomial in Y at beta is the formula on each end value
                         plus beta times its mask entry; at 0 it is the summand at the point
  `endsAt_getD`, `Summand.Named`, `formula_congr`   the end values by number; every factor names
                         one of n end values; then the formula reads the values below n alone
  `length_round_le`, `length_inY_le`, `tame_of_isExt`   where no term has more than k factors the
                         two lists have at most k + 2 and k + 1 members: nothing is cut there

Limits. No summand of the protocol is shown to be tame here. Nothing says that a summand is the
verifier's. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Read
import Johnson.Desc.K5.Honest.Law.Poly
import Blocks.ProductBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (valueAt)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## 1 Lists by index -/

namespace Lists

theorem getD_at {α : Type} (d s : α) : ∀ a y : List α, (a ++ s :: y).getD a.length d = s
  | [], _ => rfl
  | x :: a, y => by
    simp only [List.cons_append, List.length_cons, List.getD_cons_succ]
    exact getD_at d s a y

theorem getD_mid {α : Type} (d s s' : α) : ∀ (a y : List α) (i : Nat), i ≠ a.length →
    (a ++ s :: y).getD i d = (a ++ s' :: y).getD i d
  | [], _, 0, h => absurd rfl h
  | [], _, _ + 1, _ => rfl
  | _ :: _, _, 0, _ => rfl
  | x :: a, y, i + 1, h => by
    simp only [List.cons_append, List.getD_cons_succ]
    exact getD_mid d s s' a y i fun e => h (by rw [e, List.length_cons])

theorem sum_map_range {α : Type} (d : α) (g : α → K) : ∀ l : List α,
    (l.map g).sum = ∑ i ∈ Finset.range l.length, g (l.getD i d)
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      sum_map_range d g l]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

theorem prod_map_range {α : Type} (d : α) (g : α → K) : ∀ l : List α,
    (l.map g).prod = ∏ i ∈ Finset.range l.length, g (l.getD i d)
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.prod_cons, List.length_cons, Finset.prod_range_succ',
      prod_map_range d g l]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [mul_comm]

theorem sum_zip_range {α β : Type} (da : α) (db : β) (g : α × β → K) : ∀ (a : List α) (b : List β),
    a.length = b.length →
    ((a.zip b).map g).sum = ∑ i ∈ Finset.range a.length, g (a.getD i da, b.getD i db)
  | [], [], _ => by simp
  | x :: a, y :: b, h => by
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
      Finset.sum_range_succ', sum_zip_range da db g a b (by simpa using h)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem prod_zip_range {α β : Type} (da : α) (db : β) (g : α × β → K) : ∀ (a : List α) (b : List β),
    a.length = b.length →
    ((a.zip b).map g).prod = ∏ i ∈ Finset.range a.length, g (a.getD i da, b.getD i db)
  | [], [], _ => by simp
  | x :: a, y :: b, h => by
    rw [List.zip_cons_cons, List.map_cons, List.prod_cons, List.length_cons,
      Finset.prod_range_succ', prod_zip_range da db g a b (by simpa using h)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [mul_comm]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

end Lists

open Lists

/-! ## 2 Degree at most 1 in a variable -/

/-- **Read, f is of degree at most 1 in coordinate number v, from 0, of n**: at every point its
value lies on the line through its values at 0 and at 1 in that coordinate. -/
def Affine (n v : Nat) (f : List E → E) : Prop :=
  ∀ (a y : List E) (r : E), a.length = v → a.length + 1 + y.length = n →
    ρ.val (f (a ++ r :: y)) =
      (1 - ρ.val r) * ρ.val (f (a ++ zeroE :: y)) + ρ.val r * ρ.val (f (a ++ oneE :: y))

/-- **Read, f is the multilinear extension of some table** on n variables; the first coordinate is
the top bit of the table's index. -/
def IsExt (n : Nat) (f : List E → E) : Prop :=
  ∃ v : ℕ → K, ∀ x : List E, x.length = n →
    ρ.val (f x) = Blocks.ext n v fun i => ρ.val (x.getD i zeroE)

/-- A multilinear extension lies, in each coordinate, on the line through its values at 0 and 1. -/
theorem ext_update : ∀ (n v : Nat) (f p : ℕ → K) (r : K), v < n →
    Blocks.ext n f (Function.update p v r) =
      (1 - r) * Blocks.ext n f (Function.update p v 0) +
        r * Blocks.ext n f (Function.update p v 1)
  | 0, v, _, _, _, h => absurd h (Nat.not_lt_zero v)
  | n + 1, 0, f, p, r, _ => by
    have e : ∀ s : K, Function.update p 0 s = Blocks.consPt s fun t => p (t + 1) := by
      intro s
      funext t
      cases t with
      | zero => simp [Blocks.consPt]
      | succ t => simp [Blocks.consPt]
    rw [e r, e 0, e 1, Blocks.ext_succ_consPt, Blocks.ext_succ_consPt, Blocks.ext_succ_consPt]
    ring
  | n + 1, v + 1, f, p, r, h => by
    have e : ∀ s : K, Function.update p (v + 1) s =
        Blocks.consPt (p 0) (Function.update (fun t => p (t + 1)) v s) := by
      intro s
      funext t
      cases t with
      | zero => simp [Blocks.consPt]
      | succ t =>
        by_cases ht : t = v
        · subst ht
          simp [Blocks.consPt]
        · simp [Blocks.consPt, Function.update, ht]
    rw [e r, e 0, e 1, Blocks.ext_succ_consPt, Blocks.ext_succ_consPt, Blocks.ext_succ_consPt,
      ext_update n v f _ r (by omega), ext_update n v (fun X => f (X + 2 ^ n)) _ r (by omega)]
    ring

/-- **An extension of a table is of degree at most 1 in each coordinate.** -/
theorem isExt_affine {n : Nat} {f : List E → E} (h : IsExt ρ n f) (v : Nat) : Affine ρ n v f := by
  obtain ⟨tb, h⟩ := h
  intro a y r ha hn
  have len : ∀ s : E, (a ++ s :: y).length = n := fun s => by
    rw [List.length_append, List.length_cons]
    omega
  obtain ⟨base, hb⟩ : ∃ b : ℕ → K, b = fun i => ρ.val ((a ++ zeroE :: y).getD i zeroE) := ⟨_, rfl⟩
  have pt : ∀ s : E, (fun i => ρ.val ((a ++ s :: y).getD i zeroE)) =
      Function.update base v (ρ.val s) := by
    intro s
    funext i
    by_cases hi : i = v
    · rw [hi, Function.update_self, ← ha, getD_at]
    · rw [Function.update_of_ne hi, hb]
      exact congrArg ρ.val (getD_mid zeroE s zeroE a y i (by rw [ha]; exact hi))
  rw [h _ (len r), h _ (len zeroE), h _ (len oneE), pt r, pt zeroE, pt oneE, ρ.zero, ρ.one]
  exact ext_update n v tb base (ρ.val r) (by omega)

/-! ## 3 The cube -/

theorem cube_length : ∀ n : Nat, (cube n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    show ((cube n).map (zeroE :: ·) ++ (cube n).map (oneE :: ·)).length = _
    rw [List.length_append, List.length_map, List.length_map, cube_length n]
    omega

theorem length_of_mem_cube : ∀ (n : Nat) (y : List E), y ∈ cube n → y.length = n
  | 0, y, h => by
    rw [List.mem_singleton.1 h]
    rfl
  | n + 1, y, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 h
      rw [List.length_cons, length_of_mem_cube n z hz]
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 h
      rw [List.length_cons, length_of_mem_cube n z hz]

/-! ## 4 The form, read -/

/-- Term number t at a point; beyond the list: the coefficient 0 and no factor. -/
def Summand.termAt (S : Summand) (x : List E) (t : Nat) : Term := (S.terms x).getD t ⟨zeroE, []⟩

/-- The coefficient of term number t, as a function of the point. -/
def Summand.coefAt (S : Summand) (t : Nat) (x : List E) : E := (S.termAt x t).c

/-- The value of factor number j of term number t, as a function of the point: its a, its b and its
hidden map all move with the point. Beyond the list: 0 times a map plus 0. -/
def Summand.facAt (S : Summand) (t j : Nat) (x : List E) : E :=
  S.factorAt x ((S.termAt x t).fs.getD j ⟨zeroE, 0, zeroE⟩)

/-- **The terms' skeleton does not depend on the point**: the number of terms, the number of each
term's factors, and the number of each factor's hidden map. -/
def Summand.Uniform (S : Summand) : Prop :=
  ∀ x y : List E, x.length = S.vars → y.length = S.vars →
    (S.terms x).map (fun t => t.fs.map (·.n)) = (S.terms y).map (fun t => t.fs.map (·.n))

theorem Summand.Uniform.terms {S : Summand} (h : S.Uniform) {x y : List E} (hx : x.length = S.vars)
    (hy : y.length = S.vars) : (S.terms x).length = (S.terms y).length := by
  have := congrArg List.length (h x y hx hy)
  rwa [List.length_map, List.length_map] at this

theorem Summand.Uniform.factors {S : Summand} (h : S.Uniform) {x y : List E}
    (hx : x.length = S.vars) (hy : y.length = S.vars) (t : Nat) :
    (S.termAt x t).fs.length = (S.termAt y t).fs.length := by
  have e : ∀ l : List Term, ((l.map fun t => t.fs.map (·.n)).getD t []).length =
      (l.getD t ⟨zeroE, []⟩).fs.length := by
    intro l
    have := List.getD_map (l := l) (d := (⟨zeroE, []⟩ : Term)) (n := t) fun t => t.fs.map (·.n)
    rw [show ([] : List Nat) = (fun t : Term => t.fs.map (·.n)) ⟨zeroE, []⟩ from rfl, this,
      List.length_map]
  unfold Summand.termAt
  rw [← e, ← e, h x y hx hy]

/-- **The summand's formula** at the point x, with e n in the place of the hidden map number n. -/
def Summand.formula (S : Summand) (x : List E) (e : Nat → K) : K :=
  ((S.terms x).map fun t =>
    ρ.val t.c * (t.fs.map fun f => ρ.val f.a * e f.n + ρ.val f.b).prod).sum

theorem read_factorAt (S : Summand) (x : List E) (f : Factor) :
    ρ.val (S.factorAt x f) = ρ.val f.a * ρ.val (S.endAt x f.n) + ρ.val f.b := by
  unfold Summand.factorAt
  rw [ρ.add, ρ.mul]

/-- A fold that multiplies by g f for each member f of a list, from c on. -/
theorem read_foldl_mul {α : Type} (g : α → E) : ∀ (l : List α) (c : E),
    ρ.val (l.foldl (fun p f => mulE p (g f)) c) = ρ.val c * (l.map fun f => ρ.val (g f)).prod
  | [], c => by simp
  | x :: l, c => by
    rw [List.foldl_cons, read_foldl_mul g l, ρ.mul, List.map_cons, List.prod_cons, mul_assoc]

/-- **The summand at a point**: the sum over the terms of the coefficient times the factors. -/
theorem Summand.read_at (S : Summand) (x : List E) : ρ.val (S.at x) =
    ((S.terms x).map fun t => ρ.val t.c * (t.fs.map fun f => ρ.val (S.factorAt x f)).prod).sum := by
  unfold Summand.at
  rw [read_sumE, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun t _ => read_foldl_mul ρ _ _ _)

/-- The summand at a point is its formula on the hidden maps' values there. -/
theorem Summand.at_formula (S : Summand) (x : List E) :
    ρ.val (S.at x) = S.formula ρ x fun n => ρ.val (S.endAt x n) := by
  rw [S.read_at ρ x]
  unfold Summand.formula
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  exact congrArg (ρ.val t.c * ·)
    (congrArg List.prod (List.map_congr_left fun f _ => read_factorAt ρ S x f))

/-- The sum over the whole cube. -/
theorem Summand.read_total (S : Summand) :
    ρ.val S.total = ((cube S.vars).map fun y => ρ.val (S.at y)).sum := by
  unfold Summand.total
  rw [read_sumE, List.map_map]
  rfl

/-! ## 5 Partial sums -/

/-- **The partial sum** behind the challenges `past`: the sum of the summand over all points that
begin with `past` and go on with zeros and ones. -/
def Summand.val (S : Summand) (past : List E) : K :=
  ((cube (S.vars - past.length)).map fun y => ρ.val (S.at (past ++ y))).sum

theorem Summand.val_nil (S : Summand) : S.val ρ [] = ρ.val S.total := by
  rw [S.read_total ρ]
  rfl

theorem Summand.val_full (S : Summand) (rs : List E) (h : rs.length = S.vars) :
    S.val ρ rs = ρ.val (S.at rs) := by
  unfold Summand.val
  rw [h, Nat.sub_self]
  show ([[]].map fun y => ρ.val (S.at (rs ++ y))).sum = _
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.append_nil]

/-- A partial sum splits at the next variable's 0 and 1. -/
theorem Summand.val_split (S : Summand) (rs : List E) (h : rs.length < S.vars) :
    S.val ρ rs =
      ((cube (S.vars - rs.length - 1)).map fun y => ρ.val (S.at (rs ++ zeroE :: y))).sum +
      ((cube (S.vars - rs.length - 1)).map fun y => ρ.val (S.at (rs ++ oneE :: y))).sum := by
  unfold Summand.val
  obtain ⟨n, hn⟩ : ∃ n, S.vars - rs.length = n + 1 := ⟨S.vars - rs.length - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel]
  show (((cube n).map (zeroE :: ·) ++ (cube n).map (oneE :: ·)).map _).sum = _
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  rfl

/-- The partial sum behind one challenge more. -/
theorem Summand.val_snoc (S : Summand) (rs : List E) (r : E) :
    S.val ρ (rs ++ [r]) =
      ((cube (S.vars - rs.length - 1)).map fun y => ρ.val (S.at (rs ++ r :: y))).sum := by
  unfold Summand.val
  rw [List.length_append, List.length_singleton, Nat.sub_add_eq]
  refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
  rw [List.append_assoc]
  rfl

/-! ## 6 The round polynomial -/

/-- A fold that multiplies by the list g f for each member f, from p on: its value at a point. -/
theorem value_foldl_mulP {α : Type} (g : α → List E) (x : E) : ∀ (l : List α) (p : List E),
    ρ.val (valueAt (l.foldl (fun p f => mulP p (g f)) p) x) =
      ρ.val (valueAt p x) * (l.map fun f => ρ.val (valueAt (g f) x)).prod
  | [], p => by simp
  | f :: l, p => by
    rw [List.foldl_cons, value_foldl_mulP g x l, value_mulP, List.map_cons, List.prod_cons,
      mul_assoc]

/-- A term's polynomial at r: the product of the lines' values. -/
theorem Summand.value_termLine (S : Summand) (x0 x1 : List E) (t0 t1 : Term) (r : E) :
    ρ.val (valueAt (S.termLine x0 x1 t0 t1) r) =
      ((1 - ρ.val r) * ρ.val t0.c + ρ.val r * ρ.val t1.c) *
        ((t0.fs.zip t1.fs).map fun f =>
          (1 - ρ.val r) * ρ.val (S.factorAt x0 f.1) +
            ρ.val r * ρ.val (S.factorAt x1 f.2)).prod := by
  unfold Summand.termLine
  rw [value_foldl_mulP ρ (fun f : Factor × Factor => lineP (S.factorAt x0 f.1) (S.factorAt x1 f.2)),
    value_lineP]
  exact congrArg _ (congrArg List.prod (List.map_congr_left fun f _ => value_lineP ρ _ _ _))

/-- Where, at a third point x, every coefficient and every factor lies at r on the line through its
values at x0 and x1, and the three points have terms and factors in the same numbers, the terms'
lines at r add up to the summand at x. -/
theorem Summand.lines_at (S : Summand) (x0 x1 x : List E) (r : K)
    (hT1 : (S.terms x0).length = (S.terms x1).length)
    (hT : (S.terms x0).length = (S.terms x).length)
    (hF1 : ∀ t, (S.termAt x0 t).fs.length = (S.termAt x1 t).fs.length)
    (hF : ∀ t, (S.termAt x0 t).fs.length = (S.termAt x t).fs.length)
    (hc : ∀ t, ρ.val (S.coefAt t x) =
      (1 - r) * ρ.val (S.coefAt t x0) + r * ρ.val (S.coefAt t x1))
    (hf : ∀ t j, ρ.val (S.facAt t j x) =
      (1 - r) * ρ.val (S.facAt t j x0) + r * ρ.val (S.facAt t j x1)) :
    (((S.terms x0).zip (S.terms x1)).map fun t : Term × Term =>
      ((1 - r) * ρ.val t.1.c + r * ρ.val t.2.c) *
        ((t.1.fs.zip t.2.fs).map fun f : Factor × Factor =>
          (1 - r) * ρ.val (S.factorAt x0 f.1) + r * ρ.val (S.factorAt x1 f.2)).prod).sum =
      ρ.val (S.at x) := by
  rw [S.read_at ρ x, sum_zip_range ⟨zeroE, []⟩ ⟨zeroE, []⟩ _ _ _ hT1,
    sum_map_range ⟨zeroE, []⟩, ← hT]
  refine Finset.sum_congr rfl fun t _ => ?_
  show ((1 - r) * ρ.val (S.coefAt t x0) + r * ρ.val (S.coefAt t x1)) *
      (((S.termAt x0 t).fs.zip (S.termAt x1 t).fs).map fun f : Factor × Factor =>
        (1 - r) * ρ.val (S.factorAt x0 f.1) + r * ρ.val (S.factorAt x1 f.2)).prod =
    ρ.val (S.coefAt t x) * ((S.termAt x t).fs.map fun f => ρ.val (S.factorAt x f)).prod
  rw [← hc t, prod_zip_range ⟨zeroE, 0, zeroE⟩ ⟨zeroE, 0, zeroE⟩ _ _ _ (hF1 t),
    prod_map_range ⟨zeroE, 0, zeroE⟩, ← hF t]
  exact congrArg _ (Finset.prod_congr rfl fun j _ => (hf t j).symm)

/-- **The round polynomial's value at r**, CONDITIONAL on: the skeleton does not depend on the
point; on the cube behind, every coefficient and every factor lies at r on the line through its
values at 0 and at 1 in the round's variable. Then the value is the sum of the summand over the cube
behind r. -/
theorem Summand.round_value (S : Summand) (hU : S.Uniform) (rs : List E) (r : E)
    (h : rs.length < S.vars)
    (hc : ∀ t, ∀ y ∈ cube (S.vars - rs.length - 1), ρ.val (S.coefAt t (rs ++ r :: y)) =
      (1 - ρ.val r) * ρ.val (S.coefAt t (rs ++ zeroE :: y)) +
        ρ.val r * ρ.val (S.coefAt t (rs ++ oneE :: y)))
    (hf : ∀ t j, ∀ y ∈ cube (S.vars - rs.length - 1), ρ.val (S.facAt t j (rs ++ r :: y)) =
      (1 - ρ.val r) * ρ.val (S.facAt t j (rs ++ zeroE :: y)) +
        ρ.val r * ρ.val (S.facAt t j (rs ++ oneE :: y))) :
    ρ.val (valueAt (S.round rs) r) =
      ((cube (S.vars - rs.length - 1)).map fun y => ρ.val (S.at (rs ++ r :: y))).sum := by
  unfold Summand.round
  rw [value_sumP, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
  have len : ∀ s : E, (rs ++ s :: y).length = S.vars := fun s => by
    rw [List.length_append, List.length_cons, length_of_mem_cube _ y hy]
    omega
  show ρ.val (valueAt (sumP (((S.terms (rs ++ zeroE :: y)).zip (S.terms (rs ++ oneE :: y))).map
    fun t => S.termLine (rs ++ zeroE :: y) (rs ++ oneE :: y) t.1 t.2)) r) = _
  rw [value_sumP, List.map_map, ← S.lines_at ρ (rs ++ zeroE :: y) (rs ++ oneE :: y) (rs ++ r :: y)
    (ρ.val r) (hU.terms (len _) (len _)) (hU.terms (len _) (len _))
    (hU.factors (len _) (len _)) (hU.factors (len _) (len _)) (fun t => hc t y hy)
    fun t j => hf t j y hy]
  exact congrArg List.sum (List.map_congr_left fun t _ => S.value_termLine ρ _ _ _ _ r)

/-- **The round polynomial's values at 0 and at 1 add up to the partial sum in front of it**,
CONDITIONAL on: the skeleton does not depend on the point. -/
theorem Summand.round_sum (S : Summand) (hU : S.Uniform) (rs : List E) (h : rs.length < S.vars) :
    ρ.val (valueAt (S.round rs) zeroE) + ρ.val (valueAt (S.round rs) oneE) = S.val ρ rs := by
  rw [S.val_split ρ rs h,
    S.round_value ρ hU rs zeroE h (fun t y _ => by rw [ρ.zero]; ring)
      (fun t j y _ => by rw [ρ.zero]; ring),
    S.round_value ρ hU rs oneE h (fun t y _ => by rw [ρ.one]; ring)
      (fun t j y _ => by rw [ρ.one]; ring)]

/-- **The round polynomial's value at the challenge r is the next partial sum**, CONDITIONAL on: the
skeleton does not depend on the point; every coefficient and every factor is of degree at most 1 in
the round's variable. -/
theorem Summand.round_at (S : Summand) (hU : S.Uniform) (rs : List E) (r : E)
    (h : rs.length < S.vars) (hc : ∀ t, Affine ρ S.vars rs.length (S.coefAt t))
    (hf : ∀ t j, Affine ρ S.vars rs.length (S.facAt t j)) :
    ρ.val (valueAt (S.round rs) r) = S.val ρ (rs ++ [r]) := by
  have len : ∀ y ∈ cube (S.vars - rs.length - 1), rs.length + 1 + y.length = S.vars :=
    fun y hy => by
      rw [length_of_mem_cube _ y hy]
      omega
  rw [S.val_snoc ρ rs r]
  exact S.round_value ρ hU rs r h (fun t y hy => hc t rs y r rfl (len y hy))
    fun t j y hy => hf t j rs y r rfl (len y hy)

/-! ## 7 The polynomial in Y -/

/-- **The polynomial in Y at beta is the summand's formula on each end value plus beta times its
mask entry.** Unconditional. -/
theorem Summand.inY_at (S : Summand) (rs m : List E) (beta : E) :
    ρ.val (valueAt (S.inY rs m) beta) =
      S.formula ρ rs fun n => ρ.val (S.endAt rs n) + ρ.val beta * ρ.val (m.getD n zeroE) := by
  unfold Summand.inY Summand.formula
  rw [value_sumP, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show ρ.val (valueAt (t.fs.foldl
    (fun p f => mulP p [S.factorAt rs f, mulE f.a (m.getD f.n zeroE)]) [t.c]) beta) = _
  rw [value_foldl_mulP ρ (fun f : Factor => [S.factorAt rs f, mulE f.a (m.getD f.n zeroE)]),
    value_single]
  refine congrArg _ (congrArg List.prod (List.map_congr_left fun f _ => ?_))
  rw [value_pair, read_factorAt, ρ.mul]
  ring

/-- At Y = 0 it is the summand at the point. Unconditional. -/
theorem Summand.inY_zero (S : Summand) (rs m : List E) :
    ρ.val (valueAt (S.inY rs m) zeroE) = ρ.val (S.at rs) := by
  rw [S.inY_at ρ rs m zeroE, S.at_formula ρ rs, ρ.zero]
  simp only [zero_mul, add_zero]

/-! ## 8 The end values and the factors' numbers -/

theorem Summand.length_endsAt (S : Summand) (rs : List E) : (S.endsAt rs).length = S.ends := by
  unfold Summand.endsAt
  rw [List.length_map, List.length_range]

/-- End value number j is the hidden map number j at the point. -/
theorem Summand.endsAt_getD (S : Summand) (rs : List E) (j : Nat) (h : j < S.ends) :
    (S.endsAt rs).getD j zeroE = S.endAt rs j := by
  unfold Summand.endsAt
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h),
    List.getElem_map, List.getElem_range]

/-- **The summand has n end values, and every factor names one of them.** Beside `Tame`: for a
caller that spends a statement on the n end values that are sent. Whoever lays the summand pays it.
-/
structure Summand.Named (S : Summand) (n : Nat) : Prop where
  /-- the number of end values -/
  ends : S.ends = n
  /-- each factor's hidden map has a number below it -/
  below : ∀ x : List E, x.length = S.vars → ∀ t ∈ S.terms x, ∀ f ∈ t.fs, f.n < n

/-- The formula reads the values at the factors' numbers alone. -/
theorem Summand.formula_congr (S : Summand) (x : List E) (e e' : Nat → K)
    (h : ∀ t ∈ S.terms x, ∀ f ∈ t.fs, e f.n = e' f.n) : S.formula ρ x e = S.formula ρ x e' := by
  unfold Summand.formula
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  refine congrArg _ (congrArg List.prod (List.map_congr_left fun f hf => ?_))
  rw [h t ht f hf]

/-- Where every factor names one of n end values, the formula reads the values below n alone. -/
theorem Summand.Named.formula_congr {S : Summand} {n : Nat} (hN : S.Named n) (x : List E)
    (hx : x.length = S.vars) (e e' : Nat → K) (h : ∀ j, j < n → e j = e' j) :
    S.formula ρ x e = S.formula ρ x e' :=
  S.formula_congr ρ x e e' fun t ht f hf => h f.n (hN.below x hx t ht f hf)

/-! ## 9 Lengths -/

theorem length_mulP_two (a b : List E) (ha : a ≠ []) (hb : b.length = 2) :
    (mulP a b).length = a.length + 1 := by
  match b, hb with
  | [u, s], _ => exact length_mulP_pair a u s ha

/-- A fold that multiplies by a list of two members for each member of l has l.length members
more. -/
theorem length_foldl_mulP {α : Type} (g : α → List E) (hg : ∀ f, (g f).length = 2) :
    ∀ (l : List α) (p : List E), p ≠ [] →
      (l.foldl (fun p f => mulP p (g f)) p).length = p.length + l.length
  | [], _, _ => rfl
  | f :: l, p, hp => by
    have h1 := length_mulP_two p (g f) hp (hg f)
    rw [List.foldl_cons, length_foldl_mulP g hg l _ (fun e => by rw [e] at h1; simp at h1), h1,
      List.length_cons]
    omega

theorem Summand.length_termLine (S : Summand) (x0 x1 : List E) (t0 t1 : Term) :
    (S.termLine x0 x1 t0 t1).length = 2 + min t0.fs.length t1.fs.length := by
  unfold Summand.termLine
  rw [length_foldl_mulP (fun f : Factor × Factor => lineP (S.factorAt x0 f.1) (S.factorAt x1 f.2))
    (fun _ => rfl) _ _ (by simp [lineP]), List.length_zip]
  rfl

/-- Where no term has more than k factors, a round polynomial has at most k + 2 coefficients. -/
theorem Summand.length_round_le (S : Summand) (k : Nat)
    (hk : ∀ x, ∀ t ∈ S.terms x, t.fs.length ≤ k) (rs : List E) : (S.round rs).length ≤ k + 2 := by
  unfold Summand.round
  refine length_sumP_le _ _ fun g hg => ?_
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hg
  refine length_sumP_le _ _ fun g hg => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hg
  rw [S.length_termLine]
  have := hk _ t.1 (List.of_mem_zip ht).1
  omega

/-- Where no term at the point has more than k factors, the polynomial in Y has at most k + 1
coefficients. -/
theorem Summand.length_inY_le (S : Summand) (k : Nat) (rs m : List E)
    (hk : ∀ t ∈ S.terms rs, t.fs.length ≤ k) : (S.inY rs m).length ≤ k + 1 := by
  unfold Summand.inY
  refine length_sumP_le _ _ fun g hg => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hg
  rw [length_foldl_mulP (fun f : Factor => [S.factorAt rs f, mulE f.a (m.getD f.n zeroE)])
    (fun _ => rfl) _ _ (by simp)]
  have := hk t ht
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## 10 A tame summand -/

/-- **A tame summand**: what a sumcheck with the numbers of coefficients ds, and dY + 1 in Y, asks
of its summand. Whoever lays the summand pays all six clauses. The clauses `coef` and `fact` say
nothing at a number v that is not below the number of variables, and beyond the lists of terms and
factors they speak of values that read 0. -/
structure Summand.Tame (S : Summand) (ds : List Nat) (dY : Nat) : Prop where
  /-- as many variables as the sumcheck has -/
  vars : ds.length = S.vars
  /-- the skeleton does not depend on the point -/
  uniform : S.Uniform
  /-- each coefficient is of degree at most 1 in each variable -/
  coef : ∀ v t, Affine ρ S.vars v (S.coefAt t)
  /-- each factor's value, a times its hidden map plus b taken as a whole, is of degree at most 1 in
  each variable; nothing is asked of a, of b or of the map alone -/
  fact : ∀ v t j, Affine ρ S.vars v (S.facAt t j)
  /-- what a sender that keeps ds[i] coefficients of round i's polynomial drops reads 0 -/
  cut : ∀ rs : List E, rs.length < S.vars → ∀ j, ds.getD rs.length 0 ≤ j →
    ρ.val ((S.round rs).getD j zeroE) = 0
  /-- the like in Y -/
  cutY : ∀ rs m : List E, rs.length = S.vars → ∀ j, dY + 1 ≤ j →
    ρ.val ((S.inY rs m).getD j zeroE) = 0

/-- **Tame by extensions and lengths**, CONDITIONAL on: the skeleton does not depend on the point;
each coefficient and each factor's value reads as the extension of a table; no term has more than k
factors; every variable has at least k + 2 coefficients and Y at least k + 1. Then nothing is cut.
-/
theorem tame_of_isExt (S : Summand) (ds : List Nat) (dY k : Nat) (hv : ds.length = S.vars)
    (hU : S.Uniform) (hc : ∀ t, IsExt ρ S.vars (S.coefAt t))
    (hf : ∀ t j, IsExt ρ S.vars (S.facAt t j)) (hk : ∀ x, ∀ t ∈ S.terms x, t.fs.length ≤ k)
    (hd : ∀ d ∈ ds, k + 2 ≤ d) (hY : k ≤ dY) : S.Tame ρ ds dY where
  vars := hv
  uniform := hU
  coef := fun v t => isExt_affine ρ (hc t) v
  fact := fun v t j => isExt_affine ρ (hf t j) v
  cut := fun rs hrs j hj => by
    refine read_beyond ρ _ j (Nat.le_trans (S.length_round_le k hk rs) ?_)
    have hlt : rs.length < ds.length := by rw [hv]; exact hrs
    have hm : ds.getD rs.length 0 ∈ ds := by
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    exact Nat.le_trans (hd _ hm) hj
  cutY := fun rs m _ j hj =>
    read_beyond ρ _ j (Nat.le_trans (S.length_inY_le k rs m (hk rs)) (by omega))

end H2K5.Honest

#print axioms H2K5.Honest.Lists.getD_at
#print axioms H2K5.Honest.Lists.getD_mid
#print axioms H2K5.Honest.Lists.sum_map_range
#print axioms H2K5.Honest.Lists.prod_map_range
#print axioms H2K5.Honest.Lists.sum_zip_range
#print axioms H2K5.Honest.Lists.prod_zip_range
#print axioms H2K5.Honest.ext_update
#print axioms H2K5.Honest.isExt_affine
#print axioms H2K5.Honest.cube_length
#print axioms H2K5.Honest.length_of_mem_cube
#print axioms H2K5.Honest.Summand.Uniform.terms
#print axioms H2K5.Honest.Summand.Uniform.factors
#print axioms H2K5.Honest.read_factorAt
#print axioms H2K5.Honest.read_foldl_mul
#print axioms H2K5.Honest.Summand.read_at
#print axioms H2K5.Honest.Summand.at_formula
#print axioms H2K5.Honest.Summand.read_total
#print axioms H2K5.Honest.Summand.val_nil
#print axioms H2K5.Honest.Summand.val_full
#print axioms H2K5.Honest.Summand.val_split
#print axioms H2K5.Honest.Summand.val_snoc
#print axioms H2K5.Honest.value_foldl_mulP
#print axioms H2K5.Honest.Summand.value_termLine
#print axioms H2K5.Honest.Summand.lines_at
#print axioms H2K5.Honest.Summand.round_value
#print axioms H2K5.Honest.Summand.round_sum
#print axioms H2K5.Honest.Summand.round_at
#print axioms H2K5.Honest.Summand.inY_at
#print axioms H2K5.Honest.Summand.inY_zero
#print axioms H2K5.Honest.Summand.length_endsAt
#print axioms H2K5.Honest.Summand.endsAt_getD
#print axioms H2K5.Honest.Summand.formula_congr
#print axioms H2K5.Honest.Summand.Named.formula_congr
#print axioms H2K5.Honest.length_mulP_two
#print axioms H2K5.Honest.length_foldl_mulP
#print axioms H2K5.Honest.Summand.length_termLine
#print axioms H2K5.Honest.Summand.length_round_le
#print axioms H2K5.Honest.Summand.length_inY_le
#print axioms H2K5.Honest.tame_of_isExt
