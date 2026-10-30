-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyDegrees.lean: degrees in each coordinate, and the sum under equality weights.

OnBytes/Slice/KeyTowerOf.lean builds a tower for every function on lists that is, in each
coordinate, a polynomial with few enough coefficients (PolyIn). This file has the tools to show that
of a summand, and to say what the tower's sum is.

Degrees. Dg k n f says: at lists of n elements, f is in its coordinate number i a polynomial of
degree at most k i. Constants, sums, multiples and products have the degrees that one expects
(Dg.const, add, cmul, mul), a bound can be raised (Dg.mono), and a multilinear map has the degree 1
in each coordinate (dg_of_ml). Two functions that a summand is made of: a map at the first n
coordinates of a longer list (dg_take), and the last coordinate (dg_last).

The sum. Under equality weights at the coordinates of a point the sum over all variables is the
multilinear extension, at that point, of the function's table (sumN_equality). A last variable that
is summed by reading at 0 puts 0 in the last place (sumN_equality_zero).

Main definitions: IsPoly, Dg.

Main theorems: IsPoly.const, add, mul, mono, affine; Dg.congr, const, add, cmul, mul, mono;
dg_of_ml, dg_take, dg_last, polyIn_of_dg, sumN_equality, sumN_equality_zero.

Not claimed. Anything on a given summand.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyTowerOf
import OnBytes.Slice.KeyTreeMaps

set_option autoImplicit false

namespace OnBytes.Slice.PscF
open Prob Cb Polynomial

/-! ## Polynomials in one variable -/

/-- h is a polynomial of degree at most k. -/
def IsPoly (k : ℕ) (h : GE → GE) : Prop := ∃ p : GE[X], p.natDegree ≤ k ∧ ∀ x, h x = p.eval x

/-- A constant. -/
theorem IsPoly.const (k : ℕ) (c : GE) : IsPoly k fun _ => c :=
  ⟨C c, by rw [natDegree_C]; exact Nat.zero_le k, fun _ => eval_C.symm⟩

/-- A bound can be raised. -/
theorem IsPoly.mono {k l : ℕ} {h : GE → GE} (hkl : k ≤ l) (hh : IsPoly k h) : IsPoly l h := by
  obtain ⟨p, hp, he⟩ := hh
  exact ⟨p, le_trans hp hkl, he⟩

/-- A sum. -/
theorem IsPoly.add {k : ℕ} {h g : GE → GE} (hh : IsPoly k h) (hg : IsPoly k g) :
    IsPoly k fun x => h x + g x := by
  obtain ⟨p, hp, he⟩ := hh
  obtain ⟨r, hr, hf⟩ := hg
  exact ⟨p + r, natDegree_add_le_of_degree_le hp hr, fun x => by
    rw [eval_add, ← he x, ← hf x]⟩

/-- A product. -/
theorem IsPoly.mul {k l : ℕ} {h g : GE → GE} (hh : IsPoly k h) (hg : IsPoly l g) :
    IsPoly (k + l) fun x => h x * g x := by
  obtain ⟨p, hp, he⟩ := hh
  obtain ⟨r, hr, hf⟩ := hg
  exact ⟨p * r, natDegree_mul_le_of_le hp hr, fun x => by
    rw [eval_mul, ← he x, ← hf x]⟩

/-- (1 - x) a + x b. -/
theorem IsPoly.affine (a b : GE) : IsPoly 1 fun x => (1 - x) * a + x * b :=
  ⟨C (b - a) * X + C a, natDegree_linear_le, fun x => by
    rw [eval_add, eval_mul, eval_C, eval_C, eval_X]
    ring⟩

/-- The variable itself. -/
theorem IsPoly.id : IsPoly 1 fun x => x := ⟨X, natDegree_X_le, fun _ => eval_X.symm⟩

/-! ## Degrees in each coordinate -/

/-- At lists of n elements, f is in coordinate number i a polynomial of degree at most k i. -/
def Dg : (ℕ → ℕ) → ℕ → (List GE → GE) → Prop
  | _, 0, _ => True
  | k, n + 1, f =>
    (∀ q, q.length = n → IsPoly (k 0) fun x => f (x :: q)) ∧
      ∀ x, Dg (fun i => k (i + 1)) n fun q => f (x :: q)

/-- The property reads f at lists of n elements alone. -/
theorem Dg.congr : ∀ {n : ℕ} {k : ℕ → ℕ} {f f' : List GE → GE},
    (∀ q, q.length = n → f q = f' q) → Dg k n f → Dg k n f'
  | 0, _, _, _, _, _ => trivial
  | n + 1, _, _, _, h, hf =>
    ⟨fun q hq => by
        obtain ⟨p, hp, he⟩ := hf.1 q hq
        exact ⟨p, hp, fun x => (h (x :: q) (congrArg (· + 1) hq)).symm.trans (he x)⟩,
      fun x => Dg.congr (fun q hq => h (x :: q) (congrArg (· + 1) hq)) (hf.2 x)⟩

/-- A constant. -/
theorem Dg.const (c : GE) : ∀ (n : ℕ) (k : ℕ → ℕ), Dg k n fun _ => c
  | 0, _ => trivial
  | n + 1, _ => ⟨fun _ _ => IsPoly.const _ c, fun _ => Dg.const c n _⟩

/-- A bound can be raised. -/
theorem Dg.mono : ∀ {n : ℕ} {k l : ℕ → ℕ} {f : List GE → GE}, (∀ i, i < n → k i ≤ l i) →
    Dg k n f → Dg l n f
  | 0, _, _, _, _, _ => trivial
  | n + 1, _, _, _, h, hf =>
    ⟨fun q hq => (hf.1 q hq).mono (h 0 (Nat.succ_pos n)),
      fun x => Dg.mono (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)) (hf.2 x)⟩

/-- A sum. -/
theorem Dg.add : ∀ {n : ℕ} {k : ℕ → ℕ} {f g : List GE → GE}, Dg k n f → Dg k n g →
    Dg k n fun q => f q + g q
  | 0, _, _, _, _, _ => trivial
  | _ + 1, _, _, _, hf, hg =>
    ⟨fun q hq => (hf.1 q hq).add (hg.1 q hq), fun x => Dg.add (hf.2 x) (hg.2 x)⟩

/-- A product. -/
theorem Dg.mul : ∀ {n : ℕ} {k l : ℕ → ℕ} {f g : List GE → GE}, Dg k n f → Dg l n g →
    Dg (fun i => k i + l i) n fun q => f q * g q
  | 0, _, _, _, _, _, _ => trivial
  | _ + 1, _, _, _, _, hf, hg =>
    ⟨fun q hq => (hf.1 q hq).mul (hg.1 q hq), fun x => Dg.mul (hf.2 x) (hg.2 x)⟩

/-- A multiple. -/
theorem Dg.cmul (a : GE) {n : ℕ} {k : ℕ → ℕ} {f : List GE → GE} (hf : Dg k n f) :
    Dg k n fun q => a * f q :=
  Dg.mono (fun i _ => le_of_eq (Nat.zero_add (k i))) (Dg.mul (Dg.const a n fun _ => 0) hf)

/-- A multilinear map has the degree 1 in each coordinate. -/
theorem dg_of_ml : ∀ {n : ℕ} {F : List GE → GE}, ML n F → Dg (fun _ => 1) n F
  | 0, _, _ => trivial
  | n + 1, F, h =>
    ⟨fun q hq => by
        obtain ⟨p, hp, he⟩ := IsPoly.affine (F (0 :: q)) (F (1 :: q))
        exact ⟨p, hp, fun x => (h.1 x q hq).trans (he x)⟩,
      fun x => dg_of_ml (h.2 x)⟩

/-- A map at the first n coordinates of a list of n + 1 elements. -/
theorem dg_take : ∀ {n : ℕ} {k : ℕ → ℕ} {V : List GE → GE}, Dg k n V →
    Dg k (n + 1) fun γ => V (γ.take n)
  | 0, _, V, _ => ⟨fun _ _ => IsPoly.const _ (V []), fun _ => trivial⟩
  | n + 1, _, V, h =>
    ⟨fun q hq => by
        show IsPoly _ fun x => V (x :: q.take n)
        exact h.1 (q.take n) (by rw [List.length_take, hq]; exact Nat.min_eq_left (Nat.le_succ n)),
      fun x => dg_take (h.2 x)⟩

/-- The last coordinate of a list of n + 1 elements. -/
theorem dg_last : ∀ n : ℕ, Dg (fun _ => 1) (n + 1) fun γ => γ.getLast?.getD 0
  | 0 => ⟨fun q hq => by
      rw [List.length_eq_zero_iff.1 hq]
      exact IsPoly.id, fun _ => trivial⟩
  | n + 1 =>
    ⟨fun q hq => by
        cases q with
        | nil => cases hq
        | cons y q => exact IsPoly.const _ _,
      fun x => Dg.congr (f := fun γ => γ.getLast?.getD 0) (fun q hq => by
        cases q with
        | nil => cases hq
        | cons y q => rfl) (dg_last n)⟩

/-- From degrees to what a tower asks. -/
theorem polyIn_of_dg : ∀ (ws : List Weight) {k : ℕ → ℕ} {f : List GE → GE},
    (∀ i (h : i < ws.length), k i < ws[i].d) → Dg k ws.length f → PolyIn ws f
  | [], _, _, _, _ => trivial
  | w :: ws, _, _, h, hf =>
    ⟨fun q hq => by
        obtain ⟨p, hp, he⟩ := hf.1 q hq
        exact ⟨p, lt_of_le_of_lt hp (h 0 (Nat.succ_pos _)), he⟩,
      fun x => polyIn_of_dg ws (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)) (hf.2 x)⟩

/-! ## The sum under equality weights -/

/-- Under equality weights at the coordinates of a point, the sum over all variables is the
extension of the function's table at that point. l: for each variable its coordinate and the
number of coefficients of its polynomials. -/
theorem sumN_equality : ∀ (l : List (GE × ℕ)) (f : List GE → GE), (∀ p ∈ l, 2 ≤ p.2) →
    sumN (l.map fun p => Weight.equality p.1 p.2) f = ext l.length f (l.map (·.1))
  | [], _, _ => rfl
  | p :: l, f, h => by
    obtain ⟨_, ha, hb⟩ := equality_twoNode p.1 p.2 (h p List.mem_cons_self)
    show (Weight.equality p.1 p.2).na * sumN _ (fun q => f (0 :: q)) +
        (Weight.equality p.1 p.2).nb * sumN _ (fun q => f (1 :: q)) =
      (1 - p.1) * ext l.length (fun q => f (0 :: q)) (l.map (·.1)) +
        p.1 * ext l.length (fun q => f (1 :: q)) (l.map (·.1))
    rw [ha, hb, sumN_equality l _ fun r hr => h r (List.mem_cons_of_mem _ hr),
      sumN_equality l _ fun r hr => h r (List.mem_cons_of_mem _ hr)]

/-- The same with a last variable that is summed by reading at 0. -/
theorem sumN_equality_zero (d : ℕ) (hd : 2 ≤ d) : ∀ (l : List (GE × ℕ)) (f : List GE → GE),
    (∀ p ∈ l, 2 ≤ p.2) →
    sumN ((l.map fun p => Weight.equality p.1 p.2) ++ [Weight.atZero d]) f =
      ext l.length (fun q => f (q ++ [0])) (l.map (·.1))
  | [], f, _ => by
    obtain ⟨_, ha, hb⟩ := equality_twoNode 0 d hd
    show (Weight.equality 0 d).na * f [0] + (Weight.equality 0 d).nb * f [1] = f [0]
    rw [ha, hb]
    ring
  | p :: l, f, h => by
    obtain ⟨_, ha, hb⟩ := equality_twoNode p.1 p.2 (h p List.mem_cons_self)
    show (Weight.equality p.1 p.2).na *
          sumN ((l.map fun p => Weight.equality p.1 p.2) ++ [Weight.atZero d])
            (fun q => f (0 :: q)) +
        (Weight.equality p.1 p.2).nb *
          sumN ((l.map fun p => Weight.equality p.1 p.2) ++ [Weight.atZero d])
            (fun q => f (1 :: q)) =
      (1 - p.1) * ext l.length (fun q => f (0 :: q ++ [0])) (l.map (·.1)) +
        p.1 * ext l.length (fun q => f (1 :: q ++ [0])) (l.map (·.1))
    rw [ha, hb, sumN_equality_zero d hd l _ fun r hr => h r (List.mem_cons_of_mem _ hr),
      sumN_equality_zero d hd l _ fun r hr => h r (List.mem_cons_of_mem _ hr)]
    rfl

end OnBytes.Slice.PscF
