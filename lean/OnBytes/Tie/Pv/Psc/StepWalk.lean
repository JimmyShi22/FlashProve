-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/StepWalk.lean: the verifier's linear form of a hiding polynomial, applied to the
masks, is the library's hiding polynomial at the point of challenges.

Main definitions: Match (the verifier's weights with their challenges match the library's variables
and point), place (which mask stands for which coefficient, if the verifier's coefficients have the
masks from a slot on: the last variable has its constant first). Main theorems: powers_sum,
hev_poly, hU_cons, walk_hU.

What is not claimed. Match is a hypothesis here. Nothing on a run, on soundness or on hiding.

-/
import OnBytes.Model.HideLaws
import Cb.Ld.LdHide

set_option autoImplicit false

namespace OnBytes.Road.Hd

open OnBytes.Model (Reading sumFrom)

section Walk

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Lists of powers, and polynomials given by their coefficients -/

/-- The loop of powers puts what it was given, turned round, before what it makes. -/
theorem powersLoop_pre (x : E) : ∀ (n : ℕ) (c : E) (done : List E),
    OnBytes.Psc.powersLoop x n c done = done.reverse ++ OnBytes.Psc.powersLoop x n c []
  | 0, c, done => by simp [OnBytes.Psc.powersLoop]
  | n + 1, c, done => by
    show OnBytes.Psc.powersLoop x n (mulE c x) (c :: done) =
      done.reverse ++ OnBytes.Psc.powersLoop x n (mulE c x) [c]
    rw [powersLoop_pre x n (mulE c x) (c :: done), powersLoop_pre x n (mulE c x) [c]]
    simp

/-- The first of n + 1 powers from c on is c. -/
theorem powers_cons (c x : E) (n : ℕ) :
    OnBytes.Psc.powers c x (n + 1) = c :: OnBytes.Psc.powers (mulE c x) x n := by
  show OnBytes.Psc.powersLoop x n (mulE c x) [c] = c :: OnBytes.Psc.powersLoop x n (mulE c x) []
  rw [powersLoop_pre]
  rfl

/-- The list of n powers has n members. -/
theorem powers_len (x : E) : ∀ (n : ℕ) (c : E), (OnBytes.Psc.powers c x n).length = n
  | 0, _ => rfl
  | n + 1, c => by rw [powers_cons, List.length_cons, powers_len x n]

/-- A sum over two lists, one behind the other. -/
theorem sumFrom_app (f : ℕ → E → K) : ∀ (a b : List E) (s : ℕ),
    sumFrom f s (a ++ b) = sumFrom f s a + sumFrom f (s + a.length) b
  | [], b, s => by
    show sumFrom f s b = 0 + sumFrom f (s + 0) b
    rw [zero_add, Nat.add_zero]
  | x :: a, b, s => by
    show f s x + sumFrom f (s + 1) (a ++ b) =
      f s x + sumFrom f (s + 1) a + sumFrom f (s + (a.length + 1)) b
    have e : s + 1 + a.length = s + (a.length + 1) := by omega
    rw [sumFrom_app f a b (s + 1), e, add_assoc]

/-- The list c, c x, c x^2 .. of n members, applied to the masks from s on. -/
theorem powers_sum (mask : ℕ → K) (x : E) : ∀ (n : ℕ) (c : E) (s : ℕ),
    sumFrom (fun j y => ρ.val y * mask j) s (OnBytes.Psc.powers c x n) =
      ∑ t : Fin n, ρ.val c * ρ.val x ^ (t : ℕ) * mask (s + t)
  | 0, c, s => by
    show (0 : K) = _
    simp
  | n + 1, c, s => by
    rw [powers_cons, Fin.sum_univ_succ]
    show ρ.val c * mask s + sumFrom (fun j y => ρ.val y * mask j) (s + 1)
      (OnBytes.Psc.powers (mulE c x) x n) = _
    rw [powers_sum mask x n (mulE c x) (s + 1), ρ.mul]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun t _ => ?_
      have e : s + 1 + (t : ℕ) = s + ((t.succ : Fin (n + 1)) : ℕ) := by
        rw [Fin.val_succ]
        omega
      rw [e, Fin.val_succ, pow_succ]
      ring

/-- A polynomial without a constant term, given by its other coefficients. -/
theorem hev_cons {n : ℕ} (W : Fin n → K) (x : K) :
    Cb.hev (Fin.cons 0 W : Fin (n + 1) → K) x = ∑ t : Fin n, x ^ ((t : ℕ) + 1) * W t := by
  unfold Cb.hev
  rw [Fin.sum_univ_succ, Fin.cons_zero, smul_zero, zero_add]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fin.cons_succ, Fin.val_succ, smul_eq_mul]

/-- The terms of a polynomial from the power s on, written as a sum over N places, for a list of at
most N coefficients. -/
theorem poly_sum (y : K) : ∀ (g : List E) (s N : ℕ), g.length ≤ N →
    sumFrom (fun i c => ρ.val c * y ^ i) s g =
      ∑ t : Fin N, y ^ (s + (t : ℕ)) * ρ.val (g.getD t zeroE)
  | [], s, N, _ => by
    show (0 : K) = _
    simp [ρ.zero]
  | c :: g, s, 0, h => by simp at h
  | c :: g, s, N + 1, h => by
    rw [Fin.sum_univ_succ]
    show ρ.val c * y ^ s + sumFrom (fun i c => ρ.val c * y ^ i) (s + 1) g = _
    rw [poly_sum y g (s + 1) N (by simpa using h)]
    congr 1
    · simp [mul_comm]
    · refine Finset.sum_congr rfl fun t _ => ?_
      have e : s + 1 + (t : ℕ) = s + ((t.succ : Fin (N + 1)) : ℕ) := by
        rw [Fin.val_succ]
        omega
      rw [e, Fin.val_succ, List.getD_cons_succ]

/-- The library's value of a polynomial whose coefficients are the readings of a list is the reading
of the verifier's value. -/
theorem hev_poly {n : ℕ} (g : List E) (x : E) (h : g.length ≤ n + 1) :
    Cb.hev (fun t : Fin (n + 1) => ρ.val (g.getD t zeroE)) (ρ.val x) =
      ρ.val (OnBytes.Psc.polyAt g x) := by
  have a := ρ.polyAt x g 0
  rw [poly_sum ρ (ρ.val x) g 0 (n + 1) h, pow_zero, one_mul] at a
  rw [← a]
  unfold Cb.hev
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.zero_add, smul_eq_mul]

/-! ## The two hiding polynomials -/

/-- The library's hiding polynomial, one variable taken off. -/
theorem hU_cons (v : Cb.HVar K) (l : List (Cb.HVar K)) (W : Cb.HIdx (v :: l) → K)
    (x : Cb.HPt (v :: l)) :
    Cb.hU (v :: l) W x =
      Cb.hPsi l x.2 * (∑ t : Fin v.n, x.1 ^ ((t : ℕ) + 1) * W (Sum.inl t)) +
        Cb.hU l (fun i => W (Sum.inr i)) x.2 := by
  show Cb.hPsi l x.2 • Cb.hev (Fin.cons 0 fun t => W (Sum.inl t) : Fin (v.n + 1) → K) x.1 +
    Cb.hU l (fun i => W (Sum.inr i)) x.2 = _
  rw [hev_cons, smul_eq_mul]

/-- The verifier's weights with their challenges, the library's variables and a point fit each
other: as many of each; a polynomial in a variable has as many coefficients in both; the public
polynomial psi of the library's variable has the readings of the verifier's psi as its coefficients;
and each coordinate of the point is the reading of the challenge. -/
def Match : List (OnBytes.Psc.Weight × E) → (l : List (Cb.HVar K)) → Cb.HPt l → Prop
  | [], [], _ => True
  | y :: vs, v :: l, x =>
    v.n + 1 = y.1.d ∧ y.1.psi.length ≤ y.1.d ∧
      (∀ t : Fin (v.n + 1), v.psi t = ρ.val (y.1.psi.getD t zeroE)) ∧ x.1 = ρ.val y.2 ∧
      Match vs l x.2
  | [], _ :: _, _ => False
  | _ :: _, [], _ => False

/-- Which mask stands for which coefficient of the library's hiding polynomial, if the verifier's
coefficients have the masks from s on. -/
def place (mask : ℕ → K) : (l : List (Cb.HVar K)) → ℕ → Cb.HIdx l → K
  | [], s, _ => mask s
  | [_], s, Sum.inl t => mask (s + 1 + (t : ℕ))
  | [_], s, Sum.inr _ => mask s
  | _ :: _ :: _, s, Sum.inl t => mask (s + (t : ℕ))
  | v :: v' :: l, s, Sum.inr i => place mask (v' :: l) (s + v.n) i

/-- **The verifier's linear form, applied to the masks, is the library's hiding polynomial at the
point of challenges; and the verifier's product of the public polynomials is the library's.** For
any list of variables that is not empty. -/
theorem walk_hU (mask : ℕ → K) : ∀ (vs : List (OnBytes.Psc.Weight × E)) (l : List (Cb.HVar K))
    (x : Cb.HPt l) (s : ℕ), vs ≠ [] → Match ρ vs l x →
      sumFrom (fun j y => ρ.val y * mask j) s (OnBytes.Psc.hidingWalk vs).1 =
          Cb.hU l (place mask l s) x ∧
        ρ.val (OnBytes.Psc.hidingWalk vs).2 = Cb.hPsi l x
  | [], _, _, _, h, _ => absurd rfl h
  | _ :: _, [], _, _, _, hM => hM.elim
  | [_], _ :: _ :: _, _, _, _, hM => hM.2.2.2.2.elim
  | _ :: _ :: _, [_], _, _, _, hM => hM.2.2.2.2.elim
  | [(w, g)], [v], x, s, _, hM => by
    obtain ⟨h1, h2, h3, h4, _⟩ := hM
    have h1' : v.n + 1 = w.d := h1
    have h2' : w.psi.length ≤ v.n + 1 := by
      rw [h1']
      exact h2
    have h4' : x.1 = ρ.val g := h4
    have e1 : (OnBytes.Psc.hidingWalk [(w, g)]).1 = OnBytes.Psc.powers oneE g w.d := rfl
    have e2 : (OnBytes.Psc.hidingWalk [(w, g)]).2 = OnBytes.Psc.polyAt w.psi g := rfl
    have ep : v.psi = fun t : Fin (v.n + 1) => ρ.val (w.psi.getD t zeroE) := funext h3
    have eR : Cb.hU [v] (place mask [v] s) x =
        Cb.hPsi ([] : List (Cb.HVar K)) x.2 *
          (∑ t : Fin v.n, x.1 ^ ((t : ℕ) + 1) * mask (s + 1 + (t : ℕ))) + mask s :=
      hU_cons v [] _ x
    have eP : Cb.hPsi ([] : List (Cb.HVar K)) x.2 = 1 := rfl
    constructor
    · rw [e1, ← h1', powers_sum, eR, eP, one_mul, h4', Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Nat.add_zero, Fin.val_succ, ρ.one, one_mul, mul_one]
      rw [add_comm (mask s)]
      refine congrArg (· + mask s) (Finset.sum_congr rfl fun t _ => ?_)
      have e : s + ((t : ℕ) + 1) = s + 1 + (t : ℕ) := by omega
      rw [e]
    · rw [e2]
      show _ = Cb.hev v.psi x.1 * 1
      rw [mul_one, ep, h4', hev_poly ρ w.psi g h2']
  | (w, g) :: y :: rest, v :: v' :: l, x, s, _, hM => by
    obtain ⟨h1, h2, h3, h4, hR⟩ := hM
    have h1' : v.n + 1 = w.d := h1
    have h2' : w.psi.length ≤ v.n + 1 := by
      rw [h1']
      exact h2
    have h4' : x.1 = ρ.val g := h4
    have hn : w.d - 1 = v.n := by omega
    obtain ⟨a1, a2⟩ := walk_hU mask (y :: rest) (v' :: l) x.2 (s + v.n) (List.cons_ne_nil _ _) hR
    have e1 : (OnBytes.Psc.hidingWalk ((w, g) :: y :: rest)).1 =
        OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 g) g (w.d - 1) ++
          (OnBytes.Psc.hidingWalk (y :: rest)).1 := rfl
    have e2 : (OnBytes.Psc.hidingWalk ((w, g) :: y :: rest)).2 =
        mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 (OnBytes.Psc.polyAt w.psi g) := rfl
    have ep : v.psi = fun t : Fin (v.n + 1) => ρ.val (w.psi.getD t zeroE) := funext h3
    have eR : Cb.hU (v :: v' :: l) (place mask (v :: v' :: l) s) x =
        Cb.hPsi (v' :: l) x.2 * (∑ t : Fin v.n, x.1 ^ ((t : ℕ) + 1) * mask (s + (t : ℕ))) +
          Cb.hU (v' :: l) (place mask (v' :: l) (s + v.n)) x.2 :=
      hU_cons v (v' :: l) _ x
    constructor
    · rw [e1, hn, sumFrom_app, powers_sum, powers_len, a1, eR, h4', ρ.mul, a2, Finset.mul_sum]
      refine congrArg (· + Cb.hU (v' :: l) (place mask (v' :: l) (s + v.n)) x.2)
        (Finset.sum_congr rfl fun t _ => ?_)
      rw [pow_succ]
      ring
    · rw [e2, ρ.mul, a2]
      show _ = Cb.hev v.psi x.1 * Cb.hPsi (v' :: l) x.2
      rw [ep, h4', hev_poly ρ w.psi g h2', mul_comm]

end Walk

#print axioms powers_sum
#print axioms hev_poly
#print axioms walk_hU

end OnBytes.Road.Hd
