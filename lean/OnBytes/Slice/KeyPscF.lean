-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyPscF.lean: the arithmetic of the zero-knowledge sumcheck, in the field.

OnBytes/Iop/Psc.lean has the verifier's part in the zero-knowledge sumcheck, on machine words. This
file has the same functions on lists over the field, with the same text (polyAt, dot, powers,
Weight, Weight.complete, hidingWalk, claimAfter), and the facts on them that a proof of soundness
uses. No protocol occurs here.

A weight says how polynomials in one variable are summed: a linear functional, given by its values
(moments) on 1, X, X^2 and so on. In a round of the sumcheck the prover sends all coefficients of a
polynomial but one, and the verifier computes that one from the equation "the polynomial's sum is
the running claim" (Weight.complete).

Towers. Let ws be the weights of the variables X_1 .. X_k. A tower over ws (Tower) is a function T
on lists of field elements, to be read as follows: T [x_1, .., x_i] is the sum, over the variables
from i + 1 on, of some polynomial at X_1 = x_1, .., X_i = x_i. So T [] is the whole sum, and T at a
list of k elements is the polynomial's value. What is asked is what the sumcheck's argument uses: at
each list of i - 1 elements there are d_i coefficients of a polynomial in one variable whose value
at x is T at the list with x appended, and whose sum under the weight of X_i is T at the list.
Towers can be added and multiplied by an element (Tower.add, Tower.smul).

Two towers are built here for all weights that meet Weight.OK: the product of the polynomials psi
of the variables (psiT), and the hiding polynomial with any coefficients (hideT). At a full list of
challenges they are what hidingWalk computes (hidingWalk_snd, hidingWalk_fst).

One round (Tower.round_cnt). If the running claim is not T at the challenges so far, then, whatever
the prover sends, the completed polynomial's value at x is T at the challenges with x appended for
at most d - 1 values x. The count of zeros is the library's Cb.hev_roots
(Cb/Ld/LdPscProofs.lean).

Main definitions: polyAt, dot, powers, Weight, Weight.plain, Weight.equality, Weight.atZero,
Weight.OK, Weight.complete, hidingEntries, hidingWalk, claimAfter, pv, Weight.sum, Tower, psiT,
hideT.

Main theorems: polyAt_eq_pv, dot_eq_sum, complete_length, complete_sum, pv_agree_cnt, plain_ok,
equality_ok, Tower.add, Tower.smul, Tower.round_cnt, tower_psiT, tower_hideT, hidingWalk_snd,
hidingWalk_fst.

Not claimed. That these functions are the readings of the program's: the texts are the same, and no
theorem here compares them. Nothing on hiding.

-/
import Cb.Ld.LdPscProofs
import OnBytes.Slice.Draws

set_option autoImplicit false

namespace OnBytes.Slice.PscF
open Prob Cb

/-! ## Polynomials and sums of products, on lists -/

/-- The value at x of the polynomial with coefficients g, lowest degree first. -/
def polyAt (g : List GE) (x : GE) : GE := g.foldr (fun c r => r * x + c) 0

/-- The sum of the products of the members of two lists, as far as the shorter list goes. -/
def dot (a b : List GE) : GE := (a.zip b).foldl (fun r p => r + p.1 * p.2) 0

/-- The loop of powers: so many more powers from c on; done: those so far, the last one first. -/
def powersLoop (x : GE) : ℕ → GE → List GE → List GE
  | 0, _, done => done.reverse
  | n + 1, c, done => powersLoop x n (c * x) (c :: done)

/-- The n elements c, c x, c x^2 and so on. -/
def powers (c x : GE) (n : ℕ) : List GE := powersLoop x n c []

/-- The polynomial without coefficients has the value 0. -/
theorem polyAt_nil (x : GE) : polyAt [] x = 0 := rfl

/-- One step of Horner's rule. -/
theorem polyAt_cons (c : GE) (g : List GE) (x : GE) : polyAt (c :: g) x = polyAt g x * x + c := rfl

/-- The loop of dot, started at r, adds r to the loop started at 0. -/
theorem foldl_acc (l : List (GE × GE)) (r : GE) :
    l.foldl (fun r p => r + p.1 * p.2) r = r + l.foldl (fun r p => r + p.1 * p.2) 0 := by
  induction l generalizing r with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (0 + _)]
    ring

/-- The sum of products with an empty first list is 0. -/
theorem dot_nil_left (b : List GE) : dot [] b = 0 := rfl

/-- The sum of products with an empty second list is 0. -/
theorem dot_nil_right (a : List GE) : dot a [] = 0 := by
  unfold dot
  rw [List.zip_nil_right]
  rfl

/-- The sum of products, split at the first members. -/
theorem dot_cons (a : GE) (as : List GE) (b : GE) (bs : List GE) :
    dot (a :: as) (b :: bs) = a * b + dot as bs := by
  unfold dot
  rw [List.zip_cons_cons, List.foldl_cons, foldl_acc]
  ring

/-- The loop of powers puts what was done so far in front. -/
theorem powersLoop_eq (x : GE) : ∀ (n : ℕ) (c : GE) (done : List GE),
    powersLoop x n c done = done.reverse ++ powersLoop x n c []
  | 0, _, done => by simp [powersLoop]
  | n + 1, c, done => by
    show powersLoop x n (c * x) (c :: done) = done.reverse ++ powersLoop x n (c * x) [c]
    rw [powersLoop_eq x n (c * x) (c :: done), powersLoop_eq x n (c * x) [c]]
    simp

/-- No powers. -/
theorem powers_zero (c x : GE) : powers c x 0 = [] := rfl

/-- The powers, split at the first. -/
theorem powers_succ (c x : GE) (n : ℕ) : powers c x (n + 1) = c :: powers (c * x) x n := by
  show powersLoop x n (c * x) [c] = c :: powersLoop x n (c * x) []
  rw [powersLoop_eq]
  rfl

/-- There are n powers. -/
theorem powers_length (c x : GE) : ∀ n, (powers c x n).length = n := by
  intro n
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [powers_succ, List.length_cons, ih]

/-! ## The same, as sums over a range -/

/-- The value at x of the polynomial with the d coefficients c 0, .., c (d - 1). -/
def pv (d : ℕ) (c : ℕ → GE) (x : GE) : GE := ∑ t ∈ Finset.range d, c t * x ^ t

/-- The value of a polynomial given by a list is the sum of its terms. -/
theorem polyAt_eq_pv (g : List GE) (x : GE) : polyAt g x = pv g.length (fun t => g.getD t 0) x := by
  induction g with
  | nil => rfl
  | cons c g ih =>
    rw [polyAt_cons, ih]
    unfold pv
    rw [List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    refine congrArg (· + c) (Finset.sum_congr rfl fun t _ => ?_)
    rw [pow_succ]
    ring

/-- The sum of products of two lists is the sum of the products of their members, up to any number
that is at least the length of one of them. -/
theorem dot_eq_sum (a b : List GE) (d : ℕ) (h : a.length ≤ d ∨ b.length ≤ d) :
    dot a b = ∑ t ∈ Finset.range d, a.getD t 0 * b.getD t 0 := by
  induction a generalizing b d with
  | nil =>
    rw [dot_nil_left]
    exact (Finset.sum_eq_zero fun t _ => by simp).symm
  | cons x a ih =>
    cases b with
    | nil =>
      rw [dot_nil_right]
      exact (Finset.sum_eq_zero fun t _ => by simp).symm
    | cons y b =>
      cases d with
      | zero => simp at h
      | succ d =>
        rw [dot_cons, Finset.sum_range_succ', ih b d (by simpa using h)]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        ring

/-- **Two polynomials with d coefficients that differ in a coefficient agree at no more than d - 1
elements.** -/
theorem pv_agree_cnt (d : ℕ) (c c' : ℕ → GE) (h : ∃ t, t < d ∧ c t ≠ c' t) :
    cnt (fun x : GE => pv d c x = pv d c' x) ≤ d - 1 := by
  obtain ⟨t, ht, hne⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hc : (fun i : Fin (n + 1) => c i.val - c' i.val) ≠ 0 := fun h0 =>
    hne (sub_eq_zero.1 (congrFun h0 ⟨t, ht⟩))
  refine le_trans (cnt_mono fun x hx => ?_) (hev_roots _ hc)
  show ∑ i : Fin (n + 1), x ^ (i : ℕ) • (c i.val - c' i.val) = 0
  unfold pv at hx
  rw [Finset.sum_range, Finset.sum_range] at hx
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hx
  rw [← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  ring

/-- A list's polynomial, with more coefficients counted: those beyond the list are 0. -/
theorem polyAt_eq_pv_le (g : List GE) (d : ℕ) (h : g.length ≤ d) (x : GE) :
    polyAt g x = pv d (fun t => g.getD t 0) x := by
  rw [polyAt_eq_pv]
  unfold pv
  refine Finset.sum_subset (Finset.range_mono h) fun t _ ht => ?_
  show g.getD t 0 * x ^ t = 0
  rw [List.getD_eq_default _ _ (Nat.le_of_not_lt fun hlt => ht (Finset.mem_range.2 hlt)), zero_mul]

/-- Writing y for 0 at one place of the second list adds y times the first list's member at that
place. -/
theorem dot_at (y : GE) (high : List GE) : ∀ low m : List GE,
    dot m (low ++ y :: high) = dot m (low ++ 0 :: high) + m.getD low.length 0 * y
  | [], [] => by simp [dot_nil_left]
  | [], a :: m => by
    simp only [List.nil_append, dot_cons, List.length_nil, List.getD_cons_zero]
    ring
  | _ :: low, [] => by simp [dot_nil_left]
  | b :: low, a :: m => by
    simp only [List.cons_append, dot_cons, List.length_cons, List.getD_cons_succ]
    rw [dot_at y high low m]
    ring

/-- The sum of products with powers: c times the value of a polynomial. -/
theorem dot_powers (g : GE) : ∀ (n : ℕ) (c : GE) (cs : List GE),
    dot (powers c g n) cs = c * polyAt (cs.take n) g
  | 0, c, cs => by simp [powers_zero, dot_nil_left, polyAt_nil]
  | n + 1, c, [] => by simp [dot_nil_right, polyAt_nil]
  | n + 1, c, y :: cs => by
    rw [powers_succ, dot_cons, dot_powers g n (c * g) cs, List.take_succ_cons, polyAt_cons]
    ring

/-- The sum of products with a joined list. -/
theorem dot_append : ∀ l₁ l₂ cs : List GE,
    dot (l₁ ++ l₂) cs = dot l₁ (cs.take l₁.length) + dot l₂ (cs.drop l₁.length)
  | [], l₂, cs => by simp [dot_nil_left]
  | a :: l₁, l₂, [] => by simp [dot_nil_right]
  | a :: l₁, l₂, y :: cs => by
    simp only [List.cons_append, dot_cons, List.length_cons, List.take_succ_cons,
      List.drop_succ_cons]
    rw [dot_append l₁ l₂ cs]
    ring

/-! ## One variable of a sumcheck -/

/-- How polynomials in one variable are summed: a linear functional, given by its values on 1, X,
X^2 and so on. d: a polynomial in this variable has d coefficients. moment: the sums of 1, X, X^2
and so on. psi: the coefficients of a polynomial whose sum is 1. fixed: the number of the
coefficient that is not sent. fixedInv: the inverse of the sum of X^fixed. -/
structure Weight where
  d : ℕ
  moment : List GE
  psi : List GE
  fixed : ℕ
  fixedInv : GE

/-- The plain sum g(0) + g(1). -/
def Weight.plain (d : ℕ) : Weight where
  d := d
  moment := (1 + 1) :: List.replicate (d - 1) 1
  psi := [0, 1]
  fixed := 1
  fixedInv := 1

/-- The sum (1 - z) g(0) + z g(1). -/
def Weight.equality (z : GE) (d : ℕ) : Weight where
  d := d
  moment := 1 :: List.replicate (d - 1) z
  psi := [1]
  fixed := 0
  fixedInv := 1

/-- The sum g(0). -/
def Weight.atZero (d : ℕ) : Weight := Weight.equality 0 d

/-- What is asked of a weight: its sizes fit each other, fixedInv is the inverse of the sum of
X^fixed, and the sum of psi is 1. -/
structure Weight.OK (w : Weight) : Prop where
  two : 2 ≤ w.d
  len : w.moment.length = w.d
  psiLen : w.psi.length ≤ w.d
  fix : w.fixed < w.d
  inv : w.moment.getD w.fixed 0 * w.fixedInv = 1
  psiSum : dot w.moment w.psi = 1

/-- The plain sum meets what is asked of a weight. -/
theorem plain_ok (d : ℕ) (h : 2 ≤ d) : (Weight.plain d).OK where
  two := h
  len := by
    show (List.replicate (d - 1) (1 : GE)).length + 1 = d
    rw [List.length_replicate]
    omega
  psiLen := h
  fix := h
  inv := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
    show ((1 + 1 : GE) :: List.replicate (n + 1) 1).getD 1 0 * 1 = 1
    rw [List.replicate_succ]
    simp
  psiSum := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
    show dot ((1 + 1 : GE) :: List.replicate (n + 1) 1) [0, 1] = 1
    rw [List.replicate_succ, dot_cons, dot_cons, dot_nil_right]
    ring

/-- The sum under a factor of the equality polynomial meets what is asked of a weight. -/
theorem equality_ok (z : GE) (d : ℕ) (h : 2 ≤ d) : (Weight.equality z d).OK where
  two := h
  len := by
    show (List.replicate (d - 1) z).length + 1 = d
    rw [List.length_replicate]
    omega
  psiLen := Nat.le_trans (by decide : 1 ≤ 2) h
  fix := Nat.lt_of_lt_of_le (by decide : 0 < 2) h
  inv := by
    show ((1 : GE) :: List.replicate (d - 1) z).getD 0 0 * 1 = 1
    simp
  psiSum := by
    show dot ((1 : GE) :: List.replicate (d - 1) z) [1] = 1
    rw [dot_cons, dot_nil_right]
    ring

/-- The whole polynomial of a round, from the coefficients that were sent and the claim that the
polynomial must sum to. -/
def Weight.complete (w : Weight) (sent : List GE) (claim : GE) : List GE :=
  let low := sent.take w.fixed
  let high := sent.drop w.fixed
  let rest := dot w.moment (low ++ 0 :: high)
  low ++ (claim - rest) * w.fixedInv :: high

/-- The sum of the polynomial with the coefficients c 0, .., c (d - 1). -/
def Weight.sum (w : Weight) (c : ℕ → GE) : GE :=
  ∑ t ∈ Finset.range w.d, w.moment.getD t 0 * c t

/-- The completed polynomial has d coefficients. -/
theorem complete_length (w : Weight) (hf : w.fixed < w.d) (sent : List GE)
    (hs : sent.length + 1 = w.d) (claim : GE) : (w.complete sent claim).length = w.d := by
  unfold Weight.complete
  simp only [List.length_append, List.length_cons, List.length_take, List.length_drop]
  omega

/-- **The completed polynomial's sum is the claim.** -/
theorem complete_sum (w : Weight) (hinv : w.moment.getD w.fixed 0 * w.fixedInv = 1)
    (sent : List GE) (hf : w.fixed ≤ sent.length) (claim : GE) :
    dot w.moment (w.complete sent claim) = claim := by
  have hlen : (sent.take w.fixed).length = w.fixed := by simp [hf]
  unfold Weight.complete
  simp only []
  rw [dot_at, hlen]
  linear_combination (claim - dot w.moment (sent.take w.fixed ++ 0 :: sent.drop w.fixed)) * hinv

/-- The running claim after the rounds. R: the claim before them. A round: the coefficients sent and
the challenge. -/
def claimAfter : List Weight → List (List GE × GE) → GE → GE
  | w :: ws, (q, g) :: rs, R => claimAfter ws rs (polyAt (w.complete q R) g)
  | _, _, R => R

/-! ## Towers -/

/-- **A tower over the weights ws**: see the head of this file. -/
def Tower : List Weight → (List GE → GE) → Prop
  | [], _ => True
  | w :: ws, T =>
    (∃ c : ℕ → GE, w.sum c = T [] ∧ ∀ x, pv w.d c x = T [x]) ∧ ∀ x, Tower ws fun p => T (x :: p)

/-- The sum of two towers is a tower. -/
theorem Tower.add : ∀ {ws : List Weight} {T T' : List GE → GE}, Tower ws T → Tower ws T' →
    Tower ws fun p => T p + T' p
  | [], _, _, _, _ => trivial
  | w :: _, _, _, ⟨⟨c, h1, h2⟩, h3⟩, ⟨⟨c', h1', h2'⟩, h3'⟩ =>
    ⟨⟨fun t => c t + c' t, by
        beta_reduce
        rw [← h1, ← h1']
        unfold Weight.sum
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ => mul_add _ _ _, fun x => by
        beta_reduce
        rw [← h2 x, ← h2' x]
        unfold pv
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ => add_mul _ _ _⟩,
      fun x => Tower.add (h3 x) (h3' x)⟩

/-- A multiple of a tower is a tower. -/
theorem Tower.smul (a : GE) : ∀ {ws : List Weight} {T : List GE → GE}, Tower ws T →
    Tower ws fun p => a * T p
  | [], _, _ => trivial
  | w :: _, _, ⟨⟨c, h1, h2⟩, h3⟩ =>
    ⟨⟨fun t => a * c t, by
        beta_reduce
        rw [← h1]
        unfold Weight.sum
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring, fun x => by
        beta_reduce
        rw [← h2 x]
        unfold pv
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring⟩,
      fun x => Tower.smul a (h3 x)⟩

/-- **One round.** If the running claim R is not the tower's sum, then, whatever d - 1 coefficients
the prover sends, the completed polynomial's value at x is the tower's value at x for at most d - 1
elements x. -/
theorem Tower.round_cnt {w : Weight} {ws : List Weight} {T : List GE → GE} (hw : w.OK)
    (hT : Tower (w :: ws) T) {R : GE} (hR : R ≠ T []) (sent : List GE)
    (hs : sent.length + 1 = w.d) :
    cnt (fun x : GE => polyAt (w.complete sent R) x = T [x]) ≤ w.d - 1 := by
  obtain ⟨⟨c, h1, h2⟩, _⟩ := hT
  have hl := complete_length w hw.fix sent hs R
  have hsum : w.sum (fun t => (w.complete sent R).getD t 0) = R := by
    have h := complete_sum w hw.inv sent (by have := hw.fix; omega) R
    rwa [dot_eq_sum _ _ w.d (Or.inl (le_of_eq hw.len))] at h
  have hne : ∃ t, t < w.d ∧ (w.complete sent R).getD t 0 ≠ c t := by
    by_contra hcon
    refine hR (hsum.symm.trans (Eq.trans ?_ h1))
    refine Finset.sum_congr rfl fun t ht => ?_
    beta_reduce
    rw [not_not.1 fun hne => hcon ⟨t, Finset.mem_range.1 ht, hne⟩]
  refine le_trans (cnt_mono fun x hx => ?_) (pv_agree_cnt w.d _ c hne)
  rw [h2 x, ← hx, polyAt_eq_pv, hl]

/-! ## The hiding polynomial -/

/-- The number of coefficients of the hiding polynomial. -/
def hidingEntries (vars : List Weight) : ℕ := 1 + (vars.map fun w => w.d - 1).sum

/-- The value of the hiding polynomial at the challenges as a linear form in its coefficients,
together with the product of all psi at their challenges. -/
def hidingWalk : List (Weight × GE) → List GE × GE
  | [] => ([], 1)
  | [(w, g)] => (powers 1 g w.d, polyAt w.psi g)
  | (w, g) :: rest =>
    let later := hidingWalk rest
    (powers (later.2 * g) g (w.d - 1) ++ later.1, later.2 * polyAt w.psi g)

/-- **The tower of the product of the polynomials psi.** A variable that is summed gives the factor
1. -/
def psiT : List Weight → List GE → GE
  | w :: ws, x :: p => polyAt w.psi x * psiT ws p
  | _, _ => 1

/-- Where all variables are summed the product is 1. -/
theorem psiT_nil (ws : List Weight) : psiT ws [] = 1 := by cases ws <;> rfl

/-- The product of the polynomials psi is a tower. -/
theorem tower_psiT : ∀ ws : List Weight, (∀ w ∈ ws, w.OK) → Tower ws (psiT ws)
  | [], _ => trivial
  | w :: ws, h => by
    have hw := h w List.mem_cons_self
    refine ⟨⟨fun t => w.psi.getD t 0, ?_, fun x => ?_⟩, fun x => ?_⟩
    · have h1 := hw.psiSum
      rwa [dot_eq_sum _ _ w.d (Or.inl (le_of_eq hw.len))] at h1
    · show _ = polyAt w.psi x * psiT ws []
      rw [psiT_nil, mul_one, polyAt_eq_pv_le _ _ hw.psiLen]
    · exact Tower.smul _ (tower_psiT ws fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))

/-- **The tower of the hiding polynomial** with the coefficients cs, ordered by variable, then by
degree upwards; only the last variable has a constant. -/
def hideT : List Weight → List GE → List GE → GE
  | [], _, _ => 0
  | [w], cs, [] => dot w.moment (cs.take w.d)
  | [w], cs, x :: _ => polyAt (cs.take w.d) x
  | w :: w' :: ws, cs, [] =>
    dot w.moment (0 :: cs.take (w.d - 1)) +
      w.moment.getD 0 0 * hideT (w' :: ws) (cs.drop (w.d - 1)) []
  | w :: w' :: ws, cs, x :: p =>
    polyAt (0 :: cs.take (w.d - 1)) x * psiT (w' :: ws) p + hideT (w' :: ws) (cs.drop (w.d - 1)) p

/-- The hiding polynomial is a tower, whatever its coefficients. -/
theorem tower_hideT : ∀ (ws : List Weight) (cs : List GE), (∀ w ∈ ws, w.OK) →
    Tower ws (hideT ws cs)
  | [], _, _ => trivial
  | [w], cs, h => by
    have hw := h w List.mem_cons_self
    refine ⟨⟨fun t => (cs.take w.d).getD t 0, ?_, fun x => ?_⟩, fun _ => trivial⟩
    · exact (dot_eq_sum _ _ w.d (Or.inl (le_of_eq hw.len))).symm
    · exact (polyAt_eq_pv_le _ _ (List.length_take_le _ _) x).symm
  | w :: w' :: ws, cs, h => by
    have hw := h w List.mem_cons_self
    have hr : ∀ v ∈ w' :: ws, v.OK := fun v hv => h v (List.mem_cons_of_mem _ hv)
    have hlen : (hideT (w' :: ws) (cs.drop (w.d - 1)) [] :: cs.take (w.d - 1)).length ≤ w.d := by
      have h1 := List.length_take_le (w.d - 1) cs
      have h2 := hw.two
      rw [List.length_cons]
      omega
    refine ⟨⟨fun t => (hideT (w' :: ws) (cs.drop (w.d - 1)) [] :: cs.take (w.d - 1)).getD t 0,
      ?_, fun x => ?_⟩, fun x => ?_⟩
    · show _ = dot w.moment (0 :: cs.take (w.d - 1)) +
        w.moment.getD 0 0 * hideT (w' :: ws) (cs.drop (w.d - 1)) []
      have h1 := dot_at (hideT (w' :: ws) (cs.drop (w.d - 1)) []) (cs.take (w.d - 1)) [] w.moment
      simp only [List.nil_append, List.length_nil] at h1
      rw [← h1]
      exact (dot_eq_sum _ _ w.d (Or.inl (le_of_eq hw.len))).symm
    · show _ = polyAt (0 :: cs.take (w.d - 1)) x * psiT (w' :: ws) [] +
        hideT (w' :: ws) (cs.drop (w.d - 1)) []
      rw [← polyAt_eq_pv_le _ _ hlen, psiT_nil, polyAt_cons, polyAt_cons]
      ring
    · exact Tower.add (Tower.smul _ (tower_psiT _ hr)) (tower_hideT _ _ hr)

/-- At a full list of challenges the product of the polynomials psi is what hidingWalk computes. -/
theorem hidingWalk_snd : ∀ (ws : List Weight) (γ : List GE), ws.length = γ.length →
    (hidingWalk (ws.zip γ)).2 = psiT ws γ
  | [], [], _ => rfl
  | [w], [g], _ => by
    show polyAt w.psi g = polyAt w.psi g * psiT [] []
    rw [psiT_nil, mul_one]
  | w :: w' :: ws, g :: g' :: γ, h => by
    show (hidingWalk ((w' :: ws).zip (g' :: γ))).2 * polyAt w.psi g =
      polyAt w.psi g * psiT (w' :: ws) (g' :: γ)
    rw [hidingWalk_snd (w' :: ws) (g' :: γ) (Nat.succ.inj h), mul_comm]

/-- **At a full list of challenges the hiding polynomial is the linear form that hidingWalk
computes, at the coefficients.** -/
theorem hidingWalk_fst : ∀ (ws : List Weight) (γ cs : List GE), ws.length = γ.length →
    dot (hidingWalk (ws.zip γ)).1 cs = hideT ws cs γ
  | [], [], _, _ => rfl
  | [w], [g], cs, _ => by
    show dot (powers 1 g w.d) cs = polyAt (cs.take w.d) g
    rw [dot_powers, one_mul]
  | w :: w' :: ws, g :: g' :: γ, cs, h => by
    show dot (powers ((hidingWalk ((w' :: ws).zip (g' :: γ))).2 * g) g (w.d - 1) ++
        (hidingWalk ((w' :: ws).zip (g' :: γ))).1) cs =
      polyAt (0 :: cs.take (w.d - 1)) g * psiT (w' :: ws) (g' :: γ) +
        hideT (w' :: ws) (cs.drop (w.d - 1)) (g' :: γ)
    rw [dot_append, powers_length, dot_powers, List.take_take, Nat.min_self,
      hidingWalk_snd (w' :: ws) (g' :: γ) (Nat.succ.inj h),
      hidingWalk_fst (w' :: ws) (g' :: γ) _ (Nat.succ.inj h), polyAt_cons]
    ring

end OnBytes.Slice.PscF
