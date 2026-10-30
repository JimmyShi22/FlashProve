-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/SumMle.lean: what a caller of the sumcheck owes (`IsSum`,
OnBytes/Desc/First/P1/SumCore.lean), paid FOR ONE MULTILINEAR EXTENSION AND FOR A PRODUCT OF TWO.
EVERY OTHER SUMMAND OWES ITS OWN `IsSum`: a product of three extensions, a factor that is a public
map at the run's own challenges, a summand of degree three in the further variable, variables of
which some have two coefficients only. Algebra over a field; no text of a verifier. Definitions,
statements and proofs.

A TABLE over n variables is a function from lists of n bits to the field, the first bit for the
first variable that is summed. `mle n A rs`: its multilinear extension at the challenges rs. A
variable's weight is TWO-POINT (`Wt.Two w a b`) if the sum of every polynomial q of degree below d
is a q(0) + b q(1): the plain sum (1, 1); the sum at a point z (1 - z, z); the value at 0 (1, 0).
`tot ws F`: the sum of a table under such weights.

`isSum_mul`: the product of two extensions is summed to the table of products' sum, if every
variable has at least three coefficients.
`isSum_lin`: one extension, if every variable has at least two.
`ext1`: THE FURTHER VARIABLE Y AS ONE MORE BIT: the table that holds A at bit 0 and A + m at bit 1
has the extension A(r) + beta m: an end value as it is shown. Summed by the value at 0 it gives A
back. So a masked sumcheck's summand on shown end values is covered by the same two lemmas.

THE ORDER OF THE BITS IS THE ORDER OF THE ROUNDS. A caller that hands its points on by coordinates,
and sums its variables in another order, owes the re-indexing: it is not here. A CAUTION. That a
lemma here elaborates at a caller's variables does not say that its summand is the caller's: with a
summand that is not the caller's own, the law's premise on the end term is met by no honest run.

Nothing is said of probabilities.
-/
import OnBytes.Desc.First.P1.SumCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open Polynomial

variable {K : Type} [Field K]

/-- The multilinear extension of a table over n variables. -/
def mle : ℕ → (List Bool → K) → List K → K
  | 0, A, _ => A []
  | _ + 1, _, [] => 0
  | n + 1, A, r :: rs =>
    (1 - r) * mle n (fun b => A (false :: b)) rs + r * mle n (fun b => A (true :: b)) rs

theorem mle_add : ∀ (n : ℕ) (A B : List Bool → K) (rs : List K),
    mle n (fun b => A b + B b) rs = mle n A rs + mle n B rs
  | 0, _, _, _ => rfl
  | _ + 1, _, _, [] => by simp [mle]
  | n + 1, A, B, r :: rs => by
    simp only [mle]
    rw [mle_add n, mle_add n]
    ring

theorem mle_smul (c : K) : ∀ (n : ℕ) (A : List Bool → K) (rs : List K),
    mle n (fun b => c * A b) rs = c * mle n A rs
  | 0, _, _ => rfl
  | _ + 1, _, [] => by simp [mle]
  | n + 1, A, r :: rs => by
    simp only [mle]
    rw [mle_smul c n, mle_smul c n]
    ring

/-- The table with its first variable set to x. -/
def fixFirst (A : List Bool → K) (x : K) : List Bool → K :=
  fun b => (1 - x) * A (false :: b) + x * A (true :: b)

theorem mle_cons (n : ℕ) (A : List Bool → K) (x : K) (rs : List K) :
    mle (n + 1) A (x :: rs) = mle n (fixFirst A x) rs := by
  unfold fixFirst
  rw [mle_add, mle_smul, mle_smul]
  rfl

/-- The sum of every polynomial of degree below d is a q(0) + b q(1). -/
def Wt.Two (w : Wt K) (a b : K) : Prop :=
  ∀ q : K[X], q.natDegree < w.d → w.sum q = a * q.eval 0 + b * q.eval 1

/-- The sum of a table under two-point weights. -/
def tot : List (K × K) → (List Bool → K) → K
  | [], F => F []
  | w :: ws, F => w.1 * tot ws (fun b => F (false :: b)) + w.2 * tot ws (fun b => F (true :: b))

theorem tot_add : ∀ (ws : List (K × K)) (F G : List Bool → K),
    tot ws (fun b => F b + G b) = tot ws F + tot ws G
  | [], _, _ => rfl
  | w :: ws, F, G => by
    simp only [tot]
    rw [tot_add ws, tot_add ws]
    ring

theorem tot_smul (c : K) : ∀ (ws : List (K × K)) (F : List Bool → K),
    tot ws (fun b => c * F b) = c * tot ws F
  | [], _ => rfl
  | w :: ws, F => by
    simp only [tot]
    rw [tot_smul c ws, tot_smul c ws]
    ring

/-- The variables are two-point, with these weights, and have at least k coefficients. -/
def Twos (k : ℕ) : List (Wt K) → List (K × K) → Prop
  | [], [] => True
  | w :: vs, x :: ws => w.Two x.1 x.2 ∧ k ≤ w.d ∧ Twos k vs ws
  | _, _ => False

/-- **One extension.** -/
theorem isSum_lin : ∀ (vs : List (Wt K)) (ws : List (K × K)) (A : List Bool → K), Twos 2 vs ws →
    IsSum vs (mle vs.length A) (tot ws A)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | w :: vs, x :: ws, A, ⟨h2, hd, hr⟩ => by
    set t0 := tot ws fun b => A (false :: b) with ht0
    set t1 := tot ws fun b => A (true :: b) with ht1
    refine ⟨C t0 * (1 - X) + C t1 * X, ?_, ?_, fun y => ?_⟩
    · refine lt_of_le_of_lt ?_ (show 1 < w.d by omega)
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (natDegree_C_mul_le _ _) ?_
        exact le_trans (natDegree_sub_le _ _) (by simp)
      · exact le_trans (natDegree_C_mul_le _ _) (by simp)
    · rw [h2 _ (by
        refine lt_of_le_of_lt ?_ (show 1 < w.d by omega)
        refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
        · refine le_trans (natDegree_C_mul_le _ _) ?_
          exact le_trans (natDegree_sub_le _ _) (by simp)
        · exact le_trans (natDegree_C_mul_le _ _) (by simp))]
      simp only [eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_X, tot]
      ring
    · have ih := isSum_lin vs ws (fixFirst A y) hr
      refine ih.congr (fun rs => (mle_cons vs.length A y rs).symm) ?_
      unfold fixFirst
      rw [tot_add, tot_smul, tot_smul]
      simp only [eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_X]
      ring

/-- **The product of two extensions.** -/
theorem isSum_mul : ∀ (vs : List (Wt K)) (ws : List (K × K)) (A B : List Bool → K), Twos 3 vs ws →
    IsSum vs (fun rs => mle vs.length A rs * mle vs.length B rs) (tot ws fun b => A b * B b)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | w :: vs, x :: ws, A, B, ⟨h2, hd, hr⟩ => by
    set t00 := tot ws fun b => A (false :: b) * B (false :: b) with h00
    set t01 := tot ws fun b => A (false :: b) * B (true :: b) with h01
    set t10 := tot ws fun b => A (true :: b) * B (false :: b) with h10
    set t11 := tot ws fun b => A (true :: b) * B (true :: b) with h11
    have hdeg : (C t00 * (1 - X) ^ 2 + C (t01 + t10) * (X * (1 - X)) + C t11 * X ^ 2 :
        K[X]).natDegree < w.d := by
      refine lt_of_le_of_lt ?_ (show 2 < w.d by omega)
      have h1X : ((1 : K[X]) - X).natDegree ≤ 1 := le_trans (natDegree_sub_le _ _) (by simp)
      refine le_trans (natDegree_add_le _ _) (max_le
        (le_trans (natDegree_add_le _ _) (max_le ?_ ?_)) ?_)
      · refine le_trans (natDegree_C_mul_le _ _) ?_
        exact le_trans natDegree_pow_le (by omega)
      · refine le_trans (natDegree_C_mul_le _ _) ?_
        refine le_trans natDegree_mul_le ?_
        have : (X : K[X]).natDegree ≤ 1 := natDegree_X_le
        omega
      · refine le_trans (natDegree_C_mul_le _ _) ?_
        exact le_trans natDegree_pow_le (by
          have : (X : K[X]).natDegree ≤ 1 := natDegree_X_le
          omega)
    refine ⟨_, hdeg, ?_, fun y => ?_⟩
    · rw [h2 _ hdeg]
      simp only [eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_X, eval_pow, tot]
      ring
    · have ih := isSum_mul vs ws (fixFirst A y) (fixFirst B y) hr
      refine ih.congr (fun rs => ?_) ?_
      · show _ = mle (vs.length + 1) A (y :: rs) * mle (vs.length + 1) B (y :: rs)
        rw [mle_cons, mle_cons]
      · have he : (fun b => fixFirst A y b * fixFirst B y b) = fun b =>
            ((1 - y) ^ 2 * (A (false :: b) * B (false :: b)) +
              (y * (1 - y)) * (A (false :: b) * B (true :: b))) +
            ((y * (1 - y)) * (A (true :: b) * B (false :: b)) +
              y ^ 2 * (A (true :: b) * B (true :: b))) := by
          funext b
          unfold fixFirst
          ring
        rw [he, tot_add, tot_add, tot_add, tot_smul, tot_smul, tot_smul, tot_smul]
        simp only [eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_X, eval_pow]
        ring

/-! ### The further variable as one more bit -/

/-- The table over one variable more, the LAST one: A at bit 0, A + m at bit 1. -/
def ext1 : ℕ → (List Bool → K) → K → List Bool → K
  | 0, A, m => fun b => A [] + (if b.headD false then m else 0)
  | n + 1, A, m => fun b => ext1 n (fun c => A (b.headD false :: c)) m b.tail

/-- Its extension is A's at the first n challenges, plus the last challenge times m. -/
theorem mle_ext1 : ∀ (n : ℕ) (A : List Bool → K) (m : K) (rs : List K) (beta : K), rs.length = n →
    mle (n + 1) (ext1 n A m) (rs ++ [beta]) = mle n A rs + beta * m
  | 0, A, m, [], beta, _ => by
    simp [mle, ext1]
    ring
  | 0, _, _, _ :: _, _, h => by simp at h
  | _ + 1, _, _, [], _, h => by simp at h
  | n + 1, A, m, r :: rs, beta, h => by
    have hl : rs.length = n := by simpa using h
    have e0 := mle_ext1 n (fun c => A (false :: c)) m rs beta hl
    have e1 := mle_ext1 n (fun c => A (true :: c)) m rs beta hl
    show (1 - r) * mle (n + 1) (fun b => ext1 (n + 1) A m (false :: b)) (rs ++ [beta]) +
        r * mle (n + 1) (fun b => ext1 (n + 1) A m (true :: b)) (rs ++ [beta]) =
      ((1 - r) * mle n (fun b => A (false :: b)) rs + r * mle n (fun b => A (true :: b)) rs) +
        beta * m
    have f0 : (fun b => ext1 (n + 1) A m (false :: b)) = ext1 n (fun c => A (false :: c)) m := rfl
    have f1 : (fun b => ext1 (n + 1) A m (true :: b)) = ext1 n (fun c => A (true :: c)) m := rfl
    rw [f0, f1, e0, e1]
    ring

/-- Summed by the value at 0 in the last variable, a function of the extended tables is summed as
the function of the tables. -/
theorem tot_ext1_mul : ∀ (ws : List (K × K)) (A B : List Bool → K) (m m' : K),
    tot (ws ++ [(1, 0)]) (fun b => ext1 ws.length A m b * ext1 ws.length B m' b) =
      tot ws fun b => A b * B b
  | [], A, B, m, m' => by simp [tot, ext1]
  | w :: ws, A, B, m, m' => by
    have e0 := tot_ext1_mul ws (fun c => A (false :: c)) (fun c => B (false :: c)) m m'
    have e1 := tot_ext1_mul ws (fun c => A (true :: c)) (fun c => B (true :: c)) m m'
    show w.1 * tot (ws ++ [(1, 0)]) (fun b => ext1 (ws.length + 1) A m (false :: b) *
          ext1 (ws.length + 1) B m' (false :: b)) +
        w.2 * tot (ws ++ [(1, 0)]) (fun b => ext1 (ws.length + 1) A m (true :: b) *
          ext1 (ws.length + 1) B m' (true :: b)) = _
    exact congrArg₂ (fun a b => w.1 * a + w.2 * b) e0 e1

end OnBytes.Desc.First.P1
