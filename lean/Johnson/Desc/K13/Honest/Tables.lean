--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Tables.lean: tables with code (Johnson/Desc/K13/Honest/Moves.lean) and the
multilinear extensions of vectors on the cube (Alg/Mle.lean). Statements with their proofs.

A vector f on the cube of k variables is laid as a list of 2^k entries, the first variable being the
lowest bit of an entry's number (`tabOf`). Then: the sum of the products of two tables is the sum
over the cube; a table with its first variable set to g is the table of the vector with that
variable set; with all variables set, one entry is left, the multilinear extension at the point; and
the table of the equality vector, made by products alone (`eqT`), is the table of `Alg.eqk`.
Main names:
  `ptOf k gs`: a list as a point; 0 beyond its end.
  `tabOf_length`, `dotT_tabOf`, `foldT_tabOf`, `foldsT_tabOf`, `eqT_tabOf`, `scaleT_tabOf`.
  `dot_folds`: **with all variables set, the product of two tables' entries is the product of the
    two extensions at the point.**

What is not claimed. Nothing on a protocol. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.Code
import Alg.Mle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest

variable {K : Type} [CommRing K]

/-- A list as a point of k coordinates; 0 beyond its end. -/
def ptOf : (k : ℕ) → List K → Fin k → K
  | 0, _ => fun i => i.elim0
  | k + 1, gs => Fin.cons (gs.headD 0) (ptOf k gs.tail)

/-- One table with all variables set, the first challenge first. -/
def foldsT : List K → List K → List K
  | [], T => T
  | g :: gs, T => foldsT gs (foldT g T)

/-- Two lists of m entries, woven, have 2 m. -/
theorem weave_length {K : Type} : ∀ (m : ℕ) (A B : List K), A.length = m → B.length = m →
    (weave A B).length = 2 * m
  | 0, [], [], _, _ => rfl
  | m + 1, _ :: A, _ :: B, hA, hB => by
    show (weave A B).length + 1 + 1 = 2 * (m + 1)
    rw [weave_length m A B (by simp only [List.length_cons] at hA; omega)
      (by simp only [List.length_cons] at hB; omega)]
    omega
  | 0, _ :: _, _, hA, _ => by simp only [List.length_cons] at hA; omega
  | 0, [], _ :: _, _, hB => by simp only [List.length_cons] at hB; omega
  | _ + 1, [], _, hA, _ => by simp only [List.length_nil] at hA; omega
  | _ + 1, _ :: _, [], _, hB => by simp only [List.length_nil] at hB; omega

/-- A table has 2^k entries. -/
theorem tabOf_length {K : Type} : ∀ (k : ℕ) (f : (Fin k → Bool) → K), (tabOf k f).length = 2 ^ k
  | 0, _ => rfl
  | k + 1, f => by
    show (weave _ _).length = 2 ^ (k + 1)
    rw [weave_length (2 ^ k) _ _ (tabOf_length k _) (tabOf_length k _)]
    ring

/-- The sum of the products of two woven tables. -/
theorem dotT_weave : ∀ (A B A' B' : List K), A.length = B.length → A'.length = B'.length →
    A.length = A'.length → dotT (weave A B) (weave A' B') = dotT A A' + dotT B B'
  | [], [], [], [], _, _, _ => by
    show (0 : K) = 0 + 0
    ring
  | a :: A, b :: B, a' :: A', b' :: B', h1, h2, h3 => by
    show a * a' + (b * b' + dotT (weave A B) (weave A' B')) =
      (a * a' + dotT A A') + (b * b' + dotT B B')
    rw [dotT_weave A B A' B' (by simp only [List.length_cons] at h1; omega)
      (by simp only [List.length_cons] at h2; omega)
      (by simp only [List.length_cons] at h3; omega)]
    ring
  | [], _ :: _, _, _, h1, _, _ => by simp only [List.length_cons, List.length_nil] at h1; omega
  | _ :: _, [], _, _, h1, _, _ => by simp only [List.length_cons, List.length_nil] at h1; omega
  | _, _, [], _ :: _, _, h2, _ => by simp only [List.length_cons, List.length_nil] at h2; omega
  | _, _, _ :: _, [], _, h2, _ => by simp only [List.length_cons, List.length_nil] at h2; omega
  | [], [], _ :: _, _ :: _, _, _, h3 => by
    simp only [List.length_cons, List.length_nil] at h3; omega
  | _ :: _, _ :: _, [], [], _, _, h3 => by
    simp only [List.length_cons, List.length_nil] at h3; omega

/-- **The sum of the products of two tables is the sum over the cube.** -/
theorem dotT_tabOf : ∀ (k : ℕ) (f h : (Fin k → Bool) → K),
    dotT (tabOf k f) (tabOf k h) = ∑ b, f b * h b
  | 0, f, h => by
    show f _ * h _ + 0 = _
    rw [add_zero, Fintype.sum_unique]
    congr 1
  | k + 1, f, h => by
    show dotT (weave _ _) (weave _ _) = _
    rw [dotT_weave _ _ _ _ (by rw [tabOf_length, tabOf_length]) (by rw [tabOf_length, tabOf_length])
      (by rw [tabOf_length, tabOf_length]), dotT_tabOf k, dotT_tabOf k, Alg.sum_cube_succ,
      Finset.sum_add_distrib]

/-- A woven table with its first variable set. -/
theorem foldT_weave (g : K) : ∀ (A B : List K),
    foldT g (weave A B) = List.zipWith (fun a b => a + g * (b - a)) A B
  | a :: A, b :: B => by
    show (a + g * (b - a)) :: foldT g (weave A B) = (a + g * (b - a)) :: List.zipWith _ A B
    rw [foldT_weave g A B]
  | [], _ => rfl
  | _ :: _, [] => rfl

/-- Weaving goes through an operation entry by entry. -/
theorem zipWith_weave {K : Type} (F : K → K → K) : ∀ (A B A' B' : List K),
    List.zipWith F (weave A B) (weave A' B') =
      weave (List.zipWith F A A') (List.zipWith F B B')
  | a :: A, b :: B, a' :: A', b' :: B' => by
    show F a a' :: F b b' :: List.zipWith F (weave A B) (weave A' B') =
      F a a' :: F b b' :: weave (List.zipWith F A A') (List.zipWith F B B')
    rw [zipWith_weave F A B A' B']
  | [], _, _, _ => by simp [weave]
  | _ :: _, [], _, _ => by simp [weave]
  | _ :: _, _ :: _, [], _ => by simp [weave]
  | _ :: _, _ :: _, _ :: _, [] => by simp [weave]

/-- The table of a vector that is made entry by entry of two vectors. -/
theorem tabOf_zipWith {K : Type} (F : K → K → K) : ∀ (k : ℕ) (f h : (Fin k → Bool) → K),
    List.zipWith F (tabOf k f) (tabOf k h) = tabOf k fun b => F (f b) (h b)
  | 0, _, _ => rfl
  | k + 1, f, h => by
    show List.zipWith F (weave _ _) (weave _ _) = weave _ _
    rw [zipWith_weave, tabOf_zipWith F k, tabOf_zipWith F k]

/-- **A table with its first variable set is the table of the vector with that variable set.** -/
theorem foldT_tabOf (g : K) (k : ℕ) (f : (Fin (k + 1) → Bool) → K) :
    foldT g (tabOf (k + 1) f) =
      tabOf k fun b => f (Fin.cons false b) + g * (f (Fin.cons true b) - f (Fin.cons false b)) := by
  show foldT g (weave _ _) = _
  rw [foldT_weave, tabOf_zipWith]

/-- **With all variables set, one entry is left: the multilinear extension at the point.** -/
theorem foldsT_tabOf : ∀ (k : ℕ) (gs : List K) (f : (Fin k → Bool) → K), gs.length = k →
    foldsT gs (tabOf k f) = [Alg.mle f (ptOf k gs)]
  | 0, [], f, _ => by
    show [f _] = [Alg.mle f _]
    unfold Alg.mle Alg.eqk
    rw [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    congr 2
  | k + 1, g :: gs, f, h => by
    show foldsT gs (foldT g (tabOf (k + 1) f)) = [Alg.mle f (Fin.cons g (ptOf k gs))]
    rw [foldT_tabOf, foldsT_tabOf k gs _ (by simp only [List.length_cons] at h; omega),
      Alg.mle_cons]
    congr 1
    unfold Alg.mle
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  | 0, _ :: _, _, h => by simp only [List.length_cons] at h; omega
  | _ + 1, [], _, h => by simp only [List.length_nil] at h; omega

/-- **The product of two tables' last entries.** -/
theorem dot_folds (k : ℕ) (gs : List K) (f h : (Fin k → Bool) → K) (hg : gs.length = k) :
    dotT (foldsT gs (tabOf k f)) (foldsT gs (tabOf k h)) =
      Alg.mle f (ptOf k gs) * Alg.mle h (ptOf k gs) := by
  rw [foldsT_tabOf k gs f hg, foldsT_tabOf k gs h hg]
  show _ * _ + 0 = _
  rw [add_zero]

/-- Two lists made of one list, entry by entry, woven. -/
theorem flatMap_pair {K : Type} (F G : K → K) : ∀ T : List K,
    (T.flatMap fun v => [F v, G v]) = weave (T.map F) (T.map G)
  | [] => rfl
  | v :: T => by
    show F v :: G v :: (T.flatMap fun v => [F v, G v]) = F v :: G v :: weave (T.map F) (T.map G)
    rw [flatMap_pair F G T]

/-- The table of a vector that is made entry by entry of one vector. -/
theorem tabOf_map {K : Type} (F : K → K) : ∀ (k : ℕ) (f : (Fin k → Bool) → K),
    (tabOf k f).map F = tabOf k fun b => F (f b)
  | 0, _ => rfl
  | k + 1, f => by
    have hw : ∀ A B : List K, (weave A B).map F = weave (A.map F) (B.map F) := by
      intro A
      induction A with
      | nil => intro B; rfl
      | cons a A ih =>
        intro B
        cases B with
        | nil => rfl
        | cons b B =>
          show F a :: F b :: (weave A B).map F = F a :: F b :: weave (A.map F) (B.map F)
          rw [ih B]
    show (weave _ _).map F = weave _ _
    rw [hw, tabOf_map F k, tabOf_map F k]

/-- **The table of the equality vector.** -/
theorem eqT_tabOf : ∀ (k : ℕ) (z : List K), z.length = k →
    eqT z = tabOf k (Alg.eqk (ptOf k z))
  | 0, [], _ => by
    show [(1 : K)] = [Alg.eqk _ _]
    unfold Alg.eqk
    rw [Finset.univ_eq_empty, Finset.prod_empty]
  | k + 1, t :: z, h => by
    show ((eqT z).flatMap fun v => [v * (1 - t), v * t]) =
      weave (tabOf k fun b => Alg.eqk (Fin.cons t (ptOf k z) : Fin (k + 1) → K) (Fin.cons false b))
        (tabOf k fun b => Alg.eqk (Fin.cons t (ptOf k z) : Fin (k + 1) → K) (Fin.cons true b))
    rw [flatMap_pair, eqT_tabOf k z (by simp only [List.length_cons] at h; omega), tabOf_map,
      tabOf_map]
    congr 1 <;> congr 1 <;> funext b <;> rw [Alg.eqk_cons] <;> simp <;> ring
  | 0, _ :: _, h => by simp only [List.length_cons] at h; omega
  | _ + 1, [], h => by simp only [List.length_nil] at h; omega

/-- A table times a scalar. -/
theorem scaleT_tabOf (c : K) (k : ℕ) (f : (Fin k → Bool) → K) :
    scaleT c (tabOf k f) = tabOf k fun b => c * f b :=
  tabOf_map (fun v => c * v) k f

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.weave_length
#print axioms VerifiableInference.Desc.K13.Honest.tabOf_length
#print axioms VerifiableInference.Desc.K13.Honest.dotT_weave
#print axioms VerifiableInference.Desc.K13.Honest.foldT_weave
#print axioms VerifiableInference.Desc.K13.Honest.zipWith_weave
#print axioms VerifiableInference.Desc.K13.Honest.tabOf_zipWith
#print axioms VerifiableInference.Desc.K13.Honest.flatMap_pair
#print axioms VerifiableInference.Desc.K13.Honest.tabOf_map
#print axioms VerifiableInference.Desc.K13.Honest.dotT_tabOf
#print axioms VerifiableInference.Desc.K13.Honest.foldT_tabOf
#print axioms VerifiableInference.Desc.K13.Honest.foldsT_tabOf
#print axioms VerifiableInference.Desc.K13.Honest.dot_folds
#print axioms VerifiableInference.Desc.K13.Honest.eqT_tabOf
#print axioms VerifiableInference.Desc.K13.Honest.scaleT_tabOf
