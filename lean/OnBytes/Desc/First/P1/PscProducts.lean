-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/PscProducts.lean: the masked sumcheck's law (PscSound.lean, beside this file)
at ONE KIND OF SUMMAND: a sum of products of two multilinear extensions, UNDER COEFFICIENTS THAT ARE
FIXED BEFORE THE RUN, the further variable with three coefficients, nothing kept, with the end
values shown under masks. Other summands of the protocol owe their own. Definitions, statements and
proofs.

  `two_equality`, `two_plain`, `two_atZero`: the program's three weights are two-point weights
    (OnBytes/Desc/First/P1/SumMle.lean): (1 - z, z); (1, 1); (1, 0).
  `Term`: a coefficient and two end values, by their numbers. `sumTerms`: the summand on n values.
  `isSum_terms`: the summand on the extensions of n tables is summed to the tables' sum of products.
  `products_sound`: THE LAW AT SUCH A SUMMAND. Fixed first: the variables' weights ws (each
    two-point with at least three coefficients), n tables over these variables, one mask for each,
    the terms, the hiding coefficients, T and Cv. A record as in `psc_sound`, over ws and the
    further variable (read at 0, three coefficients), whose row is 0 in a world, whose end term S0
    is the summand on what was shown, where what was shown for end value i is the table's extension
    at the challenges plus beta times its mask, and no bad element was drawn: then Cv is the sum
    over the cube, under the weights, of the terms' products of the tables. hY: that the further
    variable's weight passes its two tests (`Held`) is a premise here: a closed fact, not shown in
    this file.

Limits: those of PscSound.lean. That what was shown is "the extension plus beta times the mask" is
what a caller gets from two things: the ledger's world (hidden = shown - beta * mask) and the claim
that the hidden end value is the extension: further claims.
-/
import OnBytes.Desc.First.P1.PscSound
import OnBytes.Desc.First.P1.SumMle

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model Polynomial

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### The three weights -/

theorem getD_replicate (z : E) : ∀ (n i : ℕ), i < n → (List.replicate n z).getD i zeroE = z
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    rw [List.replicate_succ, List.getD_cons_succ]
    exact getD_replicate z n i (by omega)

/-- A weight whose sums are a at 1 and b at X, X^2, ... -/
theorem two_of_moments (w : Wt K) (a b : K) (h1 : 1 ≤ w.d) (h0 : w.mom 0 = a)
    (hi : ∀ i, i + 1 < w.d → w.mom (i + 1) = b) : w.Two (a - b) b := by
  intro q hq
  obtain ⟨n, hn⟩ : ∃ n, w.d = n + 1 := ⟨w.d - 1, by omega⟩
  have e1 : q.eval 1 = ∑ i ∈ Finset.range (n + 1), q.coeff i := by
    rw [eval_eq_sum_range' (hn ▸ hq)]
    simp
  have e0 : q.eval 0 = q.coeff 0 := by rw [← coeff_zero_eq_eval_zero]
  rw [Wt.sum, hn, e0, e1, Finset.sum_range_succ', Finset.sum_range_succ', h0]
  have hs : ∑ i ∈ Finset.range n, w.mom (i + 1) * q.coeff (i + 1) =
      b * ∑ i ∈ Finset.range n, q.coeff (i + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi' => ?_
    rw [hi i (by have := Finset.mem_range.mp hi'; omega)]
  rw [hs]
  ring

theorem two_equality (z : E) (d : ℕ) (hd : 1 ≤ d) :
    (wtOf ρ (OnBytes.Psc.Weight.equality z d)).Two (1 - ρ.val z) (ρ.val z) :=
  two_of_moments _ 1 (ρ.val z) hd (by show ρ.val oneE = 1; exact ρ.one) fun i hi => by
    show ρ.val ((oneE :: List.replicate (d - 1) z).getD (i + 1) zeroE) = ρ.val z
    rw [List.getD_cons_succ, getD_replicate z (d - 1) i (by
      have : i + 1 < d := hi
      omega)]

theorem two_atZero (d : ℕ) (hd : 1 ≤ d) : (wtOf ρ (OnBytes.Psc.Weight.atZero d)).Two 1 0 := by
  have h := two_equality ρ zeroE d hd
  rw [ρ.zero, sub_zero] at h
  exact h

theorem two_plain (d : ℕ) (hd : 1 ≤ d) : (wtOf ρ (OnBytes.Psc.Weight.plain d)).Two 1 1 := by
  have h := two_of_moments (wtOf ρ (OnBytes.Psc.Weight.plain d)) 2 1 hd
    (by show ρ.val (addE oneE oneE) = 2; rw [ρ.add, ρ.one]; norm_num) fun i hi => by
      show ρ.val ((addE oneE oneE :: List.replicate (d - 1) oneE).getD (i + 1) zeroE) = 1
      rw [List.getD_cons_succ, getD_replicate oneE (d - 1) i (by
        have : i + 1 < d := hi
        omega), ρ.one]
  have e : (2 : K) - 1 = 1 := by norm_num
  rw [e] at h
  exact h

/-! ### Sums of products -/

/-- A term: a coefficient, and the numbers of two end values. -/
abbrev Term (K : Type) : Type := K × ℕ × ℕ

/-- The summand on the values v 0, v 1, ... -/
def sumTerms (ts : List (Term K)) (v : ℕ → K) : K := (ts.map fun t => t.1 * (v t.2.1 * v t.2.2)).sum

theorem isSum_zero : ∀ vs : List (Wt K), (∀ w ∈ vs, 1 ≤ w.d) → IsSum vs (fun _ => 0) 0
  | [], _ => rfl
  | w :: vs, h =>
    ⟨0, by
      rw [natDegree_zero]
      exact h w (by simp), by simp [Wt.sum], fun x => by
      rw [eval_zero]
      exact isSum_zero vs fun v hv => h v (by simp [hv])⟩

theorem twos_pos {k : ℕ} (hk : 1 ≤ k) : ∀ (vs : List (Wt K)) (xs : List (K × K)), Twos k vs xs →
    ∀ w ∈ vs, 1 ≤ w.d
  | [], [], _, _, hw => by simp at hw
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | v :: vs, x :: xs, h, w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact le_trans hk h.2.1
    · exact twos_pos hk vs xs h.2.2 w hw'

/-- The summand on the extensions of tables is summed to the tables' sum of products. -/
theorem isSum_terms (vs : List (Wt K)) (xs : List (K × K)) (h : Twos 3 vs xs)
    (A : ℕ → List Bool → K) : ∀ ts : List (Term K),
    IsSum vs (fun rs => sumTerms ts fun i => mle vs.length (A i) rs)
      (tot xs fun b => sumTerms ts fun i => A i b)
  | [] => by
    have hz : tot xs (fun _ => (0 : K)) = 0 := by
      have := tot_smul (0 : K) xs fun _ => (0 : K)
      simpa using this
    exact (isSum_zero vs (twos_pos (by omega) vs xs h)).congr (fun _ => by simp [sumTerms])
      (by simp [sumTerms, hz])
  | t :: ts => by
    have h1 := (isSum_mul vs xs (A t.2.1) (A t.2.2) h).smul t.1
    have h2 := isSum_terms vs xs h A ts
    refine (h1.add h2).congr (fun rs => by simp [sumTerms]) ?_
    rw [← tot_smul, ← tot_add]
    simp [sumTerms]

theorem twos_append {k : ℕ} : ∀ (vs : List (Wt K)) (xs : List (K × K)) (w : Wt K) (x : K × K),
    Twos k vs xs → w.Two x.1 x.2 → k ≤ w.d → Twos k (vs ++ [w]) (xs ++ [x])
  | [], [], _, _, _, h2, hk => ⟨h2, hk, trivial⟩
  | [], _ :: _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, h, _, _ => h.elim
  | _ :: vs, _ :: xs, w, x, h, h2, hk => ⟨h.1, h.2.1, twos_append vs xs w x h.2.2 h2 hk⟩

theorem twos_length {k : ℕ} : ∀ (vs : List (Wt K)) (xs : List (K × K)), Twos k vs xs →
    xs.length = vs.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: vs, _ :: xs, h => by
    rw [List.length_cons, List.length_cons, twos_length vs xs h.2.2]

/-- Summed by the value at 0 in the last variable, the summand on the extended tables is summed as
the summand on the tables. -/
theorem tot_ext1_terms (xs : List (K × K)) (A : ℕ → List Bool → K) (m : ℕ → K) :
    ∀ ts : List (Term K),
    tot (xs ++ [(1, 0)]) (fun b => sumTerms ts fun i => ext1 xs.length (A i) (m i) b) =
      tot xs fun b => sumTerms ts fun i => A i b
  | [] => by
    have hz : ∀ ys : List (K × K), tot ys (fun _ => (0 : K)) = 0 := fun ys => by
      have := tot_smul (0 : K) ys fun _ => (0 : K)
      simpa using this
    simp [sumTerms, hz]
  | t :: ts => by
    have h1 := tot_ext1_mul xs (A t.2.1) (A t.2.2) (m t.2.1) (m t.2.2)
    have h2 := tot_ext1_terms xs A m ts
    have e1 : (fun b => sumTerms (t :: ts) fun i => ext1 xs.length (A i) (m i) b) = fun b =>
        t.1 * (ext1 xs.length (A t.2.1) (m t.2.1) b * ext1 xs.length (A t.2.2) (m t.2.2) b) +
          sumTerms ts fun i => ext1 xs.length (A i) (m i) b := by
      funext b
      simp [sumTerms]
    have e2 : (fun b => sumTerms (t :: ts) fun i => A i b) = fun b =>
        t.1 * (A t.2.1 b * A t.2.2 b) + sumTerms ts fun i => A i b := by
      funext b
      simp [sumTerms]
    rw [e1, e2, tot_add, tot_add, tot_smul, tot_smul, h1, h2]

/-! ### The law at a sum of products -/

/-- **THE LAW AT A SUM OF PRODUCTS OF TWO EXTENSIONS, THE END VALUES SHOWN UNDER MASKS.** -/
theorem products_sound (ws : List OnBytes.Psc.Weight) (hw : ∀ w ∈ ws, Held w)
    (xs : List (K × K)) (h3 : Twos 3 (ws.map (wtOf ρ)) xs) (A : ℕ → List Bool → K) (m : ℕ → K)
    (ts : List (Term K)) (hcoef : ℕ → K) (T Cv : K)
    (hY : Held (OnBytes.Psc.Weight.atZero 3)) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card <
        dAt ((ws ++ [OnBytes.Psc.Weight.atZero 3]).map (wtOf ρ)) pre.length) ∧
      ∀ (W : World K) (p : Psc) (mu : E) (ms : List Rnd) (y : Rnd) (S0 : E) (sh : ℕ → K),
        ms.map (·.1) = ws → y.1 = OnBytes.Psc.Weight.atZero 3 →
        (∀ x ∈ ms ++ [y], x.2.1.length + 1 = x.1.d) →
        p.vars.toList = ws ++ [OnBytes.Psc.Weight.atZero 3] →
        p.r.toList = (ms ++ [y]).map (·.2.2) →
        p.claim = claimAfter (ms ++ [y]) (addE mu (mulE p.eps p.target)) →
        ρ.val p.target = T → p.start.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries (ws ++ [OnBytes.Psc.Weight.atZero 3]) →
          W.slot (p.first + i) = hcoef i) →
        (p.rowForm S0 {}).value ρ W = 0 →
        ρ.val S0 = sumTerms ts sh →
        (∀ i, sh i = mle ws.length (A i) (ms.map fun x => ρ.val x.2.2) + ρ.val y.2.2 * m i) →
        ρ.val p.eps ∉ badE (ρ.val mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val mu) (ρ.val p.eps))
          (movesP ρ (ms ++ [y]) (addE mu (mulE p.eps p.target)))) →
        Cv = tot xs fun b => sumTerms ts fun i => A i b := by
  have hlen : xs.length = ws.length := by
    rw [twos_length _ _ h3, List.length_map]
  have hall : ∀ w ∈ ws ++ [OnBytes.Psc.Weight.atZero 3], Held w := by
    intro w hwm
    rcases List.mem_append.mp hwm with h | h
    · exact hw w h
    · rw [List.mem_singleton] at h
      rw [h]
      exact hY
  have htw : Twos 3 ((ws ++ [OnBytes.Psc.Weight.atZero 3]).map (wtOf ρ)) (xs ++ [(1, 0)]) := by
    rw [List.map_append]
    exact twos_append _ _ _ _ h3 (two_atZero ρ 3 (by omega)) (le_refl 3)
  have hS := isSum_terms _ _ htw (fun i => ext1 ws.length (A i) (m i)) ts
  have hl1 : ((ws ++ [OnBytes.Psc.Weight.atZero 3]).map (wtOf ρ)).length = ws.length + 1 := by
    simp
  rw [hl1] at hS
  obtain ⟨badE, bad, hE, hB, hrun⟩ := psc_sound ρ _ hall hcoef _ _ hS T Cv
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro W p mu ms y S0 sh hms hy hlens hvars hr hclaim hT hC hslots hzero hS0 hsh hne hnb
  have hfin := hrun W p mu (ms ++ [y]) S0 {} (by rw [List.map_append, hms]; simp [hy]) hlens hvars
    hr hclaim hT hC hslots hzero ?_ hne hnb
  · rw [hfin, ← hlen]
    exact tot_ext1_terms xs A m ts
  · rw [Aff.value_empty, add_zero, hS0]
    congr 1
    funext i
    rw [hsh i, List.map_append]
    have hl : (ms.map fun x => ρ.val x.2.2).length = ws.length := by
      rw [List.length_map, ← hms, List.length_map]
    exact mle_ext1 ws.length (A i) (m i) _ _ hl

end OnBytes.Desc.First.P1
