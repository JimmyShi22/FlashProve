-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SimWords.lean: the closing of a segment (K10): for Honest/K10/Sim.lean's (3b): the
fold's prover on words (`foldSigmaW`, `foldRoundW`, Johnson/Prover/Link/FoldWordsOf.lean, over the library's own honest
prover, Fmt/M1Fold.lean), read in the field and cut in two: what the 2 k + 1 words give, and the drawn factor times what
the tables give. Lemmas on words and field elements: no part, no side, no law on coins.

  `coeffs_lin`    the two coefficients that are sent (the constant, the quadratic) are linear in the round
                   polynomial's three values
  `tablesAt`, `uRound`, `tRound`, `roundAt_split`   a round's polynomial at X = the coefficients' share + the factor ×
                   the tables' share; the second reads none of the hiding polynomial's 2 k + 1 coefficients. No premise
  `hidePoly_cons`, `cube_succ`, `cube_prod`, `sigF`, `sigF_zero`, `sigF_succ`   the hiding polynomial with its first
                   variable split off; sums over the cube
  `uRound_nil`, `uRound_cons`, `tlN`, `tlN_zero`, `tlN_tl`, `tl_tlN`, **`uRound_form`**   with fewer elements drawn in
                   front than there are rounds: the coefficients' share is A + B X + C X²: A: the later variables'
                   sum; C: the round's own quadratic coefficient: neither reads a drawn element
  `runW`, `book_w`, `book_w0`, `sig_sumB`   at the structure of the 2 k + 1 words (`uOfBook`, FoldWordsOf.lean): the
                   later variables' sum is Sim.lean's `sumB`, with the constant on top where no variable is left
  **`sigma_is`**    1 ≤ k: what "FOLD epsilon" sends is `runSentN`'s first
  `tab0`, `tab2`, **`round_is`**   fewer drawn in front than k: what a "FOLD round" sends is `runSentN`'s two of that
                   round, and the factor times `tab0` | `tab2`, which are handed neither the 2 k + 1 words nor the
                   factor

Limits. No premise on a table's size: at arrays of any sizes the words are what the library's text makes of them; that
they read, in the field, as the sum of the hiding polynomial and as the honest round polynomials, under a named premise
on the sizes, is a law of Johnson/Prover/Link/FoldWordsShows.lean, not spent here; there, as here, no run of a prover is
shown to send them. At as many drawn elements as there are rounds, or more, `uRound` and `tRound` have a value that is
no round's (the cut subtraction gives the cube of 0 variables). `roundAt_split` has no premise and holds there too: the
library's `roundAt` has the same cut subtraction (Fmt/M1Fold.lean). Every other theorem here whose statement names one
of the two has fewer. Of Johnson/Prover/Link/FoldWordsLaw.lean five small lemmas are called (`toE_foldl_add`,
`toE_hidePoly_sum`, `tailProd_cons`, `toE_tailProd_zero`, `length_cube`) and one definition (`Hide.tl`); of the library
among others `Leaves.sum_flatMap` (OnBytes/Slice/BlkLeavesRows.lean), the readings `toE_…` (OnBytes/Slice/Field.lean,
FieldInv.lean) and "2 is not 0" (`Cb.Pv.Head.gl_two_ne_zero`); of Honest/K10/SimMap.lean `sent_odd`, `sent_even`. No
property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SimMap
import Johnson.Prover.Link.FoldWordsLaw
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Wd
open Fmt Fmt.M1 Fmt.M1.FoldOwn
open OnBytes.Slice
open Johnson.Prover.Link

/-- The library's constant and quadratic coefficients are linear in the three values. -/
theorem coeffs_lin (v0 v1 vm : E) :
    toE (coeffs .two v0 v1 vm).1 = toE v0 ∧
      toE (coeffs .two v0 v1 vm).2.2 = (1 + 1 : GE)⁻¹ * (toE v1 + toE vm) - toE v0 := by
  refine ⟨rfl, ?_⟩
  show toE (Fld.two.subE (Fld.two.mulE (Fld.two.invE (Fld.two.addE Fld.oneE Fld.oneE))
    (Fld.two.addE v1 vm)) v0) = _
  rw [toE_subE, toE_mulE, toE_invE, toE_addE, toE_addE, toE_oneE]

/-- The tables' term of the summed polynomial, at a point: it reads none of the hiding polynomial's 2 k + 1 coefficients
(`T.U`), nor the factor (`T.eps`). -/
def tablesAt (T : Trial) (xs : List E) : E :=
  Fld.two.addE (dot .two (foldLow .two (xs.take T.k) T.G.c) (foldLow .two (xs.take T.k) T.m))
    (Fld.two.mulE (dot .two (foldLow .two (xs.take T.h) T.G.d) (foldLow .two (xs.take T.h) T.mu))
      (tailProd .two (xs.take T.k) T.h))

/-- The coefficients' share of a round's polynomial at X. -/
noncomputable def uRound (k : ℕ) (U : Hide) (gs : List E) (X : E) : GE :=
  ((cube (k - gs.length - 1)).map fun p => toE (hidePoly .two k U (gs ++ X :: p))).sum

/-- The tables' share. -/
noncomputable def tRound (T : Trial) (gs : List E) (X : E) : GE :=
  ((cube (T.k - gs.length - 1)).map fun p => toE (tablesAt T (gs ++ X :: p))).sum

theorem roundAt_split (T : Trial) (gs : List E) (X : E) :
    toE (roundAt .two T gs X) = uRound T.k T.U gs X + toE T.eps * tRound T gs X := by
  unfold roundAt uRound tRound
  rw [toE_foldl_add, toE_zeroE, zero_add, ← List.sum_map_mul_left, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  show toE (Fld.two.addE (hidePoly .two T.k T.U (gs ++ X :: p))
    (Fld.two.mulE T.eps (tablesAt T (gs ++ X :: p)))) = _
  rw [toE_addE, toE_mulE]

/-- The polynomial with its first variable split off. -/
theorem hidePoly_cons (k : ℕ) (U : Hide) (a : E) (xs : List E) (h : xs.length = k) :
    toE (hidePoly .two (k + 1) U (a :: xs)) =
      (toE (U.w 1 1) * toE a + toE (U.w 1 2) * (toE a * toE a)) * (xs.map toE).prod +
        toE (hidePoly .two k (Hide.tl U) xs) := by
  rw [toE_hidePoly_sum, toE_hidePoly_sum, List.range_succ_eq_map, List.map_cons, List.sum_cons,
    List.map_map]
  have e0 : toE (tailProd .two ((a :: xs).take (k + 1)) (0 + 1)) = (xs.map toE).prod := by
    rw [List.take_succ_cons, tailProd_cons, toE_tailProd_zero, ← h, List.take_length]
  rw [e0]
  have e1 : lst (a :: xs) 0 = toE a := rfl
  rw [e1]
  have e2 : ((List.range k).map ((fun i =>
      (toE (U.w (i + 1) 1) * lst (a :: xs) i + toE (U.w (i + 1) 2) * (lst (a :: xs) i * lst (a :: xs) i)) *
        toE (tailProd .two ((a :: xs).take (k + 1)) (i + 1))) ∘ Nat.succ)).sum =
      ((List.range k).map fun i =>
        (toE ((Hide.tl U).w (i + 1) 1) * lst xs i + toE ((Hide.tl U).w (i + 1) 2) * (lst xs i * lst xs i)) *
          toE (tailProd .two (xs.take k) (i + 1))).sum := rfl
  rw [e2]
  show toE U.w0 + (_ + _) = _ + (toE U.w0 + _)
  ring

/-- A sum over the cube, its first coordinate split off. -/
theorem cube_succ (n : ℕ) (G : List E → GE) :
    ((cube (n + 1)).map G).sum =
      ((cube n).map fun p => G (Fld.zeroE :: p) + G (Fld.oneE :: p)).sum := by
  rw [show cube (n + 1) = (cube n).flatMap fun p => [Fld.zeroE :: p, Fld.oneE :: p] from rfl,
    List.map_flatMap, Leaves.sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  show G (Fld.zeroE :: p) + (G (Fld.oneE :: p) + 0) = _
  rw [add_zero]

/-- Over the cube the products of the coordinates add up to 1. -/
theorem cube_prod : ∀ n : ℕ, ((cube n).map fun p => (p.map toE).prod).sum = 1
  | 0 => by
      show (1 : GE) + 0 = 1
      rw [add_zero]
  | n + 1 => by
      rw [cube_succ]
      have : (fun p : List E => ((Fld.zeroE :: p).map toE).prod + ((Fld.oneE :: p).map toE).prod) =
          fun p => (p.map toE).prod := by
        funext p
        rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, toE_zeroE, toE_oneE,
          zero_mul, one_mul, zero_add]
      rw [this]
      exact cube_prod n

/-- The polynomial in n variables, summed over the cube. -/
noncomputable def sigF (n : ℕ) (U : Hide) : GE :=
  ((cube n).map fun p => toE (hidePoly .two n U p)).sum

theorem sigF_zero (U : Hide) : sigF 0 U = toE U.w0 := by
  show toE (hidePoly .two 0 U []) + 0 = _
  rw [add_zero]
  rfl

theorem sigF_succ (n : ℕ) (U : Hide) :
    sigF (n + 1) U = toE (U.w 1 1) + toE (U.w 1 2) + 2 * sigF n (Hide.tl U) := by
  unfold sigF
  rw [cube_succ]
  have : ((cube n).map fun p => toE (hidePoly .two (n + 1) U (Fld.zeroE :: p)) +
      toE (hidePoly .two (n + 1) U (Fld.oneE :: p))).sum =
      ((cube n).map fun p => (toE (U.w 1 1) + toE (U.w 1 2)) * (p.map toE).prod +
        2 * toE (hidePoly .two n (Hide.tl U) p)).sum := by
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    rw [hidePoly_cons n U _ p (length_cube n p hp), hidePoly_cons n U _ p (length_cube n p hp), toE_zeroE,
      toE_oneE]
    ring
  rw [this, List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left, cube_prod, mul_one]

/-- **A round's share of the coefficients, with no variable in front**: the constant is the later variables' sum, the
quadratic coefficient the variable's own. -/
theorem uRound_nil (n : ℕ) (U : Hide) (X : E) :
    uRound (n + 1) U [] X =
      sigF n (Hide.tl U) + toE (U.w 1 1) * toE X + toE (U.w 1 2) * (toE X * toE X) := by
  unfold uRound sigF
  have e : n + 1 - ([] : List E).length - 1 = n := by simp
  rw [e]
  have : ((cube n).map fun p => toE (hidePoly .two (n + 1) U ([] ++ X :: p))).sum =
      ((cube n).map fun p => (toE (U.w 1 1) * toE X + toE (U.w 1 2) * (toE X * toE X)) *
        (p.map toE).prod + toE (hidePoly .two n (Hide.tl U) p)).sum := by
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    rw [List.nil_append, hidePoly_cons n U X p (length_cube n p hp)]
  rw [this, List.sum_map_add, List.sum_map_mul_left, cube_prod, mul_one]
  ring

/-- **With a variable in front**: a term that is linear in X comes on top. -/
theorem uRound_cons (k : ℕ) (U : Hide) (g : E) (gs : List E) (X : E) (h : gs.length < k) :
    uRound (k + 1) U (g :: gs) X =
      (toE (U.w 1 1) * toE g + toE (U.w 1 2) * (toE g * toE g)) * (gs.map toE).prod * toE X +
        uRound k (Hide.tl U) gs X := by
  unfold uRound
  have e : k + 1 - (g :: gs).length - 1 = k - gs.length - 1 := by
    rw [List.length_cons]
    omega
  rw [e]
  have : ((cube (k - gs.length - 1)).map fun p =>
      toE (hidePoly .two (k + 1) U (g :: gs ++ X :: p))).sum =
      ((cube (k - gs.length - 1)).map fun p =>
        ((toE (U.w 1 1) * toE g + toE (U.w 1 2) * (toE g * toE g)) * (gs.map toE).prod * toE X) *
          (p.map toE).prod + toE (hidePoly .two k (Hide.tl U) (gs ++ X :: p))).sum := by
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    have hl : (gs ++ X :: p).length = k := by
      rw [List.length_append, List.length_cons, length_cube _ p hp]
      omega
    rw [List.cons_append, hidePoly_cons k U g _ hl, List.map_append, List.map_cons, List.prod_append,
      List.prod_cons]
    ring
  rw [this, List.sum_map_add, List.sum_map_mul_left, cube_prod, mul_one]

/-- The structure with its first j variables' coefficients taken off. -/
def tlN (j : ℕ) (U : Hide) : Hide := ⟨fun l t => U.w (j + l) t, U.w0⟩

theorem tlN_zero (U : Hide) : tlN 0 U = U := by
  unfold tlN
  simp only [Nat.zero_add]

theorem tlN_tl (j : ℕ) (U : Hide) : tlN j (Hide.tl U) = tlN (j + 1) U := by
  unfold tlN Hide.tl
  have : (fun l t => U.w (j + l + 1) t) = fun l t => U.w (j + 1 + l) t := by
    funext l t
    rw [show j + l + 1 = j + 1 + l by omega]
  exact congrArg (fun f => (⟨f, U.w0⟩ : Hide)) this

theorem tl_tlN (j : ℕ) (U : Hide) : Hide.tl (tlN j U) = tlN (j + 1) U := (tlN_tl j U)

/-- **A round's share of the coefficients is A + B X + C X²**: A: the later variables' sum; C: the round's own
quadratic coefficient: neither reads a drawn element; B is named in front of X. -/
theorem uRound_form : ∀ (gs : List E) (k : ℕ) (U : Hide), gs.length < k →
    ∃ B : GE, ∀ X : E, uRound k U gs X =
      sigF (k - gs.length - 1) (tlN (gs.length + 1) U) + B * toE X +
        toE (U.w (gs.length + 1) 2) * (toE X * toE X)
  | [], k, U, h => by
      obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have : 0 < k := h; omega⟩
      refine ⟨toE (U.w 1 1), fun X => ?_⟩
      rw [uRound_nil]
      have e : n + 1 - ([] : List E).length - 1 = n := by simp
      rw [e, ← tlN_tl]
      simp only [List.length_nil, tlN_zero, Nat.zero_add]
  | g :: gs, k, U, h => by
      obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by rw [List.length_cons] at h; omega⟩
      have h' : gs.length < n := by rw [List.length_cons] at h; omega
      obtain ⟨B, hB⟩ := uRound_form gs n (Hide.tl U) h'
      refine ⟨(toE (U.w 1 1) * toE g + toE (U.w 1 2) * (toE g * toE g)) * (gs.map toE).prod + B,
        fun X => ?_⟩
      rw [uRound_cons n U g gs X h', hB X, tlN_tl]
      have e : n + 1 - (g :: gs).length - 1 = n - gs.length - 1 := by
        rw [List.length_cons]
        omega
      rw [e]
      show _ + (_ + _ + toE (U.w (gs.length + 1 + 1) 2) * _) = _
      rw [List.length_cons]
      ring

/-! ## At the structure of the 2 k + 1 words (`uOfBook`) -/

section
variable (k : ℕ) (w : Fin (2 * k + 1) → E)

/-- The 2 k + 1 words, read in the field, by number; 0 beyond the count. -/
noncomputable def runW : ℕ → GE := atN fun i => toE (w i)

theorem book_w (l t : ℕ) :
    toE ((uOfBook k w).w l t) =
      runW k w (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t) := by
  show toE (if h : (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t) < 2 * k + 1 then
    w ⟨_, h⟩ else Fld.zeroE) = _
  unfold runW atN
  generalize (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t) = i
  by_cases h : i < 2 * k + 1
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    exact toE_zeroE

theorem book_w0 : toE (uOfBook k w).w0 = runW k w (2 * k - 2) := by
  show toE (w ⟨2 * (k - 1), _⟩) = _
  unfold runW atN
  have h : 2 * k - 2 < 2 * k + 1 := by omega
  rw [dif_pos h]
  exact congrArg (fun i => toE (w i)) (Fin.ext (by show 2 * (k - 1) = 2 * k - 2; omega))

/-- **The later variables' sum is `sumB`**, with the constant on top where no variable is left. -/
theorem sig_sumB : ∀ n, n ≤ k →
    sigF n (tlN (k - n) (uOfBook k w)) =
      sumB k (runW k w) n + (if n = 0 then runW k w (2 * k - 2) else 0)
  | 0, _ => by
      rw [sigF_zero, if_pos rfl]
      show toE (uOfBook k w).w0 = 0 + _
      rw [zero_add, book_w0]
  | n + 1, h => by
      have ih := sig_sumB n (by omega)
      rw [sigF_succ, tl_tlN, show k - (n + 1) + 1 = k - n by omega, ih, if_neg (Nat.succ_ne_zero n)]
      show toE ((uOfBook k w).w (k - (n + 1) + 1) 1) + toE ((uOfBook k w).w (k - (n + 1) + 1) 2) + _ =
        phiB k (runW k w) (k - n) + 2 * sumB k (runW k w) n + 0
      rw [show k - (n + 1) + 1 = k - n by omega, book_w, book_w]
      unfold phiB
      by_cases h0 : n = 0
      · subst h0
        rw [Nat.sub_zero, if_neg (Nat.lt_irrefl k), if_neg (Nat.lt_irrefl k), if_pos rfl, if_pos rfl,
          show 2 * (k - 1) + 1 = 2 * k - 1 by omega, show 2 * (k - 1) + 2 = 2 * k by omega]
        ring
      · rw [if_pos (by omega), if_pos (by omega), if_neg h0, if_neg (by omega),
          show 2 * (k - n - 1) + (1 - 1) = 2 * (k - n) - 2 by omega,
          show 2 * (k - n - 1) + (2 - 1) = 2 * (k - n) - 1 by omega]
        ring

/-- **What "FOLD epsilon" sends is `runSentN`'s first.** -/
theorem sigma_is (hk : 1 ≤ k) : toE (foldSigmaW k w) = runSentN k (runW k w) 0 := by
  show toE ((cube k).foldl (fun s p => Fld.two.addE s (hidePoly .two k (uOfBook k w) p)) Fld.zeroE) =
    sumB k (runW k w) k
  rw [toE_foldl_add, toE_zeroE, zero_add]
  have h := sig_sumB k w k (le_refl k)
  rw [Nat.sub_self, tlN_zero, if_neg (by omega), add_zero] at h
  exact h

variable (h : ℕ) (c d m mu : Array E) (keptV : E)

/-- The tables' share of a round's constant: it is handed neither the 2 k + 1 words nor the factor. Its second summand
is the kept forms' term: keptV times (1 - g) over each g of gs. -/
noncomputable def tab0 (gs : List E) : GE :=
  tRound (trialW k h c d m mu (fun _ => Fld.zeroE) Fld.zeroE) gs Fld.zeroE +
    toE (gs.foldl (fun s g => Fld.two.mulE s (Fld.two.subE Fld.oneE g)) keptV)

/-- The tables' share of a round's quadratic coefficient. -/
noncomputable def tab2 (gs : List E) : GE :=
  (1 + 1 : GE)⁻¹ * (tRound (trialW k h c d m mu (fun _ => Fld.zeroE) Fld.zeroE) gs Fld.oneE +
    tRound (trialW k h c d m mu (fun _ => Fld.zeroE) Fld.zeroE) gs (Fld.two.negE Fld.oneE)) -
      tRound (trialW k h c d m mu (fun _ => Fld.zeroE) Fld.zeroE) gs Fld.zeroE

/-- **What a "FOLD round" sends is `runSentN`'s two of that round, and the factor times the tables' share.** No premise
on a table's size. -/
theorem round_is (eps : E) (gs : List E) (hj : gs.length < k) :
    toE (foldRoundW k h c d m mu keptV w eps gs).1 =
        runSentN k (runW k w) (2 * gs.length + 1) + toE eps * tab0 k h c d m mu keptV gs ∧
      toE (foldRoundW k h c d m mu keptV w eps gs).2 =
        runSentN k (runW k w) (2 * gs.length + 1 + 1) + toE eps * tab2 k h c d m mu gs := by
  obtain ⟨B, hB⟩ := uRound_form gs k (uOfBook k w) hj
  have hA : sigF (k - gs.length - 1) (tlN (gs.length + 1) (uOfBook k w)) =
      runSentN k (runW k w) (2 * gs.length + 1) := by
    have h1 := sig_sumB k w (k - (gs.length + 1)) (Nat.sub_le _ _)
    rw [show k - (k - (gs.length + 1)) = gs.length + 1 by omega] at h1
    rw [show k - gs.length - 1 = k - (gs.length + 1) by omega, h1, sent_odd]
    by_cases e : gs.length + 1 = k
    · rw [if_pos (by omega), if_pos e]
    · rw [if_neg (by omega), if_neg e]
  have hC : toE ((uOfBook k w).w (gs.length + 1) 2) =
      runSentN k (runW k w) (2 * gs.length + 1 + 1) := by
    rw [book_w, sent_even]
    by_cases e : gs.length + 1 = k
    · rw [if_neg (by omega), if_pos e, show 2 * (k - 1) + 2 = 2 * k by omega]
    · rw [if_pos (by omega), if_neg e,
        show 2 * (gs.length + 1 - 1) + (2 - 1) = 2 * (gs.length + 1) - 1 by omega]
  have hR : ∀ X : E, toE (roundAt .two (trialW k h c d m mu w eps) gs X) =
      runSentN k (runW k w) (2 * gs.length + 1) + B * toE X +
        runSentN k (runW k w) (2 * gs.length + 1 + 1) * (toE X * toE X) +
        toE eps * tRound (trialW k h c d m mu (fun _ => Fld.zeroE) Fld.zeroE) gs X := by
    intro X
    rw [roundAt_split]
    show uRound k (uOfBook k w) gs X + toE eps * _ = _
    rw [hB X, hA, hC]
    rfl
  have hl := coeffs_lin (roundAt .two (trialW k h c d m mu w eps) gs Fld.zeroE)
    (roundAt .two (trialW k h c d m mu w eps) gs Fld.oneE)
    (roundAt .two (trialW k h c d m mu w eps) gs (Fld.two.negE Fld.oneE))
  have h2 : (1 + 1 : GE) ≠ 0 := by
    rw [one_add_one_eq_two]
    exact Cb.Pv.Head.gl_two_ne_zero
  constructor
  · show toE (Fld.two.addE _ (Fld.two.mulE eps _)) = _
    rw [toE_addE, toE_mulE, hl.1, hR, toE_zeroE]
    unfold tab0
    ring
  · have e : (foldRoundW k h c d m mu keptV w eps gs).2 =
        (coeffs .two (roundAt .two (trialW k h c d m mu w eps) gs Fld.zeroE)
          (roundAt .two (trialW k h c d m mu w eps) gs Fld.oneE)
          (roundAt .two (trialW k h c d m mu w eps) gs (Fld.two.negE Fld.oneE))).2.2 := rfl
    have hi : (1 + 1 : GE)⁻¹ * (1 + 1) = 1 := inv_mul_cancel₀ h2
    rw [e, hl.2, hR, hR, hR, toE_zeroE, toE_oneE, toE_negE, toE_oneE]
    unfold tab2
    linear_combination (runSentN k (runW k w) (2 * gs.length + 1) +
      runSentN k (runW k w) (2 * gs.length + 1 + 1)) * hi

end

end ProofFile.Honest.K10.Wd

#print axioms ProofFile.Honest.K10.Wd.coeffs_lin
#print axioms ProofFile.Honest.K10.Wd.tablesAt
#print axioms ProofFile.Honest.K10.Wd.uRound
#print axioms ProofFile.Honest.K10.Wd.tRound
#print axioms ProofFile.Honest.K10.Wd.roundAt_split
#print axioms ProofFile.Honest.K10.Wd.hidePoly_cons
#print axioms ProofFile.Honest.K10.Wd.cube_succ
#print axioms ProofFile.Honest.K10.Wd.cube_prod
#print axioms ProofFile.Honest.K10.Wd.sigF
#print axioms ProofFile.Honest.K10.Wd.sigF_zero
#print axioms ProofFile.Honest.K10.Wd.sigF_succ
#print axioms ProofFile.Honest.K10.Wd.uRound_nil
#print axioms ProofFile.Honest.K10.Wd.uRound_cons
#print axioms ProofFile.Honest.K10.Wd.tlN
#print axioms ProofFile.Honest.K10.Wd.tlN_zero
#print axioms ProofFile.Honest.K10.Wd.tlN_tl
#print axioms ProofFile.Honest.K10.Wd.tl_tlN
#print axioms ProofFile.Honest.K10.Wd.uRound_form
#print axioms ProofFile.Honest.K10.Wd.runW
#print axioms ProofFile.Honest.K10.Wd.book_w
#print axioms ProofFile.Honest.K10.Wd.book_w0
#print axioms ProofFile.Honest.K10.Wd.sig_sumB
#print axioms ProofFile.Honest.K10.Wd.sigma_is
#print axioms ProofFile.Honest.K10.Wd.tab0
#print axioms ProofFile.Honest.K10.Wd.tab2
#print axioms ProofFile.Honest.K10.Wd.round_is
